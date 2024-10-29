import subprocess
import re
import os
import sys

from openai import OpenAI


def extract_code(output) -> str:
    """Extracts the code from the LLM response."""
    output = output.rstrip()
    output = "```python\n" + output

    # replace any occurrences of "``````" with "```" (including optional spaces)
    output = re.sub(r"```\s*```", "```", output)

    end_index = output.rfind("```")
    if end_index <= len("```python\n"):
        end_index = len(output)
    before_start = output.rfind("```", 0, end_index)
    # find the newline after the index
    start_index = output.find("\n", before_start + 1)

    # extract the code
    code = output[start_index:end_index]
    # remove trailing new lines
    code = code.rstrip()

    return code


def chat(prompt, engine):
    if os.environ["OPENAI_API_KEY"]:
        client = OpenAI(api_key=os.environ["OPENAI_API_KEY"])
    else:
        raise ValueError("No OPENAI_API_KEY")
    response = client.chat.completions.create(
        model=engine, messages=[{"role": "user", "content": prompt}]
    )
    return response.choices[0].message.content.strip()


gpt4 = "gpt-4-turbo-2024-04-09"
gpt35 = "gpt-3.5-turbo-0125"


def call_uclid(output_str):
    # save the output string to a temporary file
    with open("tmp.ucl", 'w') as f:
        f.write(output_str)
    
    # call uclid on the temporary file and save the output and the return code
    result = subprocess.run(["uclid", "tmp.ucl", "-s", "z3 -in", "-g", "tmp"], capture_output=True)

    output = result.stdout.decode('utf-8')
    error = result.stderr.decode('utf-8')
    return_code = result.returncode

    if return_code != 0:
        raise Exception(output)
    
    assert len(error) == 0
    
    return output

def get_initial_prompt(task) -> str:
    if task.endswith("."):
        task = task[:-1]

    prompt = "Write UCLID5 code to complete the following task.\n\n"
    prompt += "> " + task.replace("\n", " ").replace("\r", " ").replace("  ", " ")
    prompt = prompt.rstrip()
    if prompt.endswith("."):
        prompt = prompt[:-1]
    prompt += ".\n\nReply with your UCLID5 code inside one unique code block.\n\n"
    prompt += "I can definitely do that! Here is the UCLID5 code:\n"
    prompt += "```\n"

    return prompt

def get_repair_prompt(buggy_code, compiler_feedback) -> str:
    prompt = ""

    prompt += "\nFix the following UCLID5 code using the compiler feedback provided below.\n"
    prompt += f"\n```\n{buggy_code}\n```\n"
    prompt += f"\nCompiler feedback:\n"
    prompt += f"\n```\n{compiler_feedback}\n```\n"
    prompt += "Reply with your UCLID5 code inside one unique code block.\n\n"
    prompt += "I can definitely do that! Here is the UCLID5 code:\n"
    prompt += "```\n"

    return prompt

def interact(task_file, count, prompt, model):
    # create a new file for this count iteration
    with open(f"{task_file}_{model}_prompt_{count}.md", 'w') as f:
        f.write(prompt)
    
    response = chat(prompt, model)
    # create a new file for this count iteration
    with open(f"{task_file}_{model}_response_{count}.md", 'w') as f:
        f.write(response)

    code = extract_code(response)
    with open(f"{task_file}_{model}_code_{count}.ucl", 'w') as f:
        f.write(code)
    
    return code

def self_repair(task_file, model, max_iterations=5):
    # read the task file into a string
    with open(task_file, 'r') as f:
        task = f.read()
    
    count = 1
    
    # ask the llm to solve the task
    prompt = get_initial_prompt(task)
    code = interact(task_file, count, prompt, model)

    while count < max_iterations:
        count += 1

        # call uclid on the code
        try:
            feedback = ""
            call_uclid(code)
        except Exception as e:
            feedback = str(e)

        if feedback == "":
            print(f"Passed {task_file} in {count} iterations using {model}.")
            return

        # ask the llm to repair the code
        prompt = get_repair_prompt(code, feedback)
        code = interact(task_file, count, prompt, model)


    print(f"Failed {task_file} after {max_iterations} iterations using {model}.")

# take the task file as command line argument
task_file = sys.argv[1]
self_repair(task_file, gpt35)
self_repair(task_file, gpt4)