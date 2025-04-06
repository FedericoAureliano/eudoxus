import os

from openai import BaseModel, OpenAI


def chat(prompt, engine):
    if os.environ["OPENAI_API_KEY"]:
        client = OpenAI(
            api_key="sk-proj-78kss8lazsT0ShhM49M75YwHSUR44wn9-8CX_5DcA0BQkc\
                rvdnEe2V0Q3S7nb6xACf1qy1gKcmT3BlbkFJmJmaHT7S_-KCGRz_sxNcahaz\
                    BtuJfvIqet-Fe-BytDyIzYiNNUNNRSg9wFvoI8SpNy1dqKd9YA"
        )
    else:
        raise ValueError("No OPENAI_API_KEY")
    response = client.chat.completions.create(
        model=engine, messages=[{"role": "user", "content": prompt}]
    )
    return response.choices[0].message.content.strip()


def chat_constrained(system_prompt, user_task, base_class):
    client = OpenAI(
        api_key="sk-proj-78kss8lazsT0ShhM49M75YwHSUR44wn9-8CX_5Dc\
            A0BQkcrvdnEe2V0Q3S7nb6xACf1qy1gKcmT3BlbkFJmJmaHT7S_-KCG\
                Rz_sxNcahazBtuJfvIqet-Fe-BytDyIzYiNNUNNRSg9wFvoI8SpNy1dqKd9YA"
    )
    completion = client.beta.chat.completions.parse(
        model="gpt-4o-2024-08-06",
        messages=[
            {"role": "system", "content": system_prompt},
            {"role": "user", "content": user_task},
        ],
        response_format=base_class,
    )

    suggestions_parsed = completion.choices[0].message.parsed
    # print("type parsed: ", type(suggestions_parsed))

    return suggestions_parsed


def rewrite_module_with_llm_bmc(task, module_as_py, ucl_module):
    # rewrites the bmc in the ucl_module based on llm
    class num_iter(BaseModel):
        iters: int

        class Config:
            extra = "forbid"  # Ensures no additional properties are returned

    sys_prompt = f"You are an expert model analyzer. I will provide \
        a python model meant to represent a specific task, and you have to \
            analyze all functions and the provided task. Specifically pay attention \
                to the `next` function.\n \
                Task: {task}\n \
                    Python Code: {module_as_py}"

    usr_prompt = " Using the code provided, just return the number of iterations \
        I should run the `next` function in this model to verify correctness."

    returned_iter_num = chat_constrained(sys_prompt, usr_prompt, num_iter)

    ucl_module = ucl_module.replace("bmc(3)", f"bmc({max(1, returned_iter_num.iters)})")
    return ucl_module
