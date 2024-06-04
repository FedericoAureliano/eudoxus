import os

ft = "ft:gpt-3.5-turbo-0125:justin-wong:direct-v3:9RToP45d:ckpt-step-284"
import json
import os
from pathlib import Path

from openai_framework.api_call import chat_completion, openai_init
from openai_framework.stub_registry import stub_registry
from openai_framework.utils import build_prompt
from openai_framework.visualize import pp_messages

openai_init(json.load(open("../open_ai_keys.json", "r")))

# Directory containing the ucl_files
docstrings = "../data/all_textbook_data"
output_dir = "./ft-one_shot_no_COT_ucl_code"

# Iterate over each file in the ucl_files directory
for filename in os.listdir(docstrings):
    if filename.endswith(".txt"):
        print(filename)
        if filename == "two-safety.txt":
            continue
        # Read the content of the uclid file
        with open(os.path.join(docstrings, filename), "r") as file:
            uclid_content = file.read()

        # Create the output .txt file
        output_filename = os.path.splitext(filename)[0] + ".ucl"
        output_path = os.path.join(output_dir, output_filename)

        (Path(output_dir) / "cache").mkdir(parents=True, exist_ok=True)

        # continue if the file exists already
        if os.path.exists(output_path):
            print(f"File {output_filename} already exists. Skipping...")
            continue

        # Print the content to the screen
        print(uclid_content)

        # Prompt the user to enter the content for the output file

        sys_msg = {
            "role": "system",
            "content": "You're an expert in writing uclid5 models."
            + "You will be given a docstring and asked to write a model. Remember uclid5 is a state machine language and has it's own specific syntax.",
        }
        example_user_msg = {
            "role": "user",
            "content": """Write a uclid5 model for the following description:

This UCLID5 model, inspired by Lee & Seshia's "Introduction to Embedded Systems," simulates interactions between processes to evaluate confidentiality through non-interference simulations. It features two modules, `process1` and `process2`, each handling inputs and outputs differently based on internal states and external inputs. `process1` uses a simple state and toggles its output based on the negation of a public input, while `process2` incorporates a more complex state transition system that toggles outputs based on both secret and public inputs. The main module orchestrates interactions between instances of these processes under controlled conditions, ensuring that the output remains consistent across different runs despite variations in secret inputs. This setup is used for bounded model checking to analyze potential security vulnerabilities or to demonstrate non-interference, with functionalities to unroll process behaviors up to five times and print counterexamples for detailed analysis.
""",
        }
        example_output_msg = {
            "role": "assistant",
            "content": """module process1
{
  type pc_t = enum { A };

  var pc : pc_t;
  input s : boolean; // secret input
  input x : boolean; // public input
  output z: boolean; // public output

  init {
    pc = A;
    z = false;
  }

  next {
    z' = !x;
  }

}

module process2
{
  type pc_t = enum { B, C };

  var pc : pc_t;
  input s : boolean; // secret input
  input x : boolean; // public input
  output z: boolean; // public output

  procedure next_state()
    modifies z;
    modifies pc;
  {
    case
      (pc == B) && s && !x : { pc = C; z = true; }
      (pc == C) && s && !x : { pc = B; z = false; }
    esac
  }

  init {
    pc = B;
    z = false;
  }

  next {
    call next_state();
  }
}


module main
{
  type t1pc_t = process1.pc_t;
  type t2pc_t = process2.pc_t;

  var x1,x2 : boolean;
  var s1,s2 : boolean;
  var z1,z2 : boolean;

/*
  instance p11 : process1(z: (z1), s : (s1), x : (x1));
  instance p12 : process1(z: (z2), s : (s2), x : (x2));
*/

/*
*/
  instance p21 : process2(z: (z1), s : (s1), x : (x1));
  instance p22 : process2(z: (z2), s : (s2), x : (x2));

  init {
    havoc x1; havoc x2;
    havoc s1; havoc s2;
    assume(x1 == x2);
  }

  next {
    havoc x1; havoc x2;
    havoc s1; havoc s2;
    assume(x1' == x2');
    // next(p11); next(p12);
    next(p21); next(p22);
  }

  invariant same_output_z : (z1 == z2);


  control {
    // *** BASIC ASSERTIONS/INVARIANT
/*
*/
    v = unroll(5);
    check;
    print_results;
    //v.print_cex(x1,x2,s1,s2,z1,z2,p11.pc,p12.pc);
    v.print_cex(x1,x2,s1,s2,z1,z2,p21.pc,p22.pc);

/*
    // *** INDUCTION
    v = induction(1);
    check;
    print_results;
    v.print_cex(x1,x2,s1,s2,z1,z2,p11.pc,p12.pc);
*/
  }
}""",
        }
        request_msg = {
            "role": "user",
            "content": "Write a uclid5 model for the following description: \n"
            + uclid_content,
        }
        prompt = [sys_msg, example_user_msg, example_output_msg, request_msg]

        # Call the chat_completion function to get the output content
        _, output_content = chat_completion(
            prompt,
            model=ft,
            log_file=Path(output_dir) / "cache" / f"{output_filename}.log",
            temperature=0.5,
        )
        complete_prompt = prompt + [{"role": "assistant", "content": output_content}]
        complete_trace_json = Path(output_dir) / "cache" / f"{output_filename}.json"
        json.dump(complete_prompt, open(complete_trace_json, "w"))
        baseline_pp_file = Path(output_dir) / "cache" / f"{output_filename}.txt"
        pp_messages(complete_prompt, file=open(baseline_pp_file, "w"))

        def parse(result, language="dafny"):
            result = "".join(result.split(f"```{language}")[1:])
            result = result.split("```")[0]
            return result

        # result = parse(output_content, language = "").replace("/*", "").replace("*/", "")
        result = output_content
        if result != "":
            # Write the content to the output .txt file
            with open(output_path, "w") as file:
                file.write(result)
            print("=" * 10)
            print(result)
