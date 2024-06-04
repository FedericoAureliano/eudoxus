import os

ft = "ft:gpt-3.5-turbo-0125:justin-wong:ucl-v3:9Qh16cXe"
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
output_dir = "./gpt-4-turbo-one_shot_COT_ucl_code"
# Iterate over each file in the ucl_files directory
for filename in os.listdir(docstrings):
    for attempt in range(5):
        if filename.endswith(".txt"):
            print(filename)
            if filename == "two-safety.txt":
                continue
            # Read the content of the uclid file
            with open(os.path.join(docstrings, filename), "r") as file:
                uclid_content = file.read()

            # Create the output .txt file
            output_filename = os.path.splitext(filename)[0] + f"_{attempt}.ucl"
            output_path = os.path.join(
                output_dir, os.path.splitext(filename)[0], output_filename
            )
            # Create the output directory if it doesn't exist
            os.makedirs(
                os.path.join(output_dir, os.path.splitext(filename)[0]), exist_ok=True
            )

            # continue if the file exists already
            if os.path.exists(output_path):
                print(f"File {output_filename} already exists. Skipping...")
                continue

            # Print the content to the screen
            print(uclid_content)

            # Prompt the user to enter the content for the output file
            prompt = [
                {
                    "role": "system",
                    "content": """You are an expert in program verification (hoare logic style). You are an expert user of UCLID5 which is a state transition modeling language. You will be given a description of a task and asked to write code. Before you start to write the module, first write an outline describing the key pieces.""",
                },
                {
                    "role": "user",
                    "content": """Please write code in Uclid5 to model the following description:

  This UCLID5 model, inspired by Lee & Seshia's "Introduction to Embedded Systems," simulates interactions between processes to evaluate confidentiality through non-interference simulations. It features two modules, `process1` and `process2`, each handling inputs and outputs differently based on internal states and external inputs. `process1` uses a simple state and toggles its output based on the negation of a public input, while `process2` incorporates a more complex state transition system that toggles outputs based on both secret and public inputs. The main module orchestrates interactions between instances of these processes under controlled conditions, ensuring that the output remains consistent across different runs despite variations in secret inputs. This setup is used for bounded model checking to analyze potential security vulnerabilities or to demonstrate non-interference, with functionalities to unroll process behaviors up to five times and print counterexamples for detailed analysis.

  Remember to start with an outline of the relevant parts of the Uclid5 model.""",
                },
                {
                    "role": "assistant",
                    "content": """Certainly! First let's make an outline:

  --OUTLINE--

  This UCLID5 model simulates a process interaction environment to evaluate confidentiality properties through non-interference simulations, inspired by an example in Chapter 17 on Security from "Introduction to Embedded Systems" by Lee & Seshia. The model consists of two types of process modules (`process1` and `process2`) and a main module that orchestrates the interaction between instances of these processes.

  Process Modules:
  1. `process1`: This module captures a simplified process that reflects non-deterministic behavior based on public input. It uses an enumerated type `pc_t` with a single state `A`. It has:
      - Inputs:
        * `s`: A boolean representing a secret input.
        * `x`: A boolean representing a public input.
      - Output:
        * `z`: A boolean public output that toggles based on the inverse of input `x`.
      - Behavior:
        * The process starts in state `A` and outputs `z` as `false` initially.
        * In subsequent cycles, the output `z` becomes the negation of `x`.

  2. `process2`: This module is a more complex process with an internal state machine described using state enum `pc_t` with states `B` and `C`. It demonstrates state-dependent output behavior.
      - Inputs are the same as in `process1`.
      - Output and state transitions:
        * The process starts in state `B` with the output `z` as `false`.
        * Based on the input combination (state, `s`, and `x`), the process transitions between states `B` and `C`, toggling the output `z`.
        * The transitions are specifically:
          - From `B` to `C` (output `z` is set to `true`) when `s` is true and `x` is false.
          - From `C` back to `B` (output `z` is reset to `false`) under the same input conditions.

  Main Module:
  - Sets up instances of `process2` (`p21` and `p22`) to interact under controlled input conditions.
  - Inputs `x1`, `x2` (public), and `s1`, `s2` (secret) are used for driving the process instances.
  - Controls non-determinism by initially assuming both `x1` and `x2` are equal, and it maintains this assumption in all subsequent states.
  - Evaluates confidentiality by asserting the invariant `same_output_z`, ensuring that outputs `z1` and `z2` of both process instances are always equal, thereby checking for consistent behavior across different runs with potentially varying secret inputs.

  Control:
  - The control block is used to perform bounded model checking and to produce counterexamples. It specifies that up to 5 unrolling should be checked.
  - The `print_cex` function is used for displaying counterexamples for the states of inputs and outputs along with the internal state of `process2` instances (`p21` and `p22`).

  This model is particularly useful for demonstrating the effects of secret data manipulations on the outputs, which can be analyzed to study security vulnerability or proof of non-interference in systems.

  Now here is the Uclid5 code for the model:

  --- CODE ---

  ```

  /*
  * Based on an example from Lee & Seshia, "Introduction to Embedded Systems", Chapter 17 on Security
  */
  module process1
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
  }

  ```
  """,
                },
                {
                    "role": "user",
                    "content": """Please write code in Uclid5 to model the following description:
  """
                    + uclid_content
                    + """Remember to start with an outline of the relevant parts of the Uclid5 model.""",
                },
            ]

            # Call the chat_completion function to get the output content
            _, output_content = chat_completion(
                prompt,
                model="gpt-4-turbo",
                log_file=Path("./cache") / f"{output_filename}.log",
                temperature=0.5,
            )
            complete_prompt = prompt + [
                {"role": "assistant", "content": output_content}
            ]
            complete_trace_json = os.path.join("./cache", f"{output_filename}.json")
            json.dump(complete_prompt, open(complete_trace_json, "w"))
            baseline_pp_file = (
                Path("./gpt-4-turbo-one_shot_COT_ucl_code")
                / "cache"
                / f"{output_filename}_attempt_{attempt}.txt"
            )
            pp_messages(complete_prompt, file=open(baseline_pp_file, "w"))

            def parse(result, language="dafny"):
                result = "".join(result.split(f"```{language}")[1:])
                result = result.split("```")[0]
                return result

            result = (
                parse(output_content, language="").replace("/*", "").replace("*/", "")
            )
            # result = output_content
            if result != "":
                # Write the content to the output .txt file
                with open(output_path, "w") as file:
                    file.write(result)
                print("=" * 10)
                print(result)
