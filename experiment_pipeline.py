# this file will be responsible for running the experiments
import subprocess

"""
Run Eudoxus on the examples and then ask the LLM whether
it thinks the output model matches the original.

1. Run Eudoxus and get the file outputs
2. Take the file outputs and then wrap it in an LLM call
"""


import os
import time


def run():
    files = ["docs/data/BaierKatoen/bk-ex2_17-part2.txt"]
    # files = []

    for folder in [
        "docs/data/BaierKatoen",
        "docs/data/HuthRyan",
        "docs/data/LeeSeshia",
    ]:
        for file in [
            os.path.join(folder, f) for f in os.listdir(folder) if f.endswith(".txt")
        ]:
            if files:
                if file in files:
                    e = run_file(file)
            else:
                e = run_file(file)

            # if error first time, run again
            if e == "error":
                run_file(file)
    print("done running")


def run_file(file):
    date = time.strftime("%m-%d-%Y-%H-%M")
    print("starting file: ", file)
    filename = os.path.basename(file)
    output = os.path.join("results", date, filename + ".ucl")
    summary = os.path.join("results", date, filename)
    os.makedirs(os.path.dirname(output), exist_ok=True)
    VERF_FLAG = False
    INV_GEN_SET = ["no-involvement", "simple", "external-llm"]
    LLM_INV_GEN = "simple"
    SYNTAX_ITER = 5

    # gpt-3.5-turbo-0125
    # "gpt-4-turbo-2024-04-09"
    try:
        with open(summary, "wb") as f:
            command_list = [
                "eudoxus",
                "--iterations",
                str(SYNTAX_ITER),
                file,
                "--output",
                output,
                "--model",
                "gpt-3.5-turbo-0125",
            ]
            if VERF_FLAG:
                command_list.append("--verf-eng-feedback")
            if LLM_INV_GEN in INV_GEN_SET:
                command_list.append("--semantic-assistance")
                command_list.append(LLM_INV_GEN)
            else:
                print("got unsupported / invalid LLM_INV_GEN")
                return
            print("command list: ", " ".join(command_list))
            f.write(
                subprocess.run(
                    command_list,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                    check=True,
                ).stdout
            )
    except subprocess.CalledProcessError as e:
        print("Command failed with error:")
        print("stderr:", e.stderr)
        print("Return code:", e.returncode)
        try:
            print("stderr: ", subprocess.STDOUT)
        except Exception as e:
            print("e: ", e)
            print("could not print error message")
        return "error"
    except Exception as e:
        print("An unexpected error occurred.")
        print(str(e))
        return "error"


if __name__ == "__main__":
    run()
