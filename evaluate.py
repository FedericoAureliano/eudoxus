import os
import subprocess

# if the results directory doesn't exist, create it
if not os.path.exists("results"):
    os.makedirs("results")

# get all the files in data/supported that end in ucl
supported = [f[:-4] for f in os.listdir("data/supported") if f.endswith(".ucl")]

for query in supported:
    # open the file and find // Description:
    with open(f"data/supported/{query}.ucl", "r") as f:
        description = f.read().splitlines()[1][len("// Description: ") :]

    # run eudoxus command line tool
    result = subprocess.run(
        [
            "pyenv",
            "exec",
            "eudoxus",
            "synthesize",
            "--examples",
            "data/not_supported",
            "--neighbours",
            "2",
            "--save-ir",
            f"results/{query}.py",
            "--output",
            f"results/{query}.ucl",
            f'"{description}"',
        ],
        capture_output=True,
        text=True,
    )

    # write the result to a file
    with open(f"results/{query}.trace", "w") as f:
        f.write(result.stderr)
        f.write(result.stdout)
