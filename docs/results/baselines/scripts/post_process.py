dir = "/Users/wong.justin/Documents/eudoxus/results/gpt-3.5-turbo-0125-one_shot_no_COT_ucl_code"
output = "/Users/wong.justin/Documents/eudoxus/results/gpt-3.5-turbo-0125-one_shot_no_COT_ucl_code_post_processed"
from pathlib import Path

# Read the file

# Create the output directory if it doesn't exist
Path(output).mkdir(exist_ok=True)
for filename in Path(dir).rglob("**/*.ucl"):
    print(filename)

    with open(filename, "r") as file:
        lines = file.readlines()

    if (Path(output) / filename.name).exists():
        continue

    # Find the index of the first line containing "uclid"
    first_line_index = next(
        (
            i
            for i, line in enumerate(lines)
            if "uclid" in line or "UCLID" in line or "UC5" in line
        ),
        None,
    )

    # Find the index of the last line containing "}"
    last_line_index = next(
        (i for i, line in reversed(list(enumerate(lines))) if "}" in line), None
    )

    # Search for lines starting with "module <name>"
    module_lines = [line for line in lines if line.strip().startswith("module")]

    # Extract the module names
    module_names = [line.split()[1] for line in module_lines]

    # Print the list of module names
    if "main" not in module_names and len(module_names) != 0:
        lines = [l.replace(module_names[-1], "main") for l in lines]

    # Delete the first line if "uclid" is found
    if first_line_index is not None:
        del lines[first_line_index]

    # Delete the lines after the last "}"
    if last_line_index is not None:
        del lines[last_line_index + 1 :]

    if filename.parent.name in filename.name:
        (Path(output) / filename.parent.name).mkdir(exist_ok=True)
        with open(Path(output) / filename.parent.name / filename.name, "w") as file:
            file.writelines(lines)
    else:
        # Write the modified lines back to the file
        with open(Path(output) / filename.name, "w") as file:
            file.writelines(lines)
