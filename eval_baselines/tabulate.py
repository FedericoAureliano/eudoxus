import json
import os
import sys

root_dir = sys.argv[1]

error_counts = {}

for subdir, dirs, files in os.walk(root_dir):
    error_count = 0
    parse_error = 0
    syntax_error = 0
    type_error = 0
    total_files = 0
    for file in files:
        if file.endswith(".txt"):
            file_path = os.path.join(subdir, file)

            with open(file_path, "r") as f:
                content = f.read()
                total_files += 1
                if "Parser error" in content:
                    error_count += 1
                    parse_error += 1
                elif "Syntax error" in content:
                    error_count += 1
                    syntax_error += 1
                elif "Type error" in content:
                    error_count += 1
                    type_error += 1
    if error_count > 0:
        error_counts[subdir] = {
            "total_errors": error_count,
            "parse_errors": parse_error,
            "syntax_errors": syntax_error,
            "type_errors": type_error,
            "total_files": total_files,
        }

json_data = json.dumps(error_counts, indent=4)

with open("error_counts.json", "w") as f:
    f.write(json_data)
