import os

for folder in ["final_results/run-1", "final_results/run-2"]:
    run_results = {}
    for f in os.listdir(folder):
        example_folder_path = os.path.join(folder, f)
        for version in os.listdir(example_folder_path):
            folder_version_path = os.path.join(example_folder_path, version)
            for output_file in os.listdir(folder_version_path):
                if ".ucl" in output_file:
                    run_results[output_file] = (version, f)

    for i in range(1, 166):
        output_name = f"{i}.ucl"
        print(
            f"{output_name} , \
                {run_results[output_name][0]} ,\
                      {run_results[output_name][1]}"
        )
