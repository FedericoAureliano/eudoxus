import os
import random

# import subprocess
# import time


def run():
    # files = ["data/BaierKatoen/bk-ex2_17-part2.txt"]
    files = []
    # total_runs = 2
    uuid = 1
    version_dict = {
        "plain": (),
        "just_force_spec": ("semantic_assistance"),
        "smoke": ("smoke_testing"),
        "bmc_plus_spec": ("bmc", "semantic_assistance"),
        "all": ("bmc", "smoke_testing", "semantic_assistance"),
    }
    versions = list(version_dict.keys())
    print("all original versions: ", versions)
    run_num = 2
    # TODO : IMPORT TQDM
    for folder in [
        "docs/data/BaierKatoen",
        "docs/data/HuthRyan",
        "docs/data/LeeSeshia",
    ]:
        for file in [
            os.path.join(folder, f) for f in os.listdir(folder) if f.endswith(".txt")
        ]:
            random.shuffle(versions)
            for version in versions:
                version_name = version
                version = version_dict[version]
                print(
                    f"\nRun: {run_num} | File: {file} \
                        | Version Name: {version_name} |\
                              Version: {version}"
                )
                if files:
                    if file in files:
                        e = run_file(file, run_num, uuid, version_name, version)
                else:
                    e = run_file(file, run_num, uuid, version_name, version)

                # if error first time, run again
                if e == "error":
                    run_file(file, run_num, uuid, version_name, version)
                uuid += 1
            print("\n")
    print("done running")


def run_file(file, run_num, uuid, version_name, version):
    filename = os.path.basename(file)
    base_file_name = filename.replace(".txt", "")
    ucl_output = os.path.join(
        "final_results",
        f"run-{run_num}",
        base_file_name,
        version_name,
        str(uuid) + ".ucl",
    )
    trace_location = os.path.join(
        "final_results", f"run-{run_num}", base_file_name, version_name, filename
    )
    csv_location = os.path.join(
        "final_results",
        f"run-{run_num}",
        base_file_name,
        version_name,
        base_file_name + ".csv",
    )
    os.makedirs(os.path.dirname(ucl_output), exist_ok=True)
    command_list = [
        "eudoxus",
        "--iterations",
        "5",
        "--sem-iters",
        "5",
        file,
        "--output",
        ucl_output,
        "--csv-loc",
        csv_location,
    ]
    if "semantic_assistance" in version:
        command_list.append("--semantic-assistance")
    if "smoke_testing" in version:
        command_list.append("--use-smoke")
    if "bmc" in version:
        command_list.append("--use-bmc")
    entire_command = " ".join(command_list)
    entire_command = entire_command + f" > {trace_location}"
    print(entire_command)
    # try:
    #     with open(trace_location, "wb") as f:
    #         f.write(subprocess.run(command_list,
    # stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True).stdout)
    # except subprocess.CalledProcessError as e:
    #     print("Command failed with error:")
    #     print("stderr:", e.stderr)
    #     print("Return code:", e.returncode)
    #     try:
    #         print("stderr: ", subprocess.STDOUT)
    #     except:
    #         print("could not print error message")
    #     return "error"
    # except Exception as e:
    #     print("An unexpected error occurred.")
    #     print(str(e))
    #     return "error"


if __name__ == "__main__":
    run()
