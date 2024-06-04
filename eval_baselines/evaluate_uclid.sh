#!/bin/bash

# Directory path
directory="/Users/wong.justin/Documents/eudoxus/final_result_baselines/gpt-3.5-turbo-post_processed_one_shot_COT_ucl_code"

# directory="/Users/wong.justin/Documents/eudoxus/final_result/gpt-4-turbo-post_processed_one_shot_COT_ucl_code"
# directory="/Users/wong.justin/Documents/eudoxus/final_result/ft-one_shot_COT_ucl_code"
directory="/Users/wong.justin/Documents/eudoxus/final_result_baselines/gpt-4-turbo-post_processed_one_shot_COT_ucl_code_pass@5"
# directory="/Users/wong.justin/Documents/eudoxus/final_result_baselines/ft-one_shot_COT_ucl_code"
# Loop through each file in the directory
directory="/Users/wong.justin/Documents/eudoxus/final_result_baselines/gpt-4-turbo-one_shot_no_COT_ucl_code_post_processed"
directory="/Users/wong.justin/Documents/eudoxus/final_result_baselines/gpt-3.5-turbo-0125-one_shot_no_COT_ucl_code_post_processed"
echo $directory
for file in "$directory"/*; do

  # Check if the file is a regular file
  if [[ -f "$file" ]]; then
    echo $file
    # Get the basename of the file without the extension
    filename=$(basename "$file" .ucl)
    # Run uclid with the file as input
    mkdir ${directory}/${filename}
    uclid $file 2>&1 > ${directory}/${filename}/${filename}.txt
  else
    # Check if the file name is 'cache', if so, skip it
    if [[ "$filename" == "cache" ]]; then
      continue
    fi
    # Loop through each file in the directory
    for f in $file/*; do
      # Check if the file is a regular file
      if [[ -f "$f" ]]; then
        echo $f
        # Get the basename of the file without the extension
        filename=$(basename "$f" .ucl)
        # Run uclid with the file as input
        uclid $f 2>&1 > $file/${filename}.txt
      fi
    done
  fi
done
