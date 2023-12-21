import os
import random

# get all files in data directory that end in .ucl
files = [f for f in os.listdir("data") if f.endswith(".ucl")]

# do a test-train split on the files
# first, shuffle the files
files = random.sample(files, len(files))
train = files[: int(len(files) * 0.5)]
test = files[int(len(files) * 0.5) :]
# sort the files
train.sort()
test.sort()

# create a csv file with the train and test files
with open("data/train.csv", "w") as f:
    f.write("filename\n")
    f.write("\n".join(train))

with open("data/test.csv", "w") as f:
    f.write("filename\n")
    f.write("\n".join(test))
