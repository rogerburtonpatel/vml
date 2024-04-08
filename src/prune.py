import os 

with open('all.cm', "r") as all:
    allfiles = "".join(all.readlines()).split()
    for file in os.listdir():
        if file not in allfiles and 'sml' in file:
            print(file)