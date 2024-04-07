import os 

with open('pplus.cm', "r") as all:
    allfiles = "".join(all.readlines()).split()
    for file in os.listdir():
        if file in allfiles and 'sml' in file:
            print(file)