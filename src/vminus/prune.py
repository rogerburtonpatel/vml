import os 

with open('all.cm', "r") as all:
    allfiles = "".join(all.readlines()).split()
    for file in os.listdir():
        if file not in allfiles and 'sml' in file and file != 'main.sml' and file != 'impossible.sml':
            i = input(f"Remove {file}?\n")  
            if "y" in i or "Y" in i:
                os.remove(file)