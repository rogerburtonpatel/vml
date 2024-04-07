import os 

with open('all.cm', "r") as all:
    allfiles = "".join(all.readlines()).split()
    print(allfiles)
    for file in os.listdir():
        if file in allfiles and 'sml' in file and file != 'main.sml':
            src = f"../{file}"
            dst = f"{file}"
            print (f"linking {src} to {dst}")
            os.remove(file)
            os.symlink(src=src, dst=dst)