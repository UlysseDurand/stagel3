import json, os, glob
infoexists = os.path.isfile("infos.json")
data = {}
if infoexists:
    data = json.loads(open("infos.json").read())

def loadpackages():
    for e in glob.glob("./*.sty"):
        print("\\usepackage{"+e[2:-4]+"}")

if infoexists:
    for key,value in data.items():
        print("\\newcommand{\\le"+key+"}{"+value+"}")
else:
    print("\\newcommand{\\letitle}{}")
    print("\\newcommand{\\leauthor}{}")
