import glob
import graphviz

dot = graphviz.Digraph()

for fname in glob.glob("Modformsported/**/*.lean", recursive=True):
    with open(fname, "r") as fin:
        lines = fin.read().strip().split("\n")
        path = fname.replace("/", ".").replace(".lean", "")
        path = path.replace("Modformsported.", "")
        for line in lines:
            if line.startswith("import Modform"):
                d = line.replace("import ", "").replace("Modformsported.", "")
                dot.node(d)
                dot.edge(d, path)

dot.format = "png"
dot.render("graph", format="png", cleanup=True)
