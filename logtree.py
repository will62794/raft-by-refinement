import json
import graphviz
import os

# Generate trace with TLC.
# os.system("java -cp lib/tla2tools-v1.8.jar tlc2.TLC -noGenerateSpecTE -dumpTrace json trace.json MCRaftLogTree")

# Parse JSON trace.
f = open("trace.json")
trace_json_str = "{ \"trace\":  " + f.read() + "}"
f.close()
trace = json.loads(trace_json_str)
# print(trace)
last_state = trace["trace"][-1]
# print(last_state)
# print(last_state["logTree"])
# print(last_state["treeEdges"])

G = graphviz.Digraph()

nodes = set()
for edge in last_state["logTree"]:
    src = edge["entry"]
    children = edge["children"]
    for to in children:

        print(src, to)
        sn = tuple(src)[:2]
        tn = tuple(to)[:2]
        # if edge["child"] == "None":
            # tn = "None"
        print(sn)
        print(tn)
        if sn not in nodes:
            G.node(str(sn))
            nodes.add(sn)
        if tn not in nodes:
            G.node(str(tn))
            nodes.add(tn)
        G.edge(str(sn),str(tn))

    # Intra log edges.
    # for ind,entry in enumerate(b["log"][:-1]):
    #     src = tuple(entry[:2])
    #     dest = tuple(b["log"][ind+1][:2])
    #     G.edge(str(src), str(dest))

    # Log to children edges.
    # for c in b["children"]:
    #     # last entry in this log.
    #     src = tuple(b["log"][-1][:2])
    #     dest = tuple(c)
    #     G.edge(str(src), str(dest))

G.render("log_tree")
