import argparse
import sys
import os
import re
import pandas as pd
from translator import reader


def get_facts(path):
    facts = []
    atoms_to_id = {}
    with open(path, "r") as r:
        lines = r.readlines()
        atoms_lines =  [rule for rule in lines if rule[0] == "4"]
        for line in atoms_lines:
            values = line.rstrip().split(" ")
            atom = values[2]
            atom_id = values[-1]
            if atom_id == "0":
                facts.append(atom)
            else:
                atoms_to_id[atom_id] = atom
    return facts, atoms_to_id


def get_model(path, links):
    assignments = {}
    model = []
    with open(path, "r") as r:
        lines = [x.rstrip() for x in r.readlines()]
        if lines[0] != "sat":
            return []

        for line in lines[1:]:
            if not line.startswith("(="):
                continue
            if "W" not in line and "bot" not in line:
                atom, value = re.findall("\d+", line)
                if "-" in line:
                    assignments[atom] = -int(value)
                else:
                    assignments[atom] = int(value)
            elif "bot" in line:
                value = re.search("\d+", line).group(0)
                if "-" in line:
                    assignments["bot"] = -int(value)
                else:
                    assignments["bot"] = int(value)

        assert isinstance(assignments["bot"], int), "The value of the False atom was not assigned"
        limit = assignments["bot"]
        for key, value in assignments.items():
            if value < limit:
                try:
                    model.append(links[key])
                except:
                    pass
    return model


def write_model(facts, model, path):
    with open(path, "w") as w:
        w.write("% Original Facts\n")
        w.write("\n".join(facts))
        w.write("% Derived Atoms\n")
        w.write("\n".join(model))

def print_model(facts, model):
    print(f"Original Facts: {' '.join(facts)}")
    print(f"Derived atoms: {' '.join(model)}")

def main(args):
    original = args.aspif
    assert os.path.isfile(original), "Input file is not existing"
    result = args.result
    assert os.path.isfile(result), "Result file is not existing"

    facts, atoms_to_id = get_facts(original)
    model = get_model(result, atoms_to_id)

    if args.output:
        write_model(facts, model, args.output)
    else:
        print_model(facts, model)



if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("-a", "--aspif", help="Path of the original file", required=True)
    parser.add_argument("-r", "--result", help="Path of the result file in the Yices format", required=True)
    parser.add_argument("-o", "--output", help="Decide if the obtained model should be printed or not "
                                               "and specify the path")
    args = parser.parse_args()

    sys.exit(main(args))
