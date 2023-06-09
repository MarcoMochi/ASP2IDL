import sys
import os
import re
import pandas as pd
from translator import reader


def analyze_yices(folder_name, name=""):
    list_stats = []
    files = os.listdir(folder_name)
    files.sort()

    for path in files:
        # check if current path is a file
        if os.path.isfile(os.path.join(folder_name, path)) and path.endswith('.asp'):
            stats = reader(folder_name + path)
            if stats[0] != "sat" and stats[0] != "unsat":
                list_stats.append({"Instance": str(path), "State": "Time-out"})
                continue
            if "(" not in stats:
                continue
            status = stats[0]
            stats = stats[stats.index("("):]
            temp_dict = {"Instance": str(path), "State": status}
            for elem in stats[1:-1]:
                try:
                    key, value = elem.split((" "))
                    key = key.replace(":", "")
                    temp_dict[key.capitalize()] = float(value)
                except:
                    pass
            list_stats.append(temp_dict)

    result = pd.DataFrame.from_dict(list_stats)
    result.to_excel(f"{folder_name}analisi_yices_{name}.xlsx", engine='xlsxwriter')


def analyze_yices_1(folder_name, name=""):
    list_stats = []
    files = os.listdir(folder_name)
    files.sort()

    for path in files:
        # check if current path is a file
        if os.path.isfile(os.path.join(folder_name, path)) and path.endswith('.asp'):
            stats = reader(folder_name + path)
            if stats[0] != "sat" and stats[0] != "unsat":
                list_stats.append({"Instance": str(path), "State": "Time-out"})
                continue
            status = stats[0]
            temp_dict = {"Instance": str(path), "State": status}
            for elem in stats[1:-1]:
                try:
                    key, value = elem.split((":"))
                    key = key.rstrip()
                    value = value.rstrip()
                    value = value.split("s")[0]
                    temp_dict[key.capitalize()] = float(value)
                except:
                    print(elem)
                    pass
            list_stats.append(temp_dict)

    result = pd.DataFrame.from_dict(list_stats)
    result.to_excel(f"{folder_name}analisi_yices_{name}.xlsx", engine='xlsxwriter')


def extract_answer_set(folder_name):
    files = os.listdir(folder_name)
    files.sort()
    aspif = True
    for path in files:
        if os.path.isfile(os.path.join(folder_name, path)) and path.endswith('.asp'):
            assignments = {}
            answer_set = []
            rules = reader(folder_name + path)
            if not rules:
                continue
            if rules[0] != "sat":
                continue
            try:
                rules = rules[:rules.index("(")]
            except:
                rules = rules

            for elem in rules[1:]:
                try:
                    if aspif:
                        if "W" not in elem:
                            atom,value = re.findall("\d+", elem)
                            if "-" in elem:
                                assignments[atom] = -int(value)
                            else:
                                assignments[atom] = int(value)
                    else:
                        atom = elem.split("|")[1]
                        if "-" in elem.split("|")[2]:
                            assignments[atom] = -int(re.search(r"\d+", elem.split("|")[2]).group(0))
                        else:
                            assignments[atom] = int(re.search(r"\d+", elem.split("|")[2]).group(0))
                except:
                    if " bot " in elem:
                        atom = "bot"
                        assignments[atom] = int(re.search(r"\d+", elem).group(0))
            limit = assignments["bot"]
            for key, value in assignments.items():
                if value < limit:
                    answer_set.append(key)

            new_path = folder_name.replace("Results", "Istanze_Originali")
            new_path = new_path.replace("+scc", "")
            atom_to_id = {}
            facts = []
            with open(new_path + path, "r") as r:
                    atoms = [x.strip() for x in r.readlines() if x.startswith("4")]
                    for atom in atoms:
                        values = atom.split(" ")
                        if int(values[-1]) == 0:
                            facts.append(values[-2])
                        else:
                            atom_to_id[values[-1]] = values[-3]
            with open(folder_name + "Answer_Set/" + path, "w") as w:
                for elem in answer_set:
                    try:
                        w.write(f"{atom_to_id[elem]}. ")
                    except:
                        pass
                for elem in facts:
                    w.write(f"{elem}. ")




    return answer_set


def analyze_clingo(folder_name):
    list_stats = []
    files = os.listdir(folder_name)
    files.sort()
    for path in files:
        # check if current path is a file
        if os.path.isfile(os.path.join(folder_name, path)) and path.endswith('.asp'):
            stats = reader(folder_name + path)

            if "Answer" not in stats[3] and stats[3] != "UNSATISFIABLE":
                list_stats.append({"Instance": str(path), "State": "Time-out"})
                continue
            if stats[3] == "UNSATISFIABLE":
                status = "unsat"
                index = 7
            else:
                status = "sat"
                index = 9
            stats = stats[index:]
            temp_dict = {"Instance": str(path), "State": status}
            for elem in stats:
                if elem == "":
                    continue
                elem = elem.split("(")[0]
                key, value = [x.strip() for x in elem.split((":"))]
                print(value)
                temp_dict[key] = value
            list_stats.append(temp_dict)

        result = pd.DataFrame.from_dict(list_stats)
        result.to_excel(folder_name + "analisi_clingo.xlsx", engine='xlsxwriter')


def main():
    folder_name = sys.argv[1]
    if len(sys.argv[1:]) == 1:
        print(extract_answer_set(folder_name))
    else:
        smt_solver = sys.argv[2]

        try:
            name = sys.argv[3]
            if smt_solver.lower() == "yices":
                analyze_yices(folder_name, name)
            elif smt_solver.lower() == "clingo":
                analyze_clingo(folder_name, name)
            elif smt_solver.lower() =="yices_old":
                analyze_yices_1(folder_name, name)
        except:
            if smt_solver.lower() == "yices":
                analyze_yices(folder_name)
            elif smt_solver.lower() == "clingo":
                analyze_clingo(folder_name)
            elif smt_solver.lower() =="yices_old":
                analyze_yices_1(folder_name)


if __name__ == '__main__':
    sys.exit(main())
