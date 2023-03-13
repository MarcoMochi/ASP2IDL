import sys
import os
import re
import pandas as pd
from translator import reader

def analyze_yices(folder_name, name=""):
    list_stats = []
    timeout_problems = []
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

def extractAnswerSet(folder_name):
    files = os.listdir(folder_name)
    files.sort()
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

            with open(folder_name + "Answer_Set/" + path, "w") as w:
                for elem in answer_set:
                    w.write(f"{elem}. ")

    return answer_set

def analyze_clingo(folder_name):
    list_stats = []
    timeout_problems = []

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
        print(list_stats)
        result.to_excel(folder_name + "analisi_clingo.xlsx", engine='xlsxwriter')


def main():
    folder_name = sys.argv[1]
    if len(sys.argv[1:]) == 1:
        print(extractAnswerSet(folder_name))
    else:
        smt_solver = sys.argv[2]

        try:
            name = sys.argv[3]
            if smt_solver.lower() == "yices":
                analyze_yices(folder_name, name)
            elif smt_solver.lower() == "clingo":
                analyze_clingo(folder_name, name)
        except:
            if smt_solver.lower() == "yices":
                analyze_yices(folder_name)
            elif smt_solver.lower() == "clingo":
                analyze_clingo(folder_name)



if __name__ == '__main__':
    sys.exit(main())
    #test_smt()