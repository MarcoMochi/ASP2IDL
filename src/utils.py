import os, glob
import sys

import pysmt.shortcuts


def get_size(path):
    with open(path, "r") as reader:
        lines = reader.readlines()
        var = [x for x in lines if x.startswith("(declare-fun")]
        n_rules = pysmt.shortcuts.read_smtlib(path)
        return len(var), len(n_rules._content.args)


def write_latex_size(result, name):
    name_inside = name.replace("_", "\_")
    with open(f"size_comparison_{name}.txt", "w") as w:
        w.write("\\begin{table}[h!]\\footnotesize\n")
        w.write(f"\\caption{{Number of variables and rules defined by using ASP2IDL with and without SCCs in the {name_inside} domain.}}\n")
        w.write(f"\\centering\label{{tab:size_{name} }}\n")
        w.write("\\begin{tabular}{ccccc}\n")
        w.write("\\hline\\hline\n")
        w.write("Instance & \\multicolumn{2}{c}{ASP2IDL} & \\multicolumn{2}{c}{ASP2IDL + SCCs} \\\\"
                        " & \\textsc{$\#$ of Var. in} & \\textsc{$\#$ of rules} & \\textsc{$\#$ of Var. in} & \\textsc{$\#$ of rules} \\\\ \n")
        w.write("\\cmidrule{1-1} \\cmidrule{2-2} \\cmidrule{3-3} \\cmidrule{4-4} \\cmidrule{5-5} \n")
        tot1 = tot2 = tot3 = tot4 = 0
        for key, values in result.items():
            tot1 += values[0]
            tot2 += values[1]
            tot3 += values[2]
            tot4 += values[3]
            w.write(f"{key} & {values[0]} & {values[1]} & {values[2]} & {values[3]} \\\\ \n")
        w.write("\\hline\n")
        n_values = len(result.keys())
        w.write(f"Mean values & {int(tot1/n_values)} & {int(tot2/n_values)} & {int(tot3/n_values)} & {int(tot4/n_values)} \\\\ \n")
        w.write("\\hline\\hline\n")
        w.write("\\end{tabular}\n")
        w.write("\\end{table}\n")


def get_model_size(domain):
    path = "../test"
    sub_dir = ["translation/solution_no_scc", "translation/solution_scc"]
    assert os.path.isdir(f"{path}/{domain}"), f"{path}/{domain} is not a valid path"

    result_dict = {}
    for dir in sub_dir:
        transleted_files = glob.glob(f"{path}/{domain}/{dir}/last/*.asp")
        for i, temp_file in enumerate(transleted_files):
            print(f"Facendo {i} di {len(transleted_files)}")
            name_file = temp_file.split('/')[-1].split('-')[0]
            val1, val2 = get_size(temp_file)
            try:
                result_dict[name_file].append(val1)
                result_dict[name_file].append(val2)
            except:
                result_dict[name_file] = [val1, val2]

    write_latex_size(result_dict, domain)


def write_latex_time(result, name):
    name_inside = name.replace("_", "\_")
    with open(f"time_comparison_{name}.txt", "w") as w:
        w.write("\\begin{table}[h!]\\footnotesize\n")
        w.write(
            f"\\caption{{Time (sec.) required to solve the translated solution in the {name_inside} domain."
            f" - means that the solver (yices) was not able to find a solution in 600 seconds.}}\n")
        w.write(f"\\centering\label{{tab:time_{name} }}\n")
        w.write("\\begin{tabular}{ccccc}\n")
        w.write("\\hline\\hline\n")
        w.write("Instance & LP2Diff & ASP2IDL & \\multicolumn{2}{c}{ASP2IDL + SCCs} \\\\"
                " &  & & \\textsc{yices} & \\textsc{z3} \\\\ \n")
        w.write("\\cmidrule{1-1} \\cmidrule{2-2} \\cmidrule{3-3} \\cmidrule{4-4} \\cmidrule{5-5} \n")
        yices = z3 = 0
        for key, values in sorted(result.items()):
            if values[0] < 600:
                if values[0] == 0:
                    values[0] = "$<$1"
                yices += 1
            else:
                values[0] = "-"
            if values[1] < 600:
                if values[1] == 0:
                    values[1] = "1"
                z3 += 1
            else:
                values[1] = "-"
            w.write(f"{key} &  &  & {values[0]} & {values[1]} \\\\ \n")
        w.write("\\hline\n")
        w.write(
            f"Solved Instances &  & & {yices} & {z3} \\\\ \n")
        w.write("\\hline\\hline\n")
        w.write("\\end{tabular}\n")
        w.write("\\end{table}\n")


def time_comparison(domain):
    path = "../test/"
    sub_dir = ["translation/solution_scc/last/yices", "translation/solution_scc/last/z3"]
    assert os.path.isdir(f"{path}/{domain}"), f"{path}/{domain} is not a valid path"

    result_dict = {}
    for dir in sub_dir:
        with open(f"{path}/{domain}/{dir}/stats.txt", "r") as r:
            lines = r.readlines()
            for line in lines:
                name = line.split("-")[0]
                solving_time = line.split(" ")[-1]
                try:
                    result_dict[name].append(int(solving_time))
                except:
                    result_dict[name] = [int(solving_time)]

    write_latex_time(result_dict, domain)


if __name__ == '__main__':
    if sys.argv[1] == "size":
        get_model_size(sys.argv[2])
    elif sys.argv[1] == "time":
        time_comparison(sys.argv[2])