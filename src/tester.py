from translator import reader, create_atoms, create_rules, writer, get_sccs
import glob, os
import time

from pysmt.logics import QF_IDL
from pysmt.shortcuts import get_env, Solver, get_model, EqualsOrIff

domains = ["GraphColouring","HanoiTower","Labyrinth_pre"]


def create_solver():
    name = "yices_new"  # Note: The API version is called 'msat'
    path = ["/opt/homebrew/bin/yices-smt2"]
    logics = [QF_IDL]  # Some of the supported logics
    env = get_env()
    env.factory.add_generic_solver(name, path, logics)


def runner(number, args):
    #create_solver()
    for domain in domains:
        translation_time = []
        solving_time = []
        solving_status = []
        print(f"Starting Domain: {domain}")
        out_path = ""
        if not os.path.isdir(f"../test/{domain}/translation"):
            os.mkdir(f"../test/{domain}/translation")
        if args.scc:
            out_path = f"../test/{domain}/translation/solution_scc/{time.strftime('%d %b %Y')}"
            try:
                if not os.path.isdir(out_path):
                    os.mkdir(out_path)
                os.mkdir(f"{out_path}/yices")
            except:
                os.mkdir(f"../test/{domain}/translation/solution_scc")
                out_path =f"../test/{domain}/translation/solution_scc/{time.strftime('%d %b %Y')}"
                os.mkdir(out_path)
                os.mkdir(f"{out_path}/yices")
        else:
            out_path = f"../test/{domain}/translation/solution_no_scc/{time.strftime('%d %b %Y')}"
            try:
                if not os.path.isdir(out_path):
                    os.mkdir(out_path)
                os.mkdir(f"{out_path}/yices")
            except:
                os.mkdir(f"../test/{domain}/translation/solution_no_scc")
                out_path =f"../test/{domain}/translation/solution_no_scc/{time.strftime('%d %b %Y')}"
                os.mkdir(out_path)
                os.mkdir(f"{out_path}/yices")

        problem_files = glob.glob(f"../test/{domain}/Aspif/*.asp")
        try:
            problem_files.remove("scc.asp")
        except:
            pass
        already_translated = glob.glob(f"{out_path}/*.asp")
        for file in problem_files:
            name_file = file.split("/")[-1]
            if out_path+"/"+name_file not in already_translated:
                print(f"Starting {name_file}")
                starting_time = time.time()
                lines = reader(file, True)
                translations, facts = create_atoms(lines, number, True)
                if args.scc:
                    if os.path.isdir(f"../test/{domain}/scc/"):
                        temp_path = f"../test/{domain}/scc/{name_file}"
                        translations = get_sccs(temp_path, translations, True)
                    else:
                        temp_path = f"../test/{domain}/Aspif/scc.asp"
                        translations = get_sccs(temp_path, translations, True)
                defs, model = create_rules(translations, number, args.manual, args.optimization1, args.optimization2, args.scc)
                writer(model, defs, name_file, out_path + "/", True, args.manual, number)
                ending_time = time.time()
                translation_time.append(ending_time-starting_time)

            else:
                translation_time.append("Not Applicable")
            print(f"Start Solving {name_file}")
            starting_time = time.time()
            os.system(f"yices-smt2 '{out_path}/{name_file}' --stats -t 600 > '{out_path}/yices/{name_file}'")
            ending_time = time.time()
            print(f"Tempo di Solving: {ending_time-starting_time}")
            solving_time.append(ending_time-starting_time)
        with open(f"{out_path}/yices/stats.txt", "w") as w:
            for i, name in enumerate(problem_files):
                w.write(f"{name.split('/')[-1]}: Translation time: {str(translation_time[i]).split('.')[0]} Solving time: {str(solving_time[i]).split('.')[0]}\n")


