import pysmt.logics
import z3
from pysmt.shortcuts import is_sat, get_model, write_smtlib, simplify, to_smtlib, Solver
from pysmt.typing import INT, REAL
from pysmt.smtlib.parser import SmtLibParser
from z3 import Z3_benchmark_to_smtlib_string

from translator import reader, create_atoms, create_rules, call_solver, extractAnswerSet, writer
import sys


problem = "GraphColoringManuale/"


def get_optimizations_params(opt1, opt2):
    opt1, opt2 = False
    if opt1 == "true":
        opt1 = True
    if opt2 == "true":
        opt2 = True

    return opt1, opt2

def parser(values):
    manual = values[0].lower()
    number = values[1].lower()
    solve = values[2].lower()
    printer = values[3].lower()
    opt1, opt2 = False
    try:
        opt1, opt2 = get_optimizations_params(values[4], values[5])
    except:
        pass
    logic = None

    if manual == "true":
        manual = True
    else:
        manual = False

    if number == "real":
        logic = pysmt.logics.QF_RDL
        number = REAL
    elif number == "int":
        logic = pysmt.logics.QF_IDL
        number = INT

    if solve == "true":
        solve = True
    else:
        solve = False

    if printer == "true":
        printer = True
    else:
        printer = False

    return manual, number, logic, solve, printer

def main():

    lines = reader(sys.argv[1])
    name_file = sys.argv[1].split("/")[-1]
    output_path = sys.argv[2]
    if len(sys.argv[1:]) == 1:
        answer_set = extractAnswerSet(sys.argv[1])
        with open("../Answer_Set_Generati/" + problem + "/Competition/ASP/" + name_file, "w") as w:
            for elem in answer_set:
                w.write(f"{elem}.\n")

    else:
        manual, number, logic, solve, printer = parser(sys.argv[3:])

        print(f"Iniziata traduzione in SMT del file {name_file}")
        translations = create_atoms(lines, number)
        print("TROVATE TRANSAZIONI")
        model = create_rules(translations, number, manual, opt1, opt2)
        print("TROVATO MODELLO")


        writer(model, name_file, output_path, printer, manual, number)

        if solve and not manual:
            print(f"Iniziata fase solving del file {name_file} tradotto")
            answer_set = call_solver(model, number)
            if printer:
                with open("./" + name_file, "w") as r:
                    for elem in answer_set:
                        r.write(f"{elem[1:-1]}.\n")
            else:
                print(answer_set)

if __name__ == '__main__':
    sys.exit(main())
    #test_smt()