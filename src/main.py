import pysmt.logics
from pysmt.typing import INT, REAL
from translator import reader, create_atoms, create_rules, writer
import sys


def get_optimizations_params(opt1, opt2):
    temp_opt1, temp_opt2 = False, False
    if opt1 == "true":
        temp_opt1 = True
    if opt2 == "true":
        temp_opt2 = True

    return temp_opt1, temp_opt2


def parser(values):
    manual = values[0].lower()
    number = values[1].lower()
    printer = values[2].lower()
    opt1, opt2 = False, False
    try:
        opt1, opt2 = get_optimizations_params(values[3], values[4])
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

    if printer == "true":
        printer = True
    else:
        printer = False

    return manual, number, logic, printer, opt1, opt2


def main():
    lines = reader(sys.argv[1])
    name_file = sys.argv[1].split("/")[-1]
    output_path = sys.argv[2]

    manual, number, logic, printer, opt1, opt2 = parser(sys.argv[3:])

    print(f"Iniziata traduzione in SMT del file {name_file}")
    translations = create_atoms(lines, number)
    print("TROVATE TRANSAZIONI")
    model = create_rules(translations, number, manual, opt1, opt2)
    print("TROVATO MODELLO")

    writer(model, name_file, output_path, printer, manual, number)


if __name__ == '__main__':
    sys.exit(main())
