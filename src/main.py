import os.path

import pysmt.logics
from pysmt.typing import INT, REAL
from translator import reader, create_atoms, create_rules, writer, get_sccs
import sys
import argparse


def parse_value(number):
    if number == "real":
        return pysmt.logics.QF_RDL, REAL
    elif number == "int":
        return pysmt.logics.QF_IDL, INT


def main(args):

    path = args.file
    assert os.path.isfile(path), "Setted file is not existing"
    name_file = path.split("/")[-1]
    output_path, printer = args.printer, args.printer is not None
    logic, number = parse_value(args.number)

    print(f"Started translation of: {name_file}")
    if args.aspif:
        #sccs = get_sccs(path)
        lines = reader(path, True)
        translations, facts = create_atoms(lines, number, True)
    else:
        lines = reader(path)
        translations = create_atoms(lines, number)

    # TODO: Decide how to handle facts, now they are saved (taking the name from the aspif
    # output (format: 4 1 atom 0) but not used. An idea could be to add them to the model as < bot, Otherwise
    # could be added to the obtained model in a pipeline.
    print("TROVATE TRANSAZIONI")
    model = create_rules(translations, number, args.manual, args.optimization1, args.optimization2)
    print("TROVATO MODELLO")

    writer(model, name_file, output_path, printer, args.manual, number)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("-f", "--file", help="path of the file to be translated", required=True)
    parser.add_argument("-m", "--manual", help="activate if the translation should be done using the pysmt library"
                                               "or manually", action="store_true")
    parser.add_argument("-p", "--printer", help="decide if the obtained translation should be printed or not and specify the path")
    parser.add_argument("-o1", "--optimization1", help="decide if the optimization for recursive rules should be used or not",
                        action="store_true")
    parser.add_argument("-o2", "--optimization2", help="decide if the optimization for recursive rules should be used or not",
                        action="store_true")
    parser.add_argument("-n", "--number", help="decide if the numbers should be integers or reals [int, real]",
                        choices=["int", "real"], default="int")
    parser.add_argument("-aspif", "--aspif", help="define the input format of the model as aspif",  action="store_true")
    parser.add_argument("-sccs", "--sccs", help="path of the obtained reified file using --reify-sccs")
    args = parser.parse_args()

    sys.exit(main(args))
