import os.path

import pysmt.logics
from pysmt.typing import INT, REAL
from translator import reader, create_atoms, create_rules, writer, get_sccs
from tester import runner
import sys
import argparse
import time

starting_time, ending_time = None, None


def parse_value(number):
    if number == "real":
        return pysmt.logics.QF_RDL, REAL
    elif number == "int":
        return pysmt.logics.QF_IDL, INT


def main(args):
    if args.test:
        logic, number = parse_value(args.number)
        runner(number, args)
        return

    path = args.input
    assert os.path.isfile(path), "Input file is not existing"
    if args.scc:
        assert os.path.isfile(args.scc), "Setted sccs file is not existing"
    name_file = path.split("/")[-1]
    output_path, printer = args.output, args.output is not None
    logic, number = parse_value(args.number)

    print(f"Started translation of: {name_file}")
    if args.aspif:
        lines = reader(path, True)
        translations, facts = create_atoms(lines, number, True)
        if args.scc or args.optimization1 or args.optimization2:
            translations = get_sccs(args.scc, translations, True)
    else:
        lines = reader(path)
        translations = create_atoms(lines, number)
        if args.scc or args.optimization1 or args.optimization2:
            translations = get_sccs(args.scc, translations)
    print("Getting the translations")
    model = create_rules(translations, number, args.manual, args.optimization1, args.optimization2, args.scc)
    print("Created Models")
    writer(model, name_file, output_path, printer, args.manual, number)
    ending_time = time.time()
    print(f"Tempo totale richiesto: {ending_time - starting_time}s")


if __name__ == '__main__':
    starting_time = time.time()
    parser = argparse.ArgumentParser()
    parser.add_argument("-i", "--input", help="Path of the file to be translated", required=True)
    parser.add_argument("-m", "--manual", help="Activate if the translation should be done using the pysmt library"
                                               "or manually", action="store_true")
    parser.add_argument("-o", "--output", help="Decide if the obtained translation should be printed or not "
                                               "and specify the path")
    parser.add_argument("-opt1", "--optimization1", help="decide if the optimization for recursive rules should"
                                                         " be used or not",
                        action="store_true")
    parser.add_argument("-opt2", "--optimization2", help="Decide if the optimization for recursive rules should "
                                                         "be used or not", action="store_true")
    parser.add_argument("-n", "--number", help="Decide if the numbers should be integers or reals [int, real]",
                        choices=["int", "real"], default="int")
    parser.add_argument("-aspif", "--aspif", help="Define the input format of the model as aspif", action="store_true")
    parser.add_argument("-scc", "--scc", help="Path of the obtained reified file using --reify-sccs")
    parser.add_argument("-fp", "--fullpipe", help="Set if you want the tool to take care of the grounding and scc "
                                                  "founding. Require input and encoding")
    parser.add_argument("-e", "--encoding", help="Path of the file to be used as econding. Required for full-pipe.")
    parser.add_argument("-t", "--test", help="Decide if you want to test the translator with the input data", action="store_true")
    args = parser.parse_args()

    sys.exit(main(args))
