import os.path

from pysmt.typing import INT
from translator import reader, create_atoms, create_rules, writer, get_sccs
import sys
import argparse
import time


def main(args):
    path = args.input
    number = INT
    assert os.path.isfile(path), "Input file is not existing"
    if args.scc:
        assert os.path.isfile(args.scc), "Setted sccs file is not existing"
    name_file = path.split("/")[-1]
    output_path, printer = args.output, args.output is not None
    print(f"Started translation of: {name_file}")
    starting_time = time.time()
    if args.aspif:
        lines = reader(path, True)
        translations, facts = create_atoms(lines, number, True)
        if args.scc:
            translations = get_sccs(args.scc, translations, True)
    else:
        lines = reader(path)
        translations = create_atoms(lines, number)
        if args.scc:
            translations = get_sccs(args.scc, translations)
    print("Getting the translations")
    defs, model = create_rules(translations, number, args.scc)
    print("Created Models")
    writer(model, defs, name_file, output_path, printer, number)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("-i", "--input", help="Path of the file to be translated", required=True)
    parser.add_argument("-o", "--output", help="Decide if the obtained translation should be printed or not "
                                               "and specify the path")
    parser.add_argument("-aspif", "--aspif", help="Define the input format of the model as aspif", action="store_true")
    parser.add_argument("-scc", "--scc", help="Path of the obtained scc file using --reify-sccs")
    args = parser.parse_args()

    sys.exit(main(args))
