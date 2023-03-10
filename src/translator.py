from formula import Rule
import re
import fileinput
from pysmt.shortcuts import Symbol, Solver, And, Equals, Int, Real, get_env, is_sat, get_model, GE, write_smtlib, simplify
from pysmt.typing import INT, REAL
from pysmt.logics import QF_IDL, QF_RDL, QF_UFIDL
import sys, errno
import z3

def reader(file):
    lines = []
    with open(file, "r") as r:
        lines = [line.strip() for line in r.readlines()]

    return rewrite_disj(lines)


def rewrite_disj(lines):
    new_lines = []
    for line in lines:
        if ";" in line:
            left, right = line[:-1].split(";")
            new_lines.append(f"{left}:-not {right}.")
            new_lines.append(f"{right}:-not {left}.")

        else:
            new_lines.append(line)

    return new_lines

def create_atoms(rules, number):
    head_to_bodies = {}
    atom_without_support = {}
    for i, rule in enumerate(rules):
        try:
            if rule.startswith(":-"):
                head, body = "bot", [part.strip() for part in rule.split(":-")][1]
            else:
                head, body = [part.strip() for part in rule.split(":-")]

        except ValueError as e:
            head, body = rule[:-1].strip(), None

        if (expressions := head_to_bodies.get(head)) is None:
            head_to_bodies[head] = expressions = Rule(head, number)

        expressions.add_associated_variable(i+1)

        if body != None:
            positive_atoms = [atom for atom in re.split(r',\s*(?![^()]*\))', body[:-1]) if "not " not in atom]
            negative_atoms = [atom.replace("not ", "") for atom in re.split(r',\s*(?![^()]*\))', body[:-1]) if "not " in atom]
            expressions.populate_positive(positive_atoms)
            expressions.populate_negative(negative_atoms)

            for atom in positive_atoms:
                if atom not in head_to_bodies.keys():
                    atom_without_support[atom] = Rule(atom, number)
            for atom in negative_atoms:
                if atom not in head_to_bodies.keys():
                    atom_without_support[atom] = Rule(atom, number)
        else:
            expressions.populate_positive([])
            expressions.populate_negative([])

        if head in atom_without_support.keys():
            del atom_without_support[head]

    if "bot" in atom_without_support.keys():
        del atom_without_support["bot"]

    for key, rule in atom_without_support.items():
        head_to_bodies[key] = rule

    return head_to_bodies

def create_rules(head_to_bodies, number, manual):
    rules = []
    definitions = []
    atoms = set()
    variable = set()

    i = 0
    for key, elem in head_to_bodies.items():

        if manual:
            atoms.add(key)
            variable.update(elem.get_rules_id())
            rules.append(elem.create_association_manual(i))
            rules.append(elem.create_difference_manual(i))
            rules.append(elem.create_completion_manual(i))
        else:
            rules.append(elem.create_association())
            rules.append(elem.create_difference())
            rules.append(elem.create_completion())
        i += 1

    if manual:
        if "bot" not in atoms:
            atoms.add("bot")

        if number == REAL:
            for atom in atoms:
                definitions.append(f"(declare-fun |{atom}| () Real)")
        else:
            for atom in atoms:
                definitions.append(f"(declare-fun |{atom}| () Int)")
        for atom in variable:
            definitions.append(f"(declare-fun {atom} () Bool)")

        return definitions + rules

    return And(rules)

def extract_atoms(model, number):
    answer_set = []

    if number == REAL:
        limit = float(model[Symbol("F", REAL)].constant_value())
    elif number == INT:
        limit = int(model[Symbol("F", INT)].constant_value())
    for k in model:
        if k[1].constant_value() < limit and k[1].constant_value() > 0:
            answer_set.append(str(k[0]))
    return answer_set

def extractAnswerSet(name_file):
    answer_set = []
    rules = reader(name_file)
    if rules[0] != "sat":
        return print("Unsat problem")
    try:
        rules = rules[:rules.index("(")]
    except:
        rules = rules

    if "F" in rules[1]:
        limit = int(re.search(r"\d+", rules[1]).group(0))
        print(limit)
    for elem in rules[3:]:
        if int(re.search(r"\d+", elem.split("|")[2]).group(0)) < limit:
            atom = elem.split("|")[1]
            answer_set.append(atom)

    return answer_set


def call_solver_selected(model, number):
    name = "mathsat"  # Note: The API version is called 'msat'
    path = ["/Users/marco/Desktop/mathsat-5.6.9-osx/bin/mathsat"]  # Path to the solver
    logics = [QF_UFIDL]  # Some of the supported logics  # Some of the supported logics

    env = get_env()
    env.factory.add_generic_solver(name, path, logics)

    with Solver(name=name, logic=QF_IDL) as s:
        print(s.is_sat(model))
        return extract_atoms(s.get_model(), number)

def call_solver(model, number):
    if is_sat(model, logic=QF_IDL):
        return extract_atoms(get_model(model,logic=QF_IDL), number)

def writer(model, name_file, output_path, printer, manual, number):
    if printer and not manual:
        if number == REAL:
            write_smtlib(model, output_path + name_file, QF_RDL)
        else:
            write_smtlib(model, output_path + name_file, QF_IDL)
        with open(output_path + name_file, "r") as r:
            text = r.read()
        #text = text.replace("set-logic QF_LIA", "set-logic QF_IDL")
        #text = text.replace("declare-fun", "declare-const")
        #text = text.replace("() Int", "Int")
        text += "(get-model)"
        with open(output_path + name_file, "w") as w:
            w.write(text)

    elif printer:
        with open(output_path + name_file, "w") as w:
            if number == REAL:
                w.write(f"(set-logic QF_RDL)\n")
            else:
                w.write(f"(set-logic QF_IDL)\n")
            for rule in model:
                if rule != "":
                    w.write(f"{rule}\n")
            w.write(f"(check-sat)\n")
            w.write(f"(get-model)\n")

def simplify_smt2_file(file_path):
    tactics = ("simplify", "solve-eqs", "propagate-values", "simplify")
    query = z3.parse_smt2_file(file_path)
    goal = z3.Goal()
    goal.add(query)
    simplified = z3.Then(*tactics)(goal).as_expr()
    solver = z3.SolverFor("QF_IDL")
    solver.add(simplified)
    with open("prova_simpl.asp", "w") as writer:
        writer.write(solver.sexpr())