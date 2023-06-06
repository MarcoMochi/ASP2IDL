from formula import Rule
import re
from pysmt.shortcuts import And, write_smtlib, to_smtlib
from pysmt.typing import REAL
from pysmt.logics import QF_IDL, QF_RDL
from clingo import Application, clingo_main, Control

def get_sccs(file):
    pass


def reader(file, aspif=False):
    lines = []
    with open(file, "r") as r:
        lines = [line.strip() for line in r.readlines()]

    if aspif:
        return lines
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


def check_recursive(rule_from_body, new_rule):
    temp_atoms = []
    for positives in rule_from_body.get_positives():
        for atom in positives:
            if atom == new_rule.get_head():
                rule_from_body.add_recursive(new_rule.get_head())
                new_rule.add_recursive(rule_from_body.get_head())
    #for negatives in rule_from_body.get_negatives():
    #    for atom in negatives:
    #        if atom == new_rule.get_head():
    #            rule_from_body.add_recursive(new_rule.get_head())
    #            new_rule.add_recursive(rule_from_body.get_head())

    return temp_atoms


def get_body_atoms(values, positive_atoms, negative_atoms):

    if int(values[0]) > 0:
        for x in values[1:]:
            if "-" in x:
                negative_atoms.append(x.replace("-", ""))
            else:
                positive_atoms.append(x)

    return positive_atoms, negative_atoms


def update_dict(head, number, i, pos, neg, head_to_bodies):
    if (expressions := head_to_bodies.get(head)) is None:
        head_to_bodies[head] = expressions = Rule(head, number)

    expressions.add_associated_variable(i + 1)
    expressions.populate_positive(pos)
    expressions.populate_negative(neg)


def create_disj_rules(n_heads, values, i, number, head_to_bodies):
    heads_id = values[:n_heads]
    for pos, id in enumerate(heads_id):
        positive_atoms, negative_atoms = get_body_atoms(values[n_heads:], [], [x for x in heads_id if x != id])
        update_dict(id, number, i+pos, positive_atoms, negative_atoms, head_to_bodies)


def create_atoms(rules, number, aspif=False):
    if aspif:
        return create_atoms_aspif(rules, number)
    return create_atoms_text(rules, number)


def create_atoms_aspif(rules, number):
    head_to_bodies = {}
    # Consideriamo solo le righe che rappresentano una regola
    rules = [rule for rule in rules if rule[0] == "1"]
    facts = [rule for rule in rules if rule[0] == "4" and rule[-1] == "0"]
    n_disj = 0
    for i, rule in enumerate(rules):
        index = 1
        values = rule.split(" ")
        assert values[index] == "0", "Second value in the aspif syntax must be equal to 0, since choice rules are not " \
                                     "supported at the moment "

        index += 1
        n_heads = int(values[index])
        if n_heads > 1:
            # Aggiungiamo a n_disj il numero di righe in più considerato, così da assegnare la variabile corretta
            create_disj_rules(n_heads, values[index+1:], i+n_disj, number, head_to_bodies)
            n_disj += n_heads - 1
            continue

        elif n_heads == 0:
            head = "bot"
        elif n_heads == 1:
            index += 1
            head = values[index]

        index += 1
        assert values[index] == "0", "First value for the body in the ASPIF syntax must be equal to 0, since weighted" \
                                     "bodies are not supported at the moment"

        index += 1
        positive_atoms, negative_atoms = [], []
        positive_atoms, negative_atoms = get_body_atoms(values[index:], positive_atoms, negative_atoms)

        update_dict(head, number, i + n_disj, positive_atoms, negative_atoms, head_to_bodies)

    return head_to_bodies, facts


def create_atoms_text(rules, number):
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

        expressions.add_associated_variable(i + 1)

        if body is not None:
            positive_atoms = [atom for atom in re.split(r',\s*(?![^()]*\))', body[:-1]) if "not " not in atom]
            negative_atoms = [atom.replace("not ", "") for atom in re.split(r',\s*(?![^()]*\))', body[:-1]) if
                              "not " in atom]
            expressions.populate_positive(positive_atoms)
            expressions.populate_negative(negative_atoms)

            # If no rules with head as atoms of body, add to no support
            # Otherwise, check if recursive with head
            for atom in positive_atoms:
                if (temp_atom := head_to_bodies.get(atom)) is not None:
                    check_recursive(temp_atom, expressions)
                else:
                    atom_without_support[atom] = Rule(atom, number)
            for atom in negative_atoms:
                if (temp_atom := head_to_bodies.get(atom)) is not None:
                    pass
                    check_recursive(temp_atom, expressions)
                else:
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


def create_rules(head_to_bodies, number, manual, opt1, opt2):
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
            rules.append(elem.create_inference_manual(i))
            if opt1:
                rules.append(elem.create_optimization_manual_one(i))
            if opt2:
                rules.append(elem.create_optimization_manual_one(i))
            rules.append(elem.create_completion_manual(i))
        else:
            rules.extend(elem.create_rules(opt1, opt2))
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


def writer(model, name_file, output_path, printer, manual, number):
    if printer and not manual:
        print(model.serialize())
        if number == REAL:
            write_smtlib(model, output_path + name_file, QF_RDL)
        else:
            write_smtlib(model, output_path + name_file, QF_IDL)
        with open(output_path + name_file, "r") as r:
            text = r.read()
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
