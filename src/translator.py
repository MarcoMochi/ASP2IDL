from formula import Rule
import re
from pysmt.shortcuts import And, write_smtlib
from pysmt.typing import REAL
from tqdm import tqdm
from shortcuts import Bool, SuspendTypeChecking


def get_sccs(file, head_to_atoms, aspif=False):
    involved_atoms = {}
    with open(file) as f:
        whole = f.read()
        values = [x.strip() for x in whole.split("scc_atom")  if len(x)>0]
        for x in values:
            id = re.search("\d+", x.split(",")[0]).group(0)
            if aspif:
                atom = re.search("\d+", x.split(",")[1]).group(0)
            else:
                atom = x.split(",", 2)[-1][:-1]
            try:
                involved_atoms[id].append(atom)
            except:
                involved_atoms[id] = [atom]

    for id_scc, atoms in involved_atoms.items():
        for i, atom in enumerate(atoms):
            if atom in head_to_atoms.keys():
                head_to_atoms[atom].set_recursive(atoms[:i] + atoms[i + 1:])

    return head_to_atoms


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


def check_support(atoms, number, reference, no_support, head):
    for atm in atoms:
        if reference.get(atm) is not None:
            continue
        else:
            no_support[atm] = [Rule(atm, number, support=False), head]


def update_rules_with_not_supported(rule, reference):
    no_support = str(rule[0].get_head())
    to_update = rule[1]

    assert reference[to_update], "Rule to update deleting not supported atoms is not present"
    neg = reference[to_update].get_negatives()
    for elems in neg:
        if no_support in elems:
            elems.remove(no_support)


def create_atoms_aspif(rules, number):
    head_to_bodies = {}
    atom_without_support = {}
    # Filter out lines not representing a rule
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
            # update the var n_disj, so every line is correctly identified after the decoupling of the disj. rule
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

        check_support(positive_atoms, number, head_to_bodies, atom_without_support, head)
        check_support(negative_atoms, number, head_to_bodies, atom_without_support, head)

        if head in atom_without_support.keys():
            del atom_without_support[head]

        update_dict(head, number, i + n_disj, positive_atoms, negative_atoms, head_to_bodies)

    for key, rule in atom_without_support.items():
        update_rules_with_not_supported(rule, head_to_bodies)

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
                    #check_recursive(temp_atom, expressions)
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


def create_rules(head_to_bodies,sccs=None):
    rules = []
    definitions = []
    atoms = set()
    variable = set()

    for key, elem in tqdm(head_to_bodies.items(), total=len(head_to_bodies)):

        atoms.add(key)
        variable.update(elem.get_rules_id())
        if sccs:
            temp = elem.create_association_scc()
            if temp is not Bool(True):
                rules.append(temp)
            if len(elem.get_recursive()) > 0:
                temp = elem.create_difference_sccs()
                if temp is not Bool(True):
                    rules.append(temp)
        else:
            temp = elem.create_association()
            if temp is not Bool(True):
                rules.append(temp)
            temp = elem.create_difference()
            if temp is not Bool(True):
                rules.append(temp)
        temp = elem.create_completion()
        if temp is not Bool(True):
            rules.append(temp)
        temp = elem.create_inference()
        if temp is not Bool(True):
            rules.append(temp)

        head_to_bodies[key] = None

    for atom in atoms:
        definitions.append(f"(declare-fun |{atom}| () Int)")
    for atom in variable:
        definitions.append(f"(declare-fun {atom} () Bool)")
    return definitions, And(rules).to_smtlib(daggify=False)


def writer(model, definitions, name_file, output_path, printer, number):
    if printer:
        with SuspendTypeChecking():
            try:
                with open(output_path + name_file, "w") as w:
                    w.write(f"(set-logic QF_IDL)\n")
                    for defs in definitions:
                        w.write(f"{defs}\n")
                    w.write("(assert(and\n")
                    w.write(f"{model}\n")
                    w.write("))\n")
                    w.write(f"(check-sat)\n")
                    w.write(f"(get-model)\n")
            except:
                print("Was not able to produce a translated file")
