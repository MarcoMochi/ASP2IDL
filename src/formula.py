from pysmt.typing import INT, REAL, BOOL
from shortcuts import And, Or, Not, Implies, GT, LT, Bool, Symbol, SuspendTypeChecking
types = [INT, REAL]


class Rule:
    def __init__(self, head, type_, optimization=False):
        self.head = head
        self._recursive = []
        self._positive_body = []
        self._negative_body = []
        self._rules_id = []
        self.type = type_
        self.ott = optimization

    def get_head(self):
        return self.head

    def add_associated_variable(self, id_):
        self._rules_id.append(f"W{str(id_)}")

    def populate_positive(self, body):
        self._positive_body.append(body)

    def populate_negative(self, body):
        self._negative_body.append(body)

    def get_positives(self):
        return self._positive_body

    def get_negatives(self):
        return self._negative_body

    def get_rules_id(self):
        return self._rules_id

    def add_recursive(self, atom):
        self._recursive.append(atom)

    def set_recursive(self, atoms):
        self._recursive = atoms

    def get_recursive(self):
        return self._recursive
    # Creation of rules using pysmt library

    # Create formulas like:
    # W_n -> H > B+ and not (B- < bot)
    def create_association(self):
        total_and = []
        for rule_id, positive, negative in zip(self._rules_id, self._positive_body, self._negative_body):
            if self.head == "bot":
                with SuspendTypeChecking():
                    total_and.append(Implies(Symbol(rule_id, BOOL), Not(self.rule_associated(positive, negative))))
            else:
                if len(positive) > 0 or len(negative) > 0:
                    with SuspendTypeChecking():
                        total_and.append(Implies(Symbol(rule_id, BOOL), self.rule_associated(positive, negative)))
        return And(total_and)

    def rule_associated(self, pos, neg):
        temp_and = []
        for atom in pos:
            with SuspendTypeChecking():
                temp_and.append(GT(Symbol(self.head, self.type), Symbol(atom, self.type)))
        for atom in neg:
            with SuspendTypeChecking():
                temp_and.append(Not(LT(Symbol(atom, self.type), Symbol("bot", self.type))))
        return And(temp_and)

    def create_association_scc(self):
        total_and = []
        for rule_id, positive, negative in zip(self._rules_id, self._positive_body, self._negative_body):
            if self.head == "bot":
                with SuspendTypeChecking():
                    total_and.append(Implies(Symbol(rule_id, BOOL), Not(self.rule_associated_scc(positive, negative))))
            else:
                if len(positive) > 0 or len(negative) > 0:
                    with SuspendTypeChecking():
                        total_and.append(Implies(Symbol(rule_id, BOOL), self.rule_associated_scc(positive, negative)))
        return And(total_and)

    def rule_associated_scc(self, pos, neg):
        temp_and = []
        for atom in pos:
            if atom in self._recursive:
                with SuspendTypeChecking():
                    temp_and.append(LT(Symbol(atom, self.type), Symbol(self.head, self.type)))
            else:
                with SuspendTypeChecking():
                    temp_and.append(LT(Symbol(atom, self.type), Symbol("bot", self.type)))
        for atom in neg:
            with SuspendTypeChecking():
                temp_and.append(Not(LT(Symbol(atom, self.type), Symbol("bot", self.type))))
        return And(temp_and)

    # Create formulas like:
    # H > B+ -> B+ < bot
    # Se un solo atomo positivo: H > B+ -> B+ < bot and H < bot
    def create_difference(self):
        total_and = []
        for positive, negative in zip(self._positive_body, self._negative_body):
            if len(positive) > 0:
                if self.head == "bot":
                    return And([])
                else:
                    with SuspendTypeChecking():
                        total_and.append(self.rule_difference(positive, negative))

        return And(total_and)

    def rule_difference(self, pos, neg):
        temp_and = []
        if len(pos) > 1 or len(neg) > 0 or not self.ott:
            for atom in pos:
                with SuspendTypeChecking():
                    temp_and.append(Implies(GT(Symbol(self.head, self.type), Symbol(atom, self.type)),
                                        LT(Symbol(atom, self.type), Symbol("bot", self.type))))
        else:
            with SuspendTypeChecking():
                temp_and.append(Implies(GT(Symbol(self.head, self.type), Symbol(pos[0], self.type)),
                                    (And(LT(Symbol(pos[0], self.type), Symbol("bot", self.type))),
                                     LT(Symbol(self.head, self.type), Symbol("bot", self.type)))))
        return And(temp_and)

    def create_difference_sccs(self):
        temp_and = []
        for atom in self._recursive:
            with SuspendTypeChecking():
                temp_and.append(Implies(GT(Symbol(self.head, self.type), Symbol(atom, self.type)),
                                    LT(Symbol(atom, self.type), Symbol("bot", self.type))))
        return And(temp_and)

    # Create formulas like:
    # If sum(B+,B-) == 0 creates H < bot
    # Otherwise B+ < bot and not (B- < bot) -> H < bot
    def create_inference(self):
        temp_and = []
        for positive, negative in zip(self._positive_body, self._negative_body):
            if self.head == "bot":
                return Bool(True)
            if len(positive) + len(negative) == 0:
                with SuspendTypeChecking():
                    temp_and.append(LT(Symbol(self.head, self.type), Symbol("bot", self.type)))
            else:
                with SuspendTypeChecking():
                    temp_and.append(Implies(And(self.rule_inference(positive, negative)),
                                        LT(Symbol(self.head, self.type), Symbol("bot", self.type))))
        return And(temp_and)

    def rule_inference(self, pos, neg):
        temp = []
        for atom in pos:
            with SuspendTypeChecking():
                temp.append(LT(Symbol(atom, self.type), Symbol("bot", self.type)))
        for atom in neg:
            with SuspendTypeChecking():
                temp.append(Not(LT(Symbol(atom, self.type), Symbol("bot", self.type))))
        return temp

    ## Opt 2 Jelia Enrico. Mettere che al posto di B+ < bot si abbia B+ < H. Che implica B+ < bot.
    def create_inference_opt(self):
        temp_and = []
        for positive, negative in zip(self._positive_body, self._negative_body):
            if self.head == "bot":
                return Bool(True)
            with SuspendTypeChecking():
                    temp_and.append(Implies(And(self.rule_inference_opt(positive, negative)),
                                        LT(Symbol(self.head, self.type), Symbol("bot", self.type))))
        return And(temp_and)

    def rule_inference_opt(self, pos, neg):
        temp = []
        for atom in pos:
            with SuspendTypeChecking():
                temp.append(LT(Symbol(atom, self.type), Symbol(self.head, self.type)))
        for atom in neg:
            with SuspendTypeChecking():
                temp.append(Not(LT(Symbol(atom, self.type), Symbol("bot", self.type))))
        return temp

    # Create two optimization clauses
    def create_optimization(self, opt1, opt2):
        temp_and = []
        if self.head == "bot" or len(self._recursive) == 0:
            return Bool(True)
        if opt1 and opt2:
            for atom in self._recursive:
                temp_and.append(self.rule_optimization_one(atom))
                temp_and.append(self.rule_optimization_two(atom))
        elif opt1:
            for atom in self._recursive:
                temp_and.append(self.rule_optimization_one(atom))
        elif opt2:
            for atom in self._recursive:
                temp_and.append(self.rule_optimization_two(atom))

        return And(temp_and)

    def rule_optimization_one(self, atom):
        # ¬A > B ∧ ⊥ > B → ⊥ > A.
        with SuspendTypeChecking():
            return Implies(And(Not(LT(Symbol(atom, self.type), Symbol(self.head, self.type))),
                           LT(Symbol(atom, self.type), Symbol("bot", self.type))),
                       LT(Symbol(self.head, self.type), Symbol("bot", self.type)))

    def rule_optimization_two(self, atom):
        # A > B -> not B > A
        with SuspendTypeChecking():
            return Implies(LT(Symbol(atom, self.type), Symbol(self.head, self.type)),
                       Not(LT(Symbol(self.head, self.type), Symbol(atom, self.type))))

    # Create formulas like:
    # if bot is head: W_i and ... and W_n
    # Otherwise: H < bot -> W_i or .. or W_n
    def create_completion(self):
        if len(self._rules_id) > 0:
            if self.head == "bot":
                with SuspendTypeChecking():
                    return And(self.rule_completion())
            related = self.rule_completion()
            if len(related) != 0:
                with SuspendTypeChecking():
                    return Implies(LT(Symbol(self.head, self.type), Symbol("bot", self.type)), Or(related))
            else:
                return And([])
        else:
            with SuspendTypeChecking():
                return Not(LT(Symbol(self.head, self.type), Symbol("bot", self.type)))

    def rule_completion(self):
        temp = []
        for i, atom in enumerate(self._rules_id):
            if len(self._positive_body[i]) + len(self._negative_body[i]) == 0:
                continue
            temp.append(Symbol(atom, BOOL))
        return temp

    def create_rules(self, opt1, opt2, sccs):
        rules = []
        for positive, negative in zip(self._positive_body, self._negative_body):
            rules.append(self.create_inference(positive, negative))

        #rules.append(self.create_optimization(opt1, opt2))
        return rules

    # Creation of rules manual
    def create_association_manual(self, i):
        final_rule = ""
        used_var = []
        j = 0
        for rule_id, positive, negative in zip(self._rules_id, self._positive_body, self._negative_body):
            rule = "(assert ("
            if self.head == "bot":
                used_var.append(rule_id)
                rule += f"=> {rule_id} (not {(self.rule_associated_manual(positive, negative))}))"
            else:
                if len(positive) + len(negative) == 0:
                    continue
                rule += f"=> {rule_id} {self.rule_associated_manual(positive, negative)})"
            final_rule += rule + ")\n"
            j += 1
        return final_rule[:-1]

    def rule_associated_manual(self, pos, neg):
        rule = ""
        if len(pos) + len(neg) > 1:
            rule += "(and "
        for atom in pos:
            rule += f"(< |{atom}| |{self.head}|) "
        for atom in neg:
            rule += f"(not (< |{atom}| bot)) "
        if len(pos) + len(neg) > 1:
            return rule + ")"
        return rule

    def create_difference_manual(self, i):
        rule = ""
        for positive, negative in zip(self._positive_body, self._negative_body):
            if len(positive) > 0:
                if self.head == "bot":
                    return rule
                else:
                    rule += f"(assert ({self.rule_difference_manual(positive, negative)})\n"

        return rule[:-1]

    def rule_difference_manual(self, pos, neg):
        rule = "and "
        if len(pos) > 1 or len(neg) > 0 or not self.ott:
            for atom in pos:
                rule += f"(=> (< |{atom}| |{self.head}|) (< |{atom}| bot))"
        else:
            rule += f"(=> (< |{pos[0]}| |{self.head}|) (and (< |{pos[0]}| bot) (< |{self.head}| bot)))"
        return rule + ")"

    def create_inference_manual(self, i):
        if self.head == "bot":
            return ""
        rule = ""
        for positive, negative in zip(self._positive_body, self._negative_body):
            if len(positive) + len(negative) == 0:
                rule += f"(assert(< |{self.head}| bot))\n"
            else:
                rule += f"(assert(=> (and {self.rule_inference_manual(positive, negative)}) (< |{self.head}| bot)))\n"
        return rule[:-1]

    def rule_inference_manual(self, pos, neg):
        rule = ""
        for atom in pos:
            rule += f"(< |{atom}| bot) "
        for atom in neg:
            rule += f"(not (< |{atom}| bot)) "
        return rule

    def create_completion_manual(self, i):
        rule = f"(assert (=> "
        if len(self._rules_id) > 0:
            related = self.rule_completion_manual()
            if related != "":
                if self.head == "bot":
                    return f"(assert (and {self.rule_completion_manual()}))"
                return rule + f"(< |{self.head}| bot) (or {related})) )"
            else:
                return ""
        else:
            return f"(assert (not (< |{self.head}| bot)))"

    def rule_completion_manual(self):
        rule = ""
        for i, atom in enumerate(self._rules_id):
            if len(self._positive_body[i]) + len(self._negative_body[i]) > 0:
                rule += f"{atom} "
        return rule
