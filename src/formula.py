from pysmt.shortcuts import Symbol, Bool, And, Or, Implies, GT, LT, Not
from pysmt.typing import INT, REAL, BOOL

types = [INT, REAL]


class Rule:
    def __init__(self, head, type_, optimization=False):
        if type_ not in types:
            raise ValueError(f"error: type must be one of {types}")
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

    # Creation of rules using pysmt library
    def create_association(self, rule_id, positive, negative):
        total_and = []
        if self.head == "bot":
            total_and.append(Implies(Symbol(rule_id, BOOL), Not(self.rule_associated(positive, negative))))
        else:
            if len(positive) > 0 or len(negative) > 0:
                total_and.append(Implies(Symbol(rule_id, BOOL), self.rule_associated(positive, negative)))
        return And(total_and)

    def rule_associated(self, pos, neg):
        temp_and = []
        for atom in pos:
            temp_and.append(GT(Symbol(self.head, self.type), Symbol(atom, self.type)))
        for atom in neg:
            temp_and.append(Not(LT(Symbol(atom, self.type), Symbol("bot", self.type))))
        return And(temp_and)

    def create_difference(self, positive, negative):
        total_and = []
        if len(positive) > 0:
            if self.head == "bot":
                return And([])
            else:
                total_and.append(self.rule_difference(positive, negative))

        return And(total_and)

    def rule_difference(self, pos, neg):
        temp_and = []
        if len(pos) > 1 or len(neg) > 0 or not self.ott:
            for atom in pos:
                temp_and.append(Implies(GT(Symbol(self.head, self.type), Symbol(atom, self.type)),
                                        LT(Symbol(atom, self.type), Symbol("bot", self.type))))
        else:
            temp_and.append(Implies(GT(Symbol(self.head, self.type), Symbol(pos[0], self.type)),
                                    (And(LT(Symbol(pos[0], self.type), Symbol("bot", self.type))),
                                     LT(Symbol(self.head, self.type), Symbol("bot", self.type)))))
        return And(temp_and)

    def create_inference(self, positive, negative):
        temp_and = []
        if self.head == "bot":
            return Bool(True)
        if len(positive) + len(negative) == 0:
            temp_and.append(LT(Symbol(self.head, self.type), Symbol("bot", self.type)))
        else:
            temp_and.append(Implies(And(self.rule_inference(positive, negative)),
                                    LT(Symbol(self.head, self.type), Symbol("bot", self.type))))
        return And(temp_and)

    def rule_inference(self, pos, neg):
        temp = []
        for atom in pos:
            temp.append(LT(Symbol(atom, self.type), Symbol("bot", self.type)))
        for atom in neg:
            temp.append(Not(LT(Symbol(atom, self.type), Symbol("bot", self.type))))
        return temp

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
        return Implies(And(Not(LT(Symbol(atom, self.type), Symbol(self.head, self.type))),
                           LT(Symbol(atom, self.type), Symbol("bot", self.type))),
                       LT(Symbol(self.head, self.type), Symbol("bot", self.type)))

    def rule_optimization_two(self, atom):
        # A > B -> not B > A
        return Implies(LT(Symbol(atom, self.type), Symbol(self.head, self.type)),
                       Not(LT(Symbol(self.head, self.type), Symbol(atom, self.type))))

    def create_completion(self):
        if len(self._rules_id) > 0:
            if self.head == "bot":
                return And(self.rule_completion())
            related = self.rule_completion()
            if len(related) != 0:
                return Implies(LT(Symbol(self.head, self.type), Symbol("bot", self.type)), Or(related))
            else:
                return And([])
        else:
            return Not(LT(Symbol(self.head, self.type), Symbol("bot", self.type)))

    def rule_completion(self):
        temp = []
        for i, atom in enumerate(self._rules_id):
            if len(self._positive_body[i]) + len(self._negative_body[i]) == 0:
                continue
            temp.append(Symbol(atom, BOOL))
        return temp

    def create_rules(self, opt1, opt2):
        rules = []
        for rule_id, positive, negative in zip(self._rules_id, self._positive_body, self._negative_body):
            rules.append(self.create_association(rule_id, positive, negative))
            rules.append(self.create_difference(positive, negative))
            rules.append(self.create_inference(positive, negative))
            rules.append(self.create_optimization(opt1, opt2))
        rules.append(self.create_completion())
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
