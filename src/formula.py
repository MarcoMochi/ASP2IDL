from pysmt.shortcuts import Symbol, Bool, And, Or, Implies, Iff, GT, LT, LE, GE, Not, Equals, Int, Real
from pysmt.typing import INT, REAL, BOOL
types = [INT, REAL]

class Rule:
    def __init__(self, head, type, ottimization=False):
        if type not in types:
            raise ValueError(f"error: type must be one of {types}")
        self.head = head
        self._positive_body = []
        self._negative_body = []
        self._rules_id = []
        self.type = type
        self.ott = ottimization

    def add_associated_variable(self, id):
        self._rules_id.append(f"W{str(id)}")

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


    #Creation of rules using pysmt library
    def create_association(self):
        total_and = []
        for rule_id, positive, negative in zip(self._rules_id, self._positive_body, self._negative_body):
            if self.head == "bot":
                total_and.append(Iff(Symbol(rule_id, BOOL), Not(self.rule_associated(positive, negative))))
            else:
                total_and.append(Iff(Symbol(rule_id, BOOL), self.rule_associated(positive, negative)))
        return And(total_and)

    def rule_associated(self, pos, neg):
        temp_and = []
        if len(pos) == 0 and len(neg) == 0:
            return Bool(True)
        for atom in pos:
            temp_and.append(GT(Symbol(self.head, self.type), Symbol(atom, self.type)))
        for atom in neg:
            temp_and.append(Not(LT(Symbol(atom, self.type),Symbol("bot", self.type))))
        return And(temp_and)

    def create_difference(self):
        total_and = []
        for positive, negative in zip(self._positive_body, self._negative_body):
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
                temp_and.append(Implies(GT(Symbol(self.head, self.type), Symbol(atom, self.type)), LT(Symbol(atom, self.type),Symbol("bot", self.type))))
        else:
            temp_and.append(Implies(GT(Symbol(self.head, self.type), Symbol(pos[0], self.type)),
                                    (And(LT(Symbol(pos[0], self.type), Symbol("bot", self.type))),LT(Symbol(self.head, self.type), Symbol("bot", self.type)))))
        return And(temp_and)

    def create_completion(self):
        if len(self._rules_id) > 0:
            if self.head == "bot":
                return Iff(Bool(True), And(self.rule_completion()))
            return Iff(LT(Symbol(self.head, self.type),Symbol("bot", self.type)), Or(self.rule_completion()))
        else:
            return Iff(Bool(True),Not(LT(Symbol(self.head, self.type),Symbol("bot", self.type))))

    def rule_completion(self):
        temp = []
        for atom in self._rules_id:
            temp.append(Symbol(atom, BOOL))
        return temp

    ##Creation of rules manuall
    def create_association_manual(self, i):
        final_rule = ""
        used_var = []
        j = 0
        for rule_id, positive, negative in zip(self._rules_id, self._positive_body, self._negative_body):
            rule = "(assert ("
            if self.head == "bot":
                used_var.append(rule_id)
                rule += f"= {rule_id} (not {(self.rule_associated_manual(positive, negative))}))"
            else:
                rule += f"= {rule_id} {self.rule_associated_manual(positive, negative)})"
            final_rule += rule +")\n"
            j += 1
        return final_rule[:-1]

    def rule_associated_manual(self, pos, neg):
        rule = ""
        if len(pos) == 0 and len(neg) == 0:
            return "true"
        if len(pos) + len(neg) > 1:
            rule += "(and "
        for atom in pos:
            rule += f"(< |{atom}| |{self.head}|) "
        for atom in neg:
            rule += f"(not (< |{atom}| bot)) "
        if len(pos) + len(neg) > 1:
            return rule + ")"
        return rule

    def create_difference_manual(self,i):
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


    def create_completion_manual(self, i):
        rule = f"(assert (= "
        if len(self._rules_id) > 0:
            if self.head == "bot":
                return rule + f"true (and {self.rule_completion_manual()})) )"
            return rule + f"(< |{self.head}| bot) (or {self.rule_completion_manual()})) )"
        else:
            return rule + f"true (not (< |{self.head}| bot))))"

    def rule_completion_manual(self):
        rule = ""
        for atom in self._rules_id:
            rule += f"{atom} "
        return rule