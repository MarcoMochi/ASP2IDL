from pysmt.shortcuts import Symbol, Bool, And, Or, Implies, Iff, GT, LT, LE, GE, Not, Equals, Int, Real
from pysmt.typing import INT, REAL, BOOL
types = [INT, REAL]

class Rule:
    def __init__(self, head, type):
        if type not in types:
            raise ValueError(f"error: type must be one of {types}")
        self.head = head
        self._positive_body = []
        self._negative_body = []
        self._rules_id = []
        self.type = type

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

    def create_association(self):
        total_and = []
        for rule_id, positive, negative in zip(self._rules_id, self._positive_body, self._negative_body):
            if self.head == "F":
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
            temp_and.append(Not(Symbol(atom+"_B", BOOL)))
        return And(temp_and)

    def create_difference(self):
        total_and = []
        for positive in self._positive_body:
            if len(positive) > 0:
                if self.head == "F":
                    return And([])
                else:
                    total_and.append(self.rule_difference(positive))

        return And(total_and)

    def rule_difference(self, pos):
        temp_and = []
        for atom in pos:
            temp_and.append(Implies(GT(Symbol(self.head, self.type), Symbol(atom, self.type)), And(Symbol(self.head+"_B", BOOL),Symbol(atom+"_B", BOOL))))
        return And(temp_and)


    def create_completion(self):
        if len(self._rules_id) > 0:
            if self.head == "F":
                return Iff(Bool(True), And(self.rule_completion()))
            return Iff(Symbol(self.head+"_B", BOOL), Or(self.rule_completion()))
        else:
            return Iff(Bool(True),Not(Symbol(self.head+"_B", BOOL)))

    def rule_completion(self):
        temp = []
        for atom in self._rules_id:
            temp.append(Symbol(atom, BOOL))
        return temp

    def create_relation_bool(self):
        return Iff(Symbol(self.head+"_B", BOOL), LT(Symbol(self.head, self.type), Symbol("bot", self.type)))