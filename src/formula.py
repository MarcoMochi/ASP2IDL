from pysmt.typing import INT, REAL, BOOL
from shortcuts import And, Or, Not, Implies, GT, LT, Eq, Bool, Symbol, SuspendTypeChecking
types = [INT, REAL]


class Rule:
    def __init__(self, head, type_, support=True, optimization=False):
        self.head = head
        self._recursive = []
        self._positive_body = []
        self._negative_body = []
        self._rules_id = []
        self.type = type_
        self.ott = optimization
        self.support = support

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

    # W_n -> (H > B+)_SCC and (bot > B+)_notSCC and not (B- < bot)
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

    # H > B+ -> B+ < bot
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

    # IF B in SCC(H): H > B+ -> B+ < bot
    def create_difference_sccs(self):
        temp_and = []
        for pos in self._positive_body:
            for atom in pos:
                if atom in self._recursive:
                    if len(pos) == 1:
                        with SuspendTypeChecking():
                            temp_and.append(Implies(LT(Symbol(atom, self.type), Symbol(self.head, self.type)),
                                                And(LT(Symbol(atom, self.type), Symbol("bot", self.type)),
                                                LT(Symbol(self.head, self.type), Symbol("bot", self.type)))))
                    else:
                        with SuspendTypeChecking():
                            temp_and.append(Implies(LT(Symbol(atom, self.type), Symbol(self.head, self.type)),
                                                LT(Symbol(atom, self.type), Symbol("bot", self.type))))

        return And(temp_and)

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

    # NOT USED
    # B+ < H and not (B- < bot) -> h < bot
    def create_inference_opt3(self):
        temp_and = []
        for positive, negative in zip(self._positive_body, self._negative_body):
            if self.head == "bot":
                return Bool(True)
            with SuspendTypeChecking():
                    temp_and.append(Implies(And(self.rule_inference_opt3(positive, negative)),
                                        LT(Symbol(self.head, self.type), Symbol("bot", self.type))))
        return And(temp_and)

    def rule_inference_opt3(self, pos, neg):
        temp = []
        for pos, neg in pos:
            with SuspendTypeChecking():
                temp.append(Implies(And(LT(Symbol(atom, self.type), Symbol(self.head, self.type)),
                                        Not(LT(Symbol(atom, self.type), Symbol("bot", self.type)))),
                                    Not(LT(Symbol(self.head, self.type), Symbol("bot", self.type)))))

        return temp

    # # NOT USED
    # B < H and not ( B < bot) -> not (H < bot)
    def create_inference_opt(self):
        temp_and = []
        for positive in self._positive_body:
            if self.head == "bot":
                return Bool(True)
            with SuspendTypeChecking():
                temp_and.extend(self.rule_inference_opt(positive))
                #temp_and.append(Implies(And(self.rule_inference_opt(positive)),
                #                        Not(LT(Symbol(self.head, self.type), Symbol("bot", self.type)))))
        return And(temp_and)

    def rule_inference_opt(self, pos):
        temp = []
        for atom in pos:
            if atom in self._recursive:
                with SuspendTypeChecking():
                    temp.append(Implies(And(LT(Symbol(atom, self.type), Symbol(self.head, self.type)),
                                            Not(LT(Symbol(atom, self.type), Symbol("bot", self.type)))),
                                        Not(LT(Symbol(self.head, self.type), Symbol("bot", self.type)))))

        return temp

    # NOT USED
    def create_transitives(self, temp_head, pos):
        return Implies(And(
                        LT(Symbol(pos, self.type), Symbol(temp_head, self.type)),
                        LT(Symbol(temp_head, self.type), Symbol(self.head, self.type)),
                        ),
            (LT(Symbol(pos, self.type), Symbol(self.head, self.type)))
            )

    # NOT USED
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