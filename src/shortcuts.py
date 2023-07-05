from pysmt.environment import get_env

And = get_env().formula_manager.And
Or = get_env().formula_manager.Or
Implies = get_env().formula_manager.Implies
GT = get_env().formula_manager.GT
LT = get_env().formula_manager.LT
Not = get_env().formula_manager.Not
Bool = get_env().formula_manager.Bool
Symbol = get_env().formula_manager.Symbol
