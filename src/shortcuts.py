from pysmt.environment import get_env


class SuspendTypeChecking(object):
    """Context to disable type-checking during formula creation."""

    def __init__(self, env=None):
        if env is None:
            env = get_env()
        self.env = env
        self.mgr = env.formula_manager

    def __enter__(self):
        """Entering a Context: Disable type-checking."""
        self.mgr._do_type_check = lambda x : x
        return self.env

    def __exit__(self, exc_type, exc_val, exc_tb):
        """Exiting the Context: Re-enable type-checking."""
        self.mgr._do_type_check = self.mgr._do_type_check_real


And = get_env().formula_manager.And
Or = get_env().formula_manager.Or
Implies = get_env().formula_manager.Implies
GT = get_env().formula_manager.GT
LT = get_env().formula_manager.LT
Not = get_env().formula_manager.Not
Bool = get_env().formula_manager.Bool
Symbol = get_env().formula_manager.Symbol
