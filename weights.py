# Calculating Weights
# I want to use vector weights Vector Weights
from dataclasses import dataclass
from term import Term, Function_Symbol, Constant, Variable, QuoteInteger, QuoteReal, IntegerVariable, integer_variable_registry
from typing import Union, Dict, List, Tuple
import z3
import functools
import itertools


@dataclass(frozen=True)
class VariableWeight:
    name: str
    def __repr__(self):
        return f"W({self.name})"

@dataclass(frozen=True)
class ConstantWeight:
    value: int
    def __repr__(self):
        return str(self.value)

@dataclass(frozen=True)
class WeightOperation:
    op: str
    args: list['SymbolicWeight']
    def __repr__(self):
        arg_str = f" {self.op} ".join(map(str, self.args))
        return f"({arg_str})"

class VariableConstantComparisonError(Exception):
    """Raised when a comparison between a variable and a constant is required but not defined."""
    pass

class IndeterminateWeightError(Exception):
    """Raised when Z3 cannot determine the relationship between two weights."""
    def __init__(self, lhs_weight, rhs_weight, metric_index):
        self.lhs_weight = lhs_weight
        self.rhs_weight = rhs_weight
        self.metric_index = metric_index

SymbolicWeight = Union[VariableWeight, ConstantWeight, WeightOperation]
number_of_implemented_metrics = 10
LEXICOGRAPHIC_METRIC_INDEX = number_of_implemented_metrics + 1
nested_exponentiation_score_metric = number_of_implemented_metrics-8
exponential_base_score_metric = number_of_implemented_metrics-9

def _add_z3_permutation_constraints(solver: z3.Solver, unsorted_z3_list: list[z3.ArithRef], prefix: str) -> list[z3.ArithRef]:
    #This helper function allows Z3 to sort lists which are given as unsorted inputs
    n = len(unsorted_z3_list)
    if n == 0:
        return []
    #Create new Z3 variables that will hold the sorted variables
    sorted_vars = z3.IntVector(f"{prefix}_sorted", n)

    #Add sorting constraints, ensures that new variables are in decending order:
    for i in range(n-1):
        solver.add(sorted_vars[i] >= sorted_vars[i+1])

    # Add permutation constraints, ensures that the sorted_vars is the same set of values as in the unsorted_z3_list
    permutation_clauses = []
    for permutation in itertools.permutations(unsorted_z3_list):
        equality_clause = z3.And([sorted_vars[i] == permutation[i] for i in range(n)])
        permutation_clauses.append(equality_caluse)
    solver.add(z3.Or(permutation_clauses))
    # For example, if unsorted_z3_list is [s1, s2], we generate the constraint:
    # Or(
    #   And(sorted_vars[0] == s1, sorted_vars[1] == s2),  // First permutation
    #   And(sorted_vars[0] == s2, sorted_vars[1] == s1)   // Second permutation
    # )
    return sorted_vars

#####16/12/25 - working on these functions
def evaluate_quote_term_runtime(term: Term) -> float:
    if isinstance(term.root, (QuoteInteger, QuoteReal)):
        return term.root.value
    if isinstance(term.root, Function_Symbol):
        args = [evaluate_quote_term_runtime(arg) for arg in term.arguments]
        if term.root.name == "+":
            return sum(args)
        if term.root.name == "-":
            if len(args) ==1:
                return -args[0]
            else:
                return args[0] - args[1]
        if term.root.name == "*":
            result = 1
            for arg in args:
                result *= arg
            return result
        if term.root.name == "^":
            return args[0] ** args[1]
    raise ValueError(f"Unexpected term in runtime quote evaluation: {term}")
    
def quote_term_to_symbolic_weight(term: Term) -> SymbolicWeight:
    if isinstance(term.root, (QuoteInteger, QuoteReal)):
        return ConstantWeight(term.root.value)
    if isinstance(term.root, (Constant, Variable, IntegerVariable)):
        return VariableWeight(term.root.name)
    if isinstance(term.root, Function_Symbol):
        args = [quote_term_to_symbolic_weight(arg) for arg in term.arguments]
        if term.root.name == "+":
            return WeightOperation("+", args)
        if term.root.name == "-":
            if len(args) == 1:
                return WeightOperation("*", [ConstantWeight(-1), args[0]])
            else:
                return WeightOperation("-", [args[0], args[1]])
        if term.root.name == "*":
            return WeightOperation("*", args)
        if term.root.name == "^":
            return WeightOperation("**", args)
        if term.root.name == "sin":
            return WeightOperation("sin", args)
        if term.root.name == "cos":
            return WeightOperation("cos", args)
    raise ValueError(f"Unexpected term in static analysis quote evaluation: {term}")

def semantic_quote_comparison(term1: Term, term2: Term, variable_order: dict, static_analysis) -> int:
    if not static_analysis:
        val1 = evaluate_quote_term_runtime(term1.arguments[0])
        val2 = evaluate_quote_term_runtime(term2.arguments[0])
        if val1 > val2:
            return 1
        if val2 > val1:
            return -1
        return 0
    else:
        w1 = quote_term_to_symbolic_weight(term1.arguments[0])
        w2 = quote_term_to_symbolic_weight(term2.arguments[0])
        try:
            val1 = evaluate_symbolic_weight(w1)
            val2 = evaluate_symbolic_weight(w2)
            if val1 > val2:
                return 1
            if val2 > val1:
                return -1
            return 0
        except TypeError:
            pass
        
        solver = z3.Solver()
        solver.set("timeout", 5000)
        z3_vars = {}
        def collect_vars(w):
            if isinstance(w, VariableWeight):
                return {w.name}
            if isinstance(w, WeightOperation):
                if not w.args:
                    return set()
                return set().union(*(collect_vars(a) for a in w.args))
            return set()
        all_vars = collect_vars(w1).union(collect_vars(w2))
        
        for name in all_vars:
            z3_vars[name] = z3.Int(name)
            solver.add(z3_vars[name] >=0)

        sorted_vars = sorted(variable_order.keys(), key = lambda v: variable_order[v], reverse = True)
        for i in range(len(sorted_vars) -1):
            high_var = sorted_vars[i]
            low_var = sorted_vars[i+1]
            if high_var.name in z3_vars and low_var.name in z3_vars:
                solver.add(z3_vars[high_var.name] > z3_vars[low_var.name])

        z3_w1 = symbolic_weight_to_z3(w1, z3_vars)
        z3_w2 = symbolic_weight_to_z3(w2, z3_vars)

        solver.push()
        solver.add(z3.Not(z3_w1 > z3_w2))
        if solver.check() == z3.unsat:
            return 1
        solver.pop()

        solver.push()
        solver.add(z3.Not(z3_w2 > z3_w1))
        if solver.check() == z3.unsat:
            return -1
        solver.pop()

        solver.push()
        solver.add(z3.Not(z3_w2 == z3_w1))
        if solver.check() == z3.unsat:
            return 0
        solver.pop()

        print(f"[WEIGHTS] Z3 Indeterminate:")
        print(f"  W1: {w1}")
        print(f"  W2: {w2}")
        print(f"  Vars in Z3: {z3_vars.keys()}")

        raise NotImplementedError(f"Z3 was unable to determine which of these weights is larger: {w1} or {w2}. We made require splitting over cases.") 
        
##### End 16/12/25 working on functions

def compute_single_metric(term: Term, metric_index: int, static_analysis: bool, variable_order: dict, memo_cache: dict, function_symbol_registry, constant_order: dict, extra_constraints: list = []):

    def _flatten_multiplication_chain(current_term: Term) -> list[Term]:
        if isinstance(current_term.root, Function_Symbol) and current_term.root.name == "quote":
            return [current_term]
        if isinstance(current_term.root, Function_Symbol) and current_term.root.name in ['*', '/']:
            left_factors = _flatten_multiplication_chain(current_term.arguments[0])
            right_factors = _flatten_multiplication_chain(current_term.arguments[1])
            return left_factors + right_factors
        else:
            return [current_term]
    
    def _find_multiplication_chains_recursive(current_term: Term, is_inside_mult: bool = False) -> list[list[Term]]:
        if isinstance(current_term.root, Function_Symbol) and current_term.root.name == "quote":
            return []
        all_chains = []
        if isinstance(current_term.root, Function_Symbol) and current_term.root.name in ['*', '/']:
            chain = _flatten_multiplication_chain(current_term)
            if len(chain) >1:
                all_chains.append(chain)
    
            for factor in chain:
                all_chains.extend(_find_multiplication_chains_recursive(factor, is_inside_mult=True))

        elif isinstance(current_term.root, Function_Symbol) and current_term.root.name in ['+', '-']:
            for arg in current_term.arguments:
                all_chains.extend(_find_multiplication_chains_recursive(arg, is_inside_mult=False))
        
        else:
            if not is_inside_mult:
                all_chains.append([current_term])
            for arg in current_term.arguments:
                all_chains.extend(_find_multiplication_chains_recursive(arg, is_inside_mult=False))
    
        return all_chains

    def _find_monomials_for_addition_score(current_term: Term) -> list[list[Term]]:
        if isinstance(current_term.root, Function_Symbol) and current_term.root.name == "quote":
            return []      
        monomials = []
        if isinstance(current_term.root, Function_Symbol) and current_term.root.name in ["*", "/"]:
            chain = _flatten_multiplication_chain(current_term)
            if len(chain) > 1:
                monomials.append(chain)
            
            for factor in chain:
                monomials.extend(_find_monomials_for_addition_score(factor))
            return monomials
        
        if isinstance(current_term.root, Variable):
            return [[current_term]]
        
        for arg in current_term.arguments:
            monomials.extend(_find_monomials_for_addition_score(arg))
        
        return monomials
    
    def _find_all_addition_nodes(current_term: Term) -> list[Term]:
        if isinstance(current_term.root, Function_Symbol) and current_term.root.name == "quote":
            return []
        addition_nodes = []
        if isinstance(current_term.root, Function_Symbol) and current_term.root == function_symbol_registry["+"]:
            addition_nodes.append(current_term)
        for argument in current_term.arguments:
            addition_nodes.extend(_find_all_addition_nodes(argument))
    
        return addition_nodes

    def _find_all_trig_nodes(current_term: Term) -> list[Term]:
        if isinstance(current_term.root, Function_Symbol) and current_term.root.name == "quote":
            return []
        trig_nodes = []
        if isinstance(current_term.root, Function_Symbol) and current_term.root.name in ["sin", "cos"]:
            trig_nodes.append(current_term)
        
        for arg in current_term.arguments:
            trig_nodes.extend(_find_all_trig_nodes(arg))
        return trig_nodes
    
    #For addition associativity
    def _count_additions_in_term(current_term: Term, static_analysis: bool) -> int:
        if isinstance(current_term.root, Function_Symbol) and current_term.root.name == "quote":
            if static_analysis:
                return ConstantWeight(0)
            else:
                0
        if static_analysis:
            if isinstance(current_term.root, Variable):
                return VariableWeight(current_term.root.name)
            if isinstance(current_term.root, (Constant, QuoteInteger, QuoteReal)):
                return ConstantWeight(0)
            if isinstance(current_term.root, Function_Symbol):
                arg_weights = [_count_additions_in_term(arg, static_analysis) for arg in current_term.arguments]
                if current_term.root == function_symbol_registry["+"]:
                    return WeightOperation("+", [ConstantWeight(1)] + arg_weights)
                else:
                    if not arg_weights:
                        return ConstantWeight(0)
                    return WeightOperation('+', arg_weights)
        else:
            count = 0
            if isinstance(current_term.root, Function_Symbol):
                if current_term.root == function_symbol_registry["+"]:
                    count += 1
                    for argument in current_term.arguments:
                        count += _count_additions_in_term(argument, static_analysis)
            return count
    
    def calculate_max_block_sort_moves(monomial: list[Term], function_symbol_registry, static_analysis: bool, constant_order: bool, variable_order: dict = {}, memo_cache: dict={}) -> int:
        """
        Calculates the maximum number of valid "block sort" commutativity moves
        required to transform a given monomial into its fully sorted state.
    
        This is equivalent to finding the longest path in the state graph of permutations,
        where edges are valid block swaps. It uses memoized recursion (Dynamic Programming)
        to solve this efficiently.
        """
        def _get_cache_key(state_tuple, var_order_tuple):
            return (state_tuple, var_order_tuple)
        
        if len(monomial) <= 1:
            return 0
    
        def _is_block_A_greater_than_B(block_A: list[Term], block_B: list[Term], depth) -> bool:
            for i in range(min(len(block_A), len(block_B))):
                term_A = block_A[i]
                term_B = block_B[i]
    
                if _compare_summands_lexicographically(term_A, term_B, function_symbol_registry, static_analysis, constant_order, variable_order):
                    return True
                if _compare_summands_lexicographically(term_B, term_A, function_symbol_registry, static_analysis, constant_order, variable_order):
                    return False
            return False #len(block_A) > len(block_B) ####This line is the culprit
    
        def _sorting_comparator(term_A, term_B):
            if _compare_summands_lexicographically(term_A, term_B, function_symbol_registry, static_analysis, constant_order, variable_order):
                    result = 1
            elif _compare_summands_lexicographically(term_B, term_A, function_symbol_registry, static_analysis, constant_order, variable_order):
                    result =  -1
            else:
                result= 0
            return result
    
        sort_key = functools.cmp_to_key(_sorting_comparator)
    
        sorted_monomial = sorted(monomial, key=sort_key)
        target_state_tuple = tuple(sorted_monomial)
        var_order_tuple = tuple(sorted(variable_order.items(), key=lambda item: item[0].name if hasattr(item[0], 'name') else str(item[0]))) #Note that this order is only used for presenting keys to be used in the cache, not to compare variables. 
    
        def _find_longest_path(current_state_tuple: tuple[Term, ...], memo_cache: dict, depth: int=0) -> int:
            if depth > 20: # Or a higher number like 50 if needed
                raise RecursionError(f"Exceeded max depth of 20. Cycle detected in state: {[str(t) for t in current_state_tuple]}")
            
            cache_key = _get_cache_key(current_state_tuple, var_order_tuple)
            #current_state_str = ' * '.join([str(t) for t in current_state_tuple])
            #cache_keys_str = { ' * '.join([str(t) for t in k]): v for k, v in memo_cache.items() }
            
            if cache_key in memo_cache:
                return memo_cache[cache_key]
    
            if current_state_tuple == target_state_tuple:
                memo_cache[cache_key] = 0
                return memo_cache[cache_key]
    
            max_moves = 0
            current_state_list = list(current_state_tuple)
            n = len(current_state_list)
    
            for j in range(1,n):
                for i in range(j):
                    for k in range(j+1, n+1):
                        prefix = current_state_list[:i]
                        block_A = current_state_list[i:j]
                        block_B = current_state_list[j:k]
                        suffix = current_state_list[k:]
                        
                        if _is_block_A_greater_than_B(block_A, block_B, depth):
                            next_state_list = prefix + block_B + block_A + suffix
    
                            path_from_next = _find_longest_path(tuple(next_state_list), memo_cache, depth + 1)
                            max_moves = max(max_moves, 1 + path_from_next)
            
            memo_cache[cache_key] = max_moves
            return max_moves
    
        result = _find_longest_path(tuple(monomial), memo_cache, 0)
            
        return result
    
    def _flatten_addition_chain(current_term: Term) -> list[Term]: #For the addition commutativity metric
        if isinstance(current_term.root, Function_Symbol) and current_term.root.name == "quote":
            return [current_term]
        if isinstance(current_term.root, Function_Symbol) and current_term.root.name in ['+','-']:
            left_summands = _flatten_addition_chain(current_term.arguments[0])
            right_summands = _flatten_addition_chain(current_term.arguments[1])
            return left_summands + right_summands
        else:
            return[current_term]
    
    def _is_numeric_equivalent(term: Term) -> bool: #Returns true if the value is purely numerical (or has a numeric base for exponentiation). This is important because we want to ignore numeric terms when bringing terms together with addition. 
        #Base case, the term is a quote term
        if isinstance(term.root, (QuoteInteger, QuoteReal)):
            return True
        if isinstance(term.root, Function_Symbol) and term.root.name == 'quote':
            return True
        #Check multiplication/division and exponentiation
        if isinstance(term.root, Function_Symbol):
            if term.root.name in ["*", "/"]:
                return all(_is_numeric_equivalent(arg) for arg in term.arguments)
            if term.root.name == "^":
                return _is_numeric_equivalent(term.arguments[0])
        return False
    
    def _compare_summands_lexicographically(term1: Term, term2: Term, function_symbol_registry: Dict[str,Tuple], static_analysis: bool, constant_order: Dict[str, int], variable_order: Dict[str, int], depth: int=0) -> bool: #returns true if term1 > term2 (if term1 should be moved after term2). 
        if term1 is term2:
            return False
        is_t1_atomic = isinstance(term1.root, (Constant, QuoteReal, QuoteInteger, Variable))
        is_t2_atomic = isinstance(term2.root, (Constant, QuoteReal, QuoteInteger, Variable))
    
        if is_t1_atomic and is_t2_atomic:
            return compare_terms_lexicographically(term1, term2, function_symbol_registry, constant_order, static_analysis=static_analysis, variable_order=variable_order, extra_constraints=extra_constraints)
        
        is_t1_numeric = _is_numeric_equivalent(term1)
        is_t2_numeric = _is_numeric_equivalent(term2)
        # If both are numeric, they are a tie in ordering.
        if is_t1_numeric and is_t2_numeric: return False
        # If term1 is numeric and term2 is not, term2 is greater.
        if is_t1_numeric and not is_t2_numeric: return False
        # If term1 is not numeric and term2 is, term1 is greater.
        if not is_t1_numeric and is_t2_numeric: return True
    
        #If we reach here, both terms are non-numeric
        #Next we check for trig terms
        is_t1_trig = isinstance(term1.root, Function_Symbol) and term1.root.name in ['sin', 'cos']
        is_t2_trig = isinstance(term2.root, Function_Symbol) and term2.root.name in ['sin', 'cos']
    
        if is_t1_trig and not is_t2_trig: 
            return True
        if not is_t1_trig and is_t2_trig: 
            return False
        if is_t1_trig and is_t2_trig:
            if term1.root.lexicographic_precedence_level > term2.root.lexicographic_precedence_level:
                return True
            if term2.root.lexicographic_precedence_level > term1.root.lexicographic_precedence_level:
                return False
            return _compare_summands_lexicographically(term1.arguments[0], term2.arguments[0], function_symbol_registry, static_analysis, constant_order, variable_order, depth+1)

        is_t1_quote = isinstance(term1.root, Function_Symbol) and term1.root.name == 'quote'
        is_t2_quote = isinstance(term2.root, Function_Symbol) and term2.root.name == 'quote'

        if is_t1_quote and is_t2_quote:
            result = semantic_quote_comparison(term1, term2, variable_order, static_analysis)
            if result ==1:
                return True
            if result ==-1:
                return False
            return False #Ties should return False

        if is_t1_quote or is_t2_quote:
            return compare_terms_lexicographically(term1, term2, function_symbol_registry, constant_order, static_analysis = static_analysis, variable_order = variable_order, extra_constraints=extra_constraints)

            
        def get_comparison_list(t:Term) -> list[Term]:
            if isinstance(t.root, Function_Symbol):
                if t.root.name in ['*', '/', '+', '-']: #11/11/2025 Added + and - to the list because the compare_summands_lexicographically is now used in multiplication chains as well as addition chains.
                    return [arg for arg in t.arguments if not isinstance(arg.root, (QuoteInteger, QuoteReal))]
                if t.root.name == "^":
                    return t.arguments
            return [t]
    
        args1 = get_comparison_list(term1)
        args2 = get_comparison_list(term2)
        for i in range(min(len(args1), len(args2))):
            sub_term1 = args1[i]
            sub_term2 = args2[i]
            if _compare_summands_lexicographically(sub_term1, sub_term2, function_symbol_registry, static_analysis, constant_order, variable_order, depth+1):
                return True
            if _compare_summands_lexicographically(sub_term2, sub_term1, function_symbol_registry, static_analysis, constant_order, variable_order, depth+1):
                return False
    
        if len(args1) > len(args2):
            return True
        if len(args1) < len(args2):
            return False
    
        return compare_terms_lexicographically(term1, term2, function_symbol_registry, constant_order, static_analysis=static_analysis, variable_order=variable_order, extra_constraints=extra_constraints)
    
    def _find_addition_chains_recursive(current_term: Term) -> list[list[Term]]:
        if isinstance(current_term.root, Function_Symbol) and current_term.root.name == "quote":
            return []
        all_chains = []
        if isinstance(current_term.root, Function_Symbol) and current_term.root.name in ['+', '-']:
            chain = _flatten_addition_chain(current_term)
            if len(chain) > 1:
                all_chains.append(chain)
    
            for summand in chain:
                if summand is not current_term:
                    all_chains.extend(_find_addition_chains_recursive(summand))
    
        else:
            for arg in current_term.arguments:
                all_chains.extend(_find_addition_chains_recursive(arg))
    
        return all_chains
    
    def _find_all_multiplication_nodes(current_term: Term) -> list[Term]:
        if isinstance(current_term.root, Function_Symbol) and current_term.root.name == "quote":
            return []
        mult_nodes = []
        if isinstance(current_term.root, Function_Symbol) and current_term.root == function_symbol_registry["*"]:
            mult_nodes.append(current_term)
        for argument in current_term.arguments:
            mult_nodes.extend(_find_all_multiplication_nodes(argument))
        return mult_nodes
    
    # For multiplication associativity
    def _count_multiplications_in_term(current_term: Term, static_analysis: bool) -> int:
        if isinstance(current_term.root, Function_Symbol) and current_term.root.name == "quote":
            if static_analysis:
                return ConstantWeight(0)
            else:
                return 0
        if static_analysis:
            if isinstance(current_term.root, Variable):
                return VariableWeight(current_term.root.name)
            if isinstance(current_term.root, (Constant, QuoteInteger, QuoteReal)):
                return ConstantWeight(0) # Changed from 0 to ConstantWeight(0) for consistency
            if isinstance(current_term.root, Function_Symbol):
                arg_weights = [_count_multiplications_in_term(arg, static_analysis) for arg in current_term.arguments]
                if current_term.root == function_symbol_registry["*"]:
                    return WeightOperation("+", [ConstantWeight(1)] + arg_weights)
                else:
                    if not arg_weights:
                        return ConstantWeight(0)
                    return WeightOperation('+', arg_weights)
        else:
            count = 0
            if isinstance(current_term.root, Function_Symbol):
                if current_term.root == function_symbol_registry["*"]:
                    count += 1
                for argument in current_term.arguments:
                    count += _count_multiplications_in_term(argument, static_analysis)
            return count
    
    def _find_all_exponentiation_nodes(current_term: Term) -> list[Term]:
        if isinstance(current_term.root, Function_Symbol) and current_term.root.name == "quote":
            return []
        exp_nodes = []
        if isinstance(current_term.root, Function_Symbol) and current_term.root == function_symbol_registry["^"]:
            exp_nodes.append(current_term)
        for argument in current_term.arguments:
            exp_nodes.extend(_find_all_exponentiation_nodes(argument))
        return exp_nodes

    def calculate_nested_exponentiation_score(current_term: Term, static_analysis: bool) -> int:
        if static_analysis:
            if isinstance(current_term.root, Variable):
                return VariableWeight(current_term.root.name)
            if isinstance(current_term.root, (Constant, QuoteInteger, QuoteReal)):
                return ConstantWeight(0)
            if isinstance(current_term.root, Function_Symbol):
                if current_term.root == function_symbol_registry["^"]:
                    base_weight = calculate_nested_exponentiation_score(current_term.arguments[0], static_analysis)
                    return WeightOperation("+", [ConstantWeight(1), base_weight])
                else:
                    arg_weights = [calculate_nested_exponentiation_score(arg, static_analysis) for arg in current_term.arguments]
                    max_weight = WeightOperation("max", arg_weights)
                    return max_weight
        else:
            if isinstance(current_term.root, Function_Symbol):
                if current_term.root == function_symbol_registry["^"]:
                    base_weight = calculate_nested_exponentiation_score(current_term.arguments[0], static_analysis)
                    return base_weight + 1
                else:
                    arg_weights = [calculate_nested_exponentiation_score(arg, static_analysis) for arg in current_term.arguments]
                    max_weight = max(arg_weights)
                    return max_weight
            elif isinstance(current_term.root, (Constant, QuoteInteger, QuoteReal)):
                return 0
            elif isinstance(current_term.root, Variable):
                raise ValueError("Should not have a variable type when static_analysis is False")
        raise NotImplementedError("Unexpectedly reached the end of calculate_nested_exponentiation_score. This indicates that the current term is not a variable, constant, quote term or function symbol.")

    def _get_exponent_value(term: Term, static_analysis: bool):
        if isinstance(term.root, QuoteInteger):
            return ConstantWeight(term.root.value) if static_analysis else term.root.value
        elif static_analysis and isinstance(term.root, IntegerVariable):
            return VariableWeight(term.root.name)
        elif static_analysis and isinstance(term.root, Variable):
             return VariableWeight(term.root.name)
        elif isinstance(term.root, Function_Symbol):
            if term.root.name == "quote":
                if static_analysis:
                    return quote_term_to_symbolic_weight(term.arguments[0])
                else:
                    return evaluate_quote_term_runtime(term.arguments[0])
            if term.root.name in ["+", "-", "*", "^"]:
                left = _get_exponent_value(term.arguments[0], static_analysis)
                right = _get_exponent_value(term.arguments[1], static_analysis)

                if static_analysis:
                    op_map = {"^": "**"} #needed because WeightOperation uses '**' for exponentiation, but the parser uses '^'
                    op = op_map.get(term.root.name, term.root.name)
                    return WeightOperation(op, [left, right])
                else:
                    if term.root.name == "+": 
                        return left + right
                    elif term.root.name == "-":
                        return left - right
                    elif term.root.name == "*":
                        return left*right
                    elif term.root.name == "^":
                        return left ** right
        else:
            raise ValueError(f"Unspported term structure in exponent position: {term=}")

    def _get_monomial_coefficient_weight(term: Term, static_analysis: bool):
        #Calculates the product of the absolute values of all quote terms in a multiplication chain.
        #Used for the Trig Argument Score in M3.
        
        # Case 1: It is a Quote Term
        if isinstance(term.root, Function_Symbol) and term.root.name == "quote":
            inner = term.arguments[0]
            if static_analysis:
                # For static analysis, we assume the variable/value represents the coefficient
                if isinstance(inner.root, (QuoteInteger, QuoteReal)):
                    return ConstantWeight(abs(int(inner.root.value)))
                # If it is a variable inside a quote [U], we get its symbolic weight
                # We assume the solver handles the 'abs' or that variables are positive
                return quote_term_to_symbolic_weight(inner) 
            else:
                # Runtime evaluation
                val = evaluate_quote_term_runtime(inner)
                return abs(val)

        # Case 2: Multiplication - Recurse
        if isinstance(term.root, Function_Symbol) and term.root.name == "*":
            left = _get_monomial_coefficient_weight(term.arguments[0], static_analysis)
            right = _get_monomial_coefficient_weight(term.arguments[1], static_analysis)
            
            if static_analysis:
                return WeightOperation("*", [left, right])
            else:
                return left * right

        # Case 3: Any other term (Variable, sin, etc.) counts as 1 (identity for multiplication)
        if static_analysis:
            return ConstantWeight(1)
        else:
            return 1    
    
    def calculate_exponential_base_score(current_term: Term, static_analysis: bool) -> int:
        if static_analysis:
            if isinstance(current_term.root, (Constant, QuoteInteger, QuoteReal)):
                return ConstantWeight(1)
            if isinstance(current_term.root, IntegerVariable):
                return ConstantWeight(1)
            if isinstance(current_term.root, Variable):
                return VariableWeight(current_term.root.name)
            if isinstance(current_term.root, Function_Symbol):
                if current_term.root == function_symbol_registry["quote"]:
                    return ConstantWeight(1)
                elif current_term.root == function_symbol_registry["*"]:
                    first_argument_weight = calculate_exponential_base_score(current_term.arguments[0], static_analysis)
                    second_argument_weight = calculate_exponential_base_score(current_term.arguments[1], static_analysis)
                    return WeightOperation("+", [first_argument_weight, second_argument_weight])
                elif current_term.root == function_symbol_registry["^"]:
                    base_score = calculate_exponential_base_score(current_term.arguments[0], static_analysis)
                    exponent_value = _get_exponent_value(current_term.arguments[1], static_analysis)
                    return WeightOperation("*", [base_score, exponent_value])
                elif current_term.root == function_symbol_registry["+"] or current_term.root == function_symbol_registry["-"]:
                    arg_weights = [calculate_exponential_base_score(arg, static_analysis) for arg in current_term.arguments]
                    max_weight = WeightOperation("max", arg_weights)
                    return max_weight
                else:
                    raise NotImplementedError(f"Exponential Base Score not implemented for function {current_term.root}")
                    
        else:
            if isinstance(current_term.root, (Constant, QuoteInteger, QuoteReal)):
                return 1
            if isinstance(current_term.root, Function_Symbol):
                if current_term.root == function_symbol_registry["*"]:
                    first_argument_weight = calculate_exponential_base_score(current_term.arguments[0], static_analysis)
                    second_argument_weight = calculate_exponential_base_score(current_term.arguments[1], static_analysis)
                    return first_argument_weight + second_argument_weight
                elif current_term.root == function_symbol_registry["^"]:
                    base_score = calculate_exponential_base_score(current_term.arguments[0], static_analysis)
                    exponent_value = _get_exponent_value(current_term.arguments[1], static_analysis)
                    return base_score * exponent_value
                else:
                    arg_weights = [calculate_exponential_base_score(arg, static_analysis) for arg in current_term.arguments]
                    max_weight = max(arg_weights)
                    return max_weight
                
    def _is_numeric_minus_one(t: Term) -> bool:
        if isinstance(t.root, QuoteInteger) and t.root.value == -1:
            return True
        if isinstance(t.root, QuoteReal) and t.root.value == -1.0:
            return True
        
        if isinstance(t.root, Function_Symbol) and t.root.name == "quote":
            inner = t.arguments[0]
            if isinstance(inner.root, QuoteInteger) and inner.root.value == -1:
                return True
            if isinstance(inner.root, QuoteReal) and inner.root.value == -1.0:
                return True
        return False

    def _count_minus_one_factors_in_multiplication_chain(arg: Term, static_analysis: bool):
        if isinstance(arg.root, Variable):
            if static_analysis:
                return VariableWeight(arg.root.name)
            else:
                raise ValueError("In runtime a variable was encountered. Variables should only be present in static analysis.")
        if _is_numeric_minus_one(arg):
            return ConstantWeight(1) if static_analysis else 1
            
            
        if isinstance(arg.root, Function_Symbol) and arg.root.name == "quote":
            return _count_minus_one_factors_in_multiplication_chain(arg.arguments[0], static_analysis)

        elif isinstance(arg.root, Function_Symbol) and arg.root.name in ["*", "/"]:
            left = _count_minus_one_factors_in_multiplication_chain(arg.arguments[0], static_analysis)
            right = _count_minus_one_factors_in_multiplication_chain(arg.arguments[1], static_analysis)
            
            if static_analysis:
                return WeightOperation("+", [left, right])
            else:
                return left + right

        else:
            return ConstantWeight(0) if static_analysis else 0

    def _count_trig_negative_factors(current_term: Term, static_analysis: bool):
        if isinstance(current_term.root, Function_Symbol) and current_term.root.name == "quote":
            return ConstantWeight(0) if static_analysis else 0
            
        if static_analysis:
            if isinstance(current_term.root, Variable):
                # The variable itself might be instantiated to a term containing sin(-1)...
                return VariableWeight(current_term.root.name)
            if isinstance(current_term.root, (Constant, QuoteInteger, QuoteReal)):
                return ConstantWeight(0)
            
            # Recursive step for all arguments
            arg_weights = [_count_trig_negative_factors(arg, static_analysis) for arg in current_term.arguments]
            
            # Check if this specific node is sin/cos
            current_node_score = None
            if isinstance(current_term.root, Function_Symbol) and current_term.root.name in ["sin", "cos"]:
                # Look inside the argument for -1 factors
                current_node_score = _count_minus_one_factors_in_multiplication_chain(current_term.arguments[0], static_analysis)
            
            # Combine: Sum(children) + (current_node_score if applicable)
            items_to_sum = arg_weights
            if current_node_score is not None:
                items_to_sum.append(current_node_score)
            
            if not items_to_sum:
                return ConstantWeight(0)
            return WeightOperation("+", items_to_sum)

        else:
            # Runtime logic
            total = 0
            # Check if this specific node is sin/cos
            if isinstance(current_term.root, Function_Symbol) and current_term.root.name in ["sin", "cos"]:
                total += _count_minus_one_factors_in_multiplication_chain(current_term.arguments[0], False)
            
            # Add recursive results
            for arg in current_term.arguments:
                total += _count_trig_negative_factors(arg, False)
            return total

    def _get_val_plus_one(t: Term, static_analysis: bool):
        """
        Calculates (Weight(t) + 1) for the context of monomials inside trig functions.
        Variables -> W(v) + 1
        Constants/Quotes -> 1
        Powers X^N -> (W(X) + 1)^N
        """
        if isinstance(t.root, (Constant, QuoteInteger, QuoteReal)):
            return ConstantWeight(1) if static_analysis else 1
        
        if isinstance(t.root, Function_Symbol) and t.root.name == 'quote':
            return ConstantWeight(1) if static_analysis else 1

        if isinstance(t.root, (Variable, IntegerVariable)):
            if static_analysis:
                return WeightOperation("+", [VariableWeight(t.root.name), ConstantWeight(1)])
            else:
                raise ValueError("Variables encountered in runtime evaluation of M0")

        if isinstance(t.root, Function_Symbol) and t.root.name == "^":
            # Handle X^[N] -> (W(X)+1)^N
            base = t.arguments[0]
            exponent = _get_exponent_value(t.arguments[1], static_analysis)
            
            base_val_plus_one = _get_val_plus_one(base, static_analysis)
            
            if static_analysis:
                return WeightOperation("**", [base_val_plus_one, exponent])
            else:
                return base_val_plus_one ** exponent

        # Fallback for other terms
        w = calculate_sine_power_outside(t, static_analysis)
        if static_analysis:
            return WeightOperation("+", [w, ConstantWeight(1)])
        else:
            return w + 1

    def _calculate_monomial_score(t: Term, static_analysis: bool):
        """
        Handles the logic: 
        "Gather all quote terms... coefficient. Score = 3 * abs(coeff) * product(term_weights + 1)"
        """
        # 1. Flatten Multiplication
        chain = _flatten_multiplication_chain(t)
        
        # 2. Separate Coefficients (Quotes) from Terms
        coeffs = []
        terms = []
        
        for factor in chain:
            if isinstance(factor.root, (QuoteInteger, QuoteReal)):
                val = factor.root.value
                coeffs.append(abs(int(val))) 
            elif isinstance(factor.root, Function_Symbol) and factor.root.name == 'quote':
                inner = factor.arguments[0]
                if static_analysis:
                    # --- FIX: Handle Absolute Value for Static Analysis ---
                    if isinstance(inner.root, (QuoteInteger, QuoteReal)):
                        # If it's a concrete number, take abs() immediately
                        val = abs(int(inner.root.value))
                        coeffs.append(ConstantWeight(val))
                    else:
                        # If it's a variable inside a quote, we get its weight.
                        # (Assuming variables represent positive magnitudes here, or Z3 handles it)
                        w = quote_term_to_symbolic_weight(inner)
                        coeffs.append(w)
                else:
                    # Runtime evaluation
                    val = evaluate_quote_term_runtime(inner)
                    coeffs.append(abs(int(val)))
            else:
                terms.append(factor)

        # 3. Calculate Coefficient (Product of quotes)
        if not coeffs:
            total_coeff = ConstantWeight(1) if static_analysis else 1
        else:
            if static_analysis:
                if len(coeffs) == 1:
                    total_coeff = coeffs[0] if isinstance(coeffs[0], SymbolicWeight) else ConstantWeight(coeffs[0])
                else:
                    sym_coeffs = [c if isinstance(c, SymbolicWeight) else ConstantWeight(c) for c in coeffs]
                    total_coeff = WeightOperation("*", sym_coeffs)
            else:
                total_coeff = 1
                for c in coeffs:
                    total_coeff *= c

        # 4. Calculate Product of (Terms + 1)
        if not terms:
            term_product = ConstantWeight(1) if static_analysis else 1
        else:
            term_weights = [_get_val_plus_one(term, static_analysis) for term in terms]
            if static_analysis:
                if len(term_weights) == 1:
                    term_product = term_weights[0]
                else:
                    term_product = WeightOperation("*", term_weights)
            else:
                term_product = 1
                for w in term_weights:
                    term_product *= w

        # 5. Final Score: 3 * Coeff * TermProduct
        if static_analysis:
            return WeightOperation("*", [ConstantWeight(3), total_coeff, term_product])
        else:
            return 3 * total_coeff * term_product

    def calculate_sine_power_inside(t: Term, static_analysis: bool):
        # 1. Handle Addition (Sum of arguments + 3 per addition)
        if isinstance(t.root, Function_Symbol) and t.root.name in ["+", "-"]:
            args = t.arguments
            arg_scores = [calculate_sine_power_inside(arg, static_analysis) for arg in args]
            
            if static_analysis:
                sum_scores = WeightOperation("+", arg_scores)
                return WeightOperation("+", [ConstantWeight(3), sum_scores])
            else:
                return 3 + sum(arg_scores)

        # 2. Handle Constants (Base case: 0)
        if isinstance(t.root, (Constant, QuoteInteger, QuoteReal)):
            return ConstantWeight(0) if static_analysis else 0
        if isinstance(t.root, Function_Symbol) and t.root.name == 'quote':
            return ConstantWeight(0) if static_analysis else 0

        # 3. Handle Monomials (*, ^, or single Variable)
        return _calculate_monomial_score(t, static_analysis)

    def calculate_sine_power_outside(t: Term, static_analysis: bool):
        # 1. Constants -> 0
        if isinstance(t.root, (Constant, QuoteInteger, QuoteReal)):
            return ConstantWeight(0) if static_analysis else 0
        if isinstance(t.root, Function_Symbol) and t.root.name == 'quote':
            return ConstantWeight(0) if static_analysis else 0

        # 2. Variables -> Weight
        if isinstance(t.root, (Variable, IntegerVariable)):
            if static_analysis:
                return VariableWeight(t.root.name)
            else:
                return 0 

        if isinstance(t.root, Function_Symbol):
            # 3. + or - -> Max(args)
            if t.root.name in ["+", "-"]:
                args = [calculate_sine_power_outside(arg, static_analysis) for arg in t.arguments]
                if static_analysis:
                    return WeightOperation("max", args)
                else:
                    return max(args)

            # 4. * -> Sum(args)
            if t.root.name == "*":
                args = [calculate_sine_power_outside(arg, static_analysis) for arg in t.arguments]
                if static_analysis:
                    return WeightOperation("+", args)
                else:
                    return sum(args)

            # 5. ^[N] -> arg1 * N
            if t.root.name == "^":
                base_score = calculate_sine_power_outside(t.arguments[0], static_analysis)
                exponent = _get_exponent_value(t.arguments[1], static_analysis)
                
                if static_analysis:
                    return WeightOperation("*", [base_score, exponent])
                else:
                    return base_score * exponent

            # 6. Sin -> 1 + Inside
            if t.root.name == "sin":
                inside_score = calculate_sine_power_inside(t.arguments[0], static_analysis)
                if static_analysis:
                    return WeightOperation("+", [ConstantWeight(1), inside_score])
                else:
                    return 1 + inside_score

            # 7. Cos -> 0 + Inside
            if t.root.name == "cos":
                inside_score = calculate_sine_power_inside(t.arguments[0], static_analysis)
                return inside_score

        return ConstantWeight(0) if static_analysis else 0
    
        
    all_monomials = _find_multiplication_chains_recursive(term)
    all_additions = _find_all_addition_nodes(term)
    
    ### M6 Count the number of quote terms
    if metric_index == number_of_implemented_metrics-1:
        count = 0
        for subterm in term.subterms:
            if isinstance(subterm.root, Function_Symbol):
                has_quote_arg = False
                for arg in subterm.arguments:
                    #is_literal = isinstance(arg.root, (QuoteInteger, QuoteReal))
                    is_quote_func = (isinstance(arg.root, Function_Symbol) and arg.root.name == 'quote')
                    if is_quote_func:
                        has_quote_arg = True
                if has_quote_arg:
                    count += 1
        if static_analysis:
            return [ConstantWeight(count)]
        else:
            return [count]
    
    #M10 - addition associativity
    #For addition associativity
    elif metric_index == number_of_implemented_metrics-2:
        associativity_vector = []

        for addition_node in all_additions:
            lhs_argument = addition_node.arguments[0]
            count = _count_additions_in_term(lhs_argument, static_analysis)
            associativity_vector.append(count)

        if not static_analysis:
            associativity_vector.append(-1)
            associativity_vector.sort(reverse=True)
        else:
            associativity_vector.append(ConstantWeight(-1))
        return associativity_vector


    ### M9 Addition Commutativity Metric Starts Here
    elif metric_index == number_of_implemented_metrics-3:        
        all_summands = _find_addition_chains_recursive(term)
        addition_commutativity_scores = []

        for chain in all_summands:
            score = calculate_max_block_sort_moves(chain, function_symbol_registry, static_analysis, constant_order, variable_order, memo_cache)
            addition_commutativity_scores.append(score)

        if static_analysis:
            addition_commutativity_vector = [ConstantWeight(s) for s in addition_commutativity_scores]
            addition_commutativity_vector.append(ConstantWeight(-1))
        else:
            addition_commutativity_vector = addition_commutativity_scores
            addition_commutativity_vector.append(-1)
        return addition_commutativity_vector
    


    ### M8
    elif metric_index == number_of_implemented_metrics-4:
        #M8 Multiplication Commutativity Starts here
        all_multiplications = _find_all_multiplication_nodes(term)
        mult_associativity_vector = []

        for mult_node in all_multiplications:
            lhs_argument = mult_node.arguments[0]
            count = _count_multiplications_in_term(lhs_argument, static_analysis)
            mult_associativity_vector.append(count)

        if not static_analysis:
            mult_associativity_vector.append(-1)
            mult_associativity_vector.sort(reverse=True)
        else:
            mult_associativity_vector.append(ConstantWeight(-1))
        return mult_associativity_vector



    
    #M7 Multiplicaiton commutativity starts here
    elif metric_index == number_of_implemented_metrics-5:
        multiplication_commutativity_scores = []

        for monomial in all_monomials:
            score = calculate_max_block_sort_moves(monomial, function_symbol_registry, static_analysis, constant_order, variable_order, memo_cache)
            multiplication_commutativity_scores.append(score)

        multiplication_commutativity_scores.sort(reverse=True)

        if static_analysis:
            multiplication_commutativity_vector = [ConstantWeight(s) for s in multiplication_commutativity_scores]
            multiplication_commutativity_vector.append(ConstantWeight(-1))
        else:
            multiplication_commutativity_vector = multiplication_commutativity_scores 
            multiplication_commutativity_vector.append(-1)

        
        
        return multiplication_commutativity_vector


    # MT1 / M6.5: total number of -1 factors inside sin/cos arguments
    if metric_index == number_of_implemented_metrics - 6:
        count = _count_trig_negative_factors(term, static_analysis)
        return [count]

    #M3
    elif metric_index == number_of_implemented_metrics-7:
        # M3: Distributivity Scores
        # Part 1: Trig Argument Addition Scores (Count additions in sin/cos args * 2)
        trig_nodes = _find_all_trig_nodes(term)
        trig_scores = []
        
        for t_node in trig_nodes:
            arg = t_node.arguments[0]

            # 1. Calculate the sum of weights of the monomials (coefficients)
            monomials = _flatten_addition_chain(arg)
            monomial_weights = []
            # Calculate additions in the argument (index 0)
            for m in monomials:
                w = _get_monomial_coefficient_weight(m, static_analysis)
                monomial_weights.append(w)
            
            if static_analysis:
                if not monomial_weights:
                    sum_monomials = ConstantWeight(0)
                elif len(monomial_weights) == 1:
                    sum_monomials = monomial_weights[0]
                else:
                    sum_monomials = WeightOperation("+", monomial_weights)
            else:
                sum_monomials = sum(monomial_weights)

            # 2. Count the addition symbols (structural complexity)
            plus_count = _count_additions_in_term(arg, static_analysis)

            # 3. Combine: (Sum_Monomials + Plus_Count) * 2
            if static_analysis:
                total_inner = WeightOperation("+", [sum_monomials, plus_count])
                final_trig_score = WeightOperation("*", [total_inner, ConstantWeight(2)])
            else:
                final_trig_score = (sum_monomials + plus_count) * 2
            
            trig_scores.append(final_trig_score)

        # --- Part 2: Monomial Addition Scores (Original M3) ---
        monomial_scores = []
        all_monomials_for_metric = _find_monomials_for_addition_score(term)

        for monomial in all_monomials_for_metric:
            if not static_analysis:
                score = 0
                for t in monomial:
                    score += _count_additions_in_term(t, False) 
                monomial_scores.append(score)
            else:
                all_counts = [_count_additions_in_term(t, True) for t in monomial]
                if not all_counts:
                    score = ConstantWeight(0)
                elif len(all_counts) == 1:
                    score = all_counts[0]
                else:
                    score = WeightOperation("+", all_counts)
                monomial_scores.append(score)

        # Combine vectors: Trig scores first, then monomial scores
        combined_vector = trig_scores + monomial_scores

        if not static_analysis:
            combined_vector.sort(reverse=True)
            combined_vector.append(-1)
        else:
            combined_vector.append(ConstantWeight(-1))
            
        return combined_vector
        

    #M2
    elif metric_index == nested_exponentiation_score_metric:
        all_exponentiations = _find_all_exponentiation_nodes(term)
        nested_exponentiation_score_vector = []
        if not static_analysis:
            for exp_node in all_exponentiations:
                nested_exponentiation_score_vector.append(calculate_nested_exponentiation_score(exp_node, static_analysis))
            nested_exponentiation_score_vector.sort(reverse=True)
            nested_exponentiation_score_vector.append(-1)
            return nested_exponentiation_score_vector
        
        else:
            for exp_node in all_exponentiations:
                nested_exponentiation_score_vector.append(calculate_nested_exponentiation_score(exp_node, static_analysis))
            #Rather than dealing with ordering here, it is dealt with by Z3 later
            nested_exponentiation_score_vector.append(ConstantWeight(-1))
            return nested_exponentiation_score_vector

    #M1
    
    elif metric_index == exponential_base_score_metric:
        all_exponentiations = _find_all_exponentiation_nodes(term)        
        exponential_base_score_vector = []
        if not static_analysis:
            for exponentiation in all_exponentiations:
                exponential_base_score_vector.append(calculate_exponential_base_score(exponentiation, static_analysis))
            exponential_base_score_vector.sort(reverse=True)
            exponential_base_score_vector.append(-1)
            #Rather than dealing with ordering here, it is dealt with by Z3 later
            return exponential_base_score_vector
        else:
            for exponentiation in all_exponentiations:
                exponential_base_score_vector.append(calculate_exponential_base_score(exponentiation, static_analysis))
            exponential_base_score_vector.append(ConstantWeight(-1))
            return exponential_base_score_vector

    #M0
    elif metric_index == 0:
        result = calculate_sine_power_outside(term, static_analysis)
        if static_analysis:
            return [result, ConstantWeight(-1)]
        else:
            return [result, -1]
    
    else:    
        raise IndexError(f"Only {number_of_implemented_metrics} metrics implemented, but entry number {metric_index} was called.")




    
def entry_wise_prove_greater(lhs_term, rhs_term, skolem_variables, variable_order, function_symbol_registry, constant_order, memo_cache, substitution, extra_constraints=None):
    if extra_constraints is None:
        extra_constraints = []
    metric_index = 0
    while True:

    
        try:
            # Step 1: Compute the weight vector for the CURRENT metric only.
            #print(f"{metric_index=}")
            lhs_entry = compute_single_metric(lhs_term, metric_index, static_analysis=True, variable_order=variable_order, memo_cache=memo_cache, function_symbol_registry = function_symbol_registry, constant_order = constant_order, extra_constraints=extra_constraints)
            rhs_entry = compute_single_metric(rhs_term, metric_index, static_analysis=True, variable_order=variable_order, memo_cache=memo_cache, function_symbol_registry = function_symbol_registry, constant_order = constant_order, extra_constraints=extra_constraints)
            #print(f"{lhs_entry=}")
            #print(f"{rhs_entry=}")
            
            # Ensure entries are lists for the comparison function
            lhs_vec = lhs_entry if isinstance(lhs_entry, list) else [lhs_entry]
            rhs_vec = rhs_entry if isinstance(rhs_entry, list) else [rhs_entry]

            # Optimization: Remove identical symbolic terms present in both vectors.
            temp_rhs = list(rhs_vec) 
            final_lhs = []

            for item in lhs_vec:
                if item in temp_rhs:
                    temp_rhs.remove(item)
                else:
                    final_lhs.append(item)

            final_rhs = temp_rhs

            lhs_vec = final_lhs
            rhs_vec = final_rhs

            #print(f"Vectors to give to Z3: {lhs_vec=}")
            #print(f"Vectors to give to Z3: {rhs_vec=}")
            # Step 2: Set up a Z3 solver for this specific metric's comparison.
            solver = z3.Solver()
            solver.set("timeout", 5000)
            z3_variables_for_this_metric = {var.name: z3.Int(f"W_{var.name}_metric{metric_index}") for var in skolem_variables}

            #print(f"{extra_constraints=}")
            for constraint in extra_constraints:
                # 1. Handle New 4-Tuple Constraints (Metric-Specific SymbolicWeights)
                if len(constraint) == 4:
                    c_metric_idx, c_lhs, c_rel, c_rhs = constraint
                    # Only apply if it matches the current metric we are analyzing
                    if c_metric_idx == metric_index:
                        try:
                            # Convert SymbolicWeights to Z3 expressions using the current metric's variables
                            z3_lhs = symbolic_weight_to_z3(c_lhs, z3_variables_for_this_metric)
                            z3_rhs = symbolic_weight_to_z3(c_rhs, z3_variables_for_this_metric)
                            
                            if c_rel == ">": 
                                #print(f"Z3 is adding the following constraint: {z3_lhs > z3_rhs}")
                                solver.add(z3_lhs > z3_rhs)
                            elif c_rel == "<": solver.add(z3_lhs < z3_rhs)
                            elif c_rel == "==": solver.add(z3_lhs == z3_rhs)
                            elif c_rel == ">=": solver.add(z3_lhs >= z3_rhs)
                            elif c_rel == "<=": solver.add(z3_lhs <= z3_rhs)
                        except Exception:
                            # If conversion fails (e.g. variable not in scope), ignore this constraint
                            pass
                    continue

                # 2. Handle Legacy 3-Tuple Constraints (Term/Variable Ordering)
                if len(constraint) == 3:
                    item1, relation, item2 = constraint
                    
                    def get_z3_val(item):
                        if isinstance(item, Variable):
                            return z3_variables_for_this_metric.get(item.name)
                        elif isinstance(item, Term) and isinstance(item.root, Function_Symbol) and item.root.name == 'quote':
                            return get_z3_val(item.arguments[0])
                        elif isinstance(item, (QuoteInteger, QuoteReal)):
                            return z3.IntVal(constant_order.get(item.value, 0))
                        elif isinstance(item, Constant):
                            return z3.IntVal(constant_order.get(item.name, 0))
                        return None # Return None instead of raising error to be safe

                    weight1 = get_z3_val(item1)
                    weight2 = get_z3_val(item2)

                    if weight1 is not None and weight2 is not None:
                        if relation == ">":
                            solver.add(weight1 > weight2)
                        elif relation == "==":
                            solver.add(weight1 == weight2)
            
            #Helper function to callect all variables used in the calculation of weights
            def collect_vars(weight):
                if isinstance(weight, VariableWeight): 
                    return {weight.name}
                elif isinstance(weight, WeightOperation):
                    if not weight.args:
                        return set()
                    return set().union(*(collect_vars(arg) for arg in weight.args))
                return set()

            #Adding missing variables to existing set
            all_weight_vars = set().union(*(collect_vars(w) for w in lhs_vec + rhs_vec))
            for name in all_weight_vars:
                if name not in z3_variables_for_this_metric:
                    z3_variables_for_this_metric[name] = z3.Int(f"W_{name}_metric{metric_index}")

            #Apply constraints to all variables (Skolems + IntVariables)
            for name, z3_var in z3_variables_for_this_metric.items():
                if name in integer_variable_registry:
                    solver.add(z3_var >= 1)
                elif metric_index == exponential_base_score_metric: 
                    solver.add(z3_var >=1)
                else:
                    solver.add(z3_var >=0)
                
            
            # Add ordering constraints for skolem variables
            def get_precedence(variable):
                return variable_order.get(variable, 0)
            sorted_skolem_variables = sorted(skolem_variables, key=get_precedence, reverse=True)
            for i in range(len(sorted_skolem_variables)-1):
                var_high = sorted_skolem_variables[i]
                var_low = sorted_skolem_variables[i+1]
                solver.add(z3_variables_for_this_metric[var_high.name] >= z3_variables_for_this_metric[var_low.name])
            if sorted_skolem_variables:
                last_var = sorted_skolem_variables[-1]
                if metric_index == nested_exponentiation_score_metric:
                    solver.add(z3_variables_for_this_metric[last_var.name] >= 1)
                else:
                    solver.add(z3_variables_for_this_metric[last_var.name] >= 0)

            # Step 3: Check if LHS > RHS for this metric.
            is_greater_expr = build_z3_lex_comparison_expression(lhs_vec, rhs_vec, z3_variables_for_this_metric, '>', unordered_vector=True)
            solver.push()
            solver.add(z3.Not(is_greater_expr))
            if solver.check() == z3.unsat:
                solver.pop()

                return True
            solver.pop()

            # Step 4: If not strictly greater, check if they are equal.
            is_equal_expr = build_z3_lex_comparison_expression(lhs_vec, rhs_vec, z3_variables_for_this_metric, '==', unordered_vector=True)
            is_gte_expr = z3.Or(is_greater_expr, is_equal_expr)
            solver.push()
            solver.add(z3.Not(is_gte_expr))
            if solver.check() == z3.unsat:
                solver.pop()

                metric_index += 1
                continue
            solver.pop()
            
            # Step 5: If it's not > and not ==, it must be < or indeterminate.
            # In either case, we cannot prove termination. We are done.
            solver.add(z3.Not(is_greater_expr))
            solver.add(z3.Not(is_gte_expr))
            if solver.check() == z3.sat:
                print(f"    Counter-example Model: {solver.model()}")
            return False

        except IndexError:
            # We ran out of metrics, and they were all ties.
            # Fall back to the final lexicographical tie-breaker.
            return compare_terms_lexicographically(lhs_term, rhs_term, function_symbol_registry, constant_order, static_analysis=True, variable_order=variable_order, extra_constraints=extra_constraints)
        
        

def get_weight(term: Term, function_symbol_registry, constant_order: Dict[str, int], variable_order: Dict[str, int] = {}, static_analysis: bool = False, memo_cache: dict = None, extra_constraints: list = []) -> list:    
    if memo_cache is None:
        memo_cache = {}
    
    vector = []
    metric_index = 0
    while True:
        try:
            entry = compute_single_metric(term, metric_index, static_analysis, variable_order, memo_cache, function_symbol_registry, constant_order, extra_constraints)
            vector.append(entry)
            metric_index += 1
        except IndexError:
            metric_index += 1
            #No more metrics defined
            break
    return vector





                                          
### Part of AWPO
def evaluate_symbolic_weight(weight: SymbolicWeight) -> int:
    if isinstance(weight, ConstantWeight):
        return weight.value
    if isinstance(weight, VariableWeight):
        raise TypeError(f"Cannot evaluate weights with variables. Variable: {weight.name} found.")

    if isinstance(weight, WeightOperation):
        eval_args = [evaluate_symbolic_weight(arg) for arg in weight.args]
        if weight.op == "+":
            return sum(eval_args)
        if weight.op == "-":
            if len(eval_args) != 2:
                raise ValueError("Subtraction terms must have exactly two arguments")
            return eval_args[0] - eval_args[1]
        if weight.op == "*":
            result = 1
            for arg in eval_args:
                result*= arg
            return result
        if weight.op == '**':
            if len(eval_args) != 2:
                raise ValueError("Exponentiation terms must have two arguments")
            return eval_args[0] ** eval_args[1]
        if weight.op == 'max':
            if not eval_args:
                raise ValueError("max() operator requires at least one argument.")
            return max(eval_args)
        if weight.op == 'sin':
            return math.sin(eval_args[0])
        if weight.op == 'cos':
            return math.cos(eval_args[0])
        
        raise NotImplementedError(f"Evaluation for operator '{weight.op}' is not implemented.")
    
    raise TypeError(f"Unknown SymbolicWeight type: {type(weight)}")

def symbolic_weight_to_z3(weight: SymbolicWeight, z3_vars: dict) -> z3.ArithRef:
    #Converts a Symbolic Weight into a Z3 expression
    if isinstance(weight, ConstantWeight):
        return z3.IntVal(weight.value)

    if isinstance(weight, VariableWeight):
        if weight.name not in z3_vars:
            z3_vars[weight.name] = z3.Int(f"W_{weight.name}")
        return z3_vars[weight.name]

    if isinstance(weight, WeightOperation):
        z3_args = [symbolic_weight_to_z3(arg, z3_vars) for arg in weight.args]
        if weight.op == '+':
            return z3.Sum(z3_args)
        if weight.op == '-':
            if len(z3_args) != 2:
                raise ValueError("Subtraction operation must have exactly two arguments.")
            return z3_args[0] - z3_args[1]
        if weight.op == '*':
            return z3.Product(z3_args)
        if weight.op == '**':
            if len(z3_args) != 2:
                raise ValueError("Exponentiation operation must have exactly two arguments.")
            return z3_args[0] ** z3_args[1]

        if weight.op == 'max':
            if not z3_args:
                raise ValueError("max() oeprator requires at least one argument.")
            if len(z3_args) ==1:
                return z3_args[0]
            current_max = z3_args[0]
            for i in range(1, len(z3_args)):
                arg = z3_args[i]
                current_max = z3.If(arg > current_max, arg, current_max)
            return current_max

        if weight.op == 'sin':
            z3_sin = z3.Function('sin', z3.IntSort(), z3.IntSort())
            return z3_sin(z3_args[0])
            
        if weight.op == 'cos':
            z3_cos = z3.Function('cos', z3.IntSort(), z3.IntSort())
            return z3_cos(z3_args[0])
            
        raise NotImplementedError(f"Z3 translation for operator '{weight.op}' is not implemented")
    raise TypeError(f"Cannot convert type {type(weight)} to Z3. Expected SymbolicWeight (Atomic), but got {weight}.")

def check_constraints_satisfiable(extra_constraints, variable_order) -> bool:
    solver = z3.Solver()
    z3_vars = {}

    # 1. Collect Variables from BOTH types of constraints
    def collect_vars(obj):
        if isinstance(obj, (list, tuple)):
            return set().union(*(collect_vars(x) for x in obj))
        if isinstance(obj, VariableWeight): return {obj.name}
        if isinstance(obj, WeightOperation):
            if not obj.args: return set()
            return set.union(*(collect_vars(a) for a in obj.args))
        # Handle Terms/Variables from Length-3 constraints
        if isinstance(obj, (Variable, Constant)): return {obj.name}
        if isinstance(obj, Term) and isinstance(obj.root, (Variable, Constant)): return {obj.root.name}
        return set()

    all_vars = set()
    for constraint in extra_constraints:
        # Unpack based on length
        if len(constraint) == 4:
            _, lhs, rel, rhs = constraint
        elif len(constraint) == 3:
            lhs, rel, rhs = constraint
        else:
            continue
        all_vars.update(collect_vars(lhs))
        all_vars.update(collect_vars(rhs))

    # Add variables from the order dict
    for v in variable_order.keys():
        if hasattr(v, 'name'): all_vars.add(v.name)
        elif isinstance(v, Term) and hasattr(v.root, 'name'): all_vars.add(v.root.name)

    # Initialize Z3 vars
    for name in all_vars:
        z3_vars[name] = z3.Int(name)
        solver.add(z3_vars[name] >= 1)

    # 2. Add Base Variable Ordering (The "Background" Knowledge)
    # We sort the variables based on the passed 'variable_order'
    vars_in_order = [k for k in variable_order.keys() if hasattr(k, 'name') or (isinstance(k, Term) and hasattr(k.root, 'name'))]
    sorted_vars = sorted(vars_in_order, key=lambda v: variable_order[v], reverse=True)
    
    for i in range(len(sorted_vars) - 1):
        high = sorted_vars[i]
        low = sorted_vars[i+1]
        h_name = high.name if hasattr(high, 'name') else high.root.name
        l_name = low.name if hasattr(low, 'name') else low.root.name
        
        if h_name in z3_vars and l_name in z3_vars:
            solver.add(z3_vars[h_name] >= z3_vars[l_name])

    # 3. Apply Extra Constraints (The "Specific" Assumptions)
    for constraint in extra_constraints:
        if len(constraint) == 4:
            _, lhs, rel, rhs = constraint
            # Length-4 are Weights: Use symbolic_weight_to_z3
            if isinstance(lhs, list):
                if not isinstance(rhs, list): continue 
                
                if rel == ">":
                    solver.add(build_z3_lex_comparison_expression(lhs, rhs, z3_vars, '>'))
                elif rel == "<":
                    solver.add(build_z3_lex_comparison_expression(rhs, lhs, z3_vars, '>'))
                elif rel == "==":
                    solver.add(build_z3_lex_comparison_expression(lhs, rhs, z3_vars, '=='))
                elif rel == ">=":
                    gt = build_z3_lex_comparison_expression(lhs, rhs, z3_vars, '>')
                    eq = build_z3_lex_comparison_expression(lhs, rhs, z3_vars, '==')
                    solver.add(z3.Or(gt, eq))
                elif rel == "<=":
                    gt = build_z3_lex_comparison_expression(rhs, lhs, z3_vars, '>')
                    eq = build_z3_lex_comparison_expression(lhs, rhs, z3_vars, '==')
                    solver.add(z3.Or(gt, eq))
                continue
            try:
                z3_lhs = symbolic_weight_to_z3(lhs, z3_vars)
                z3_rhs = symbolic_weight_to_z3(rhs, z3_vars)
            except Exception: continue # Skip if conversion fails
        elif len(constraint) == 3:
            lhs, rel, rhs = constraint
            # Length-3 are Terms: Look up directly
            l_name = lhs.name if hasattr(lhs, 'name') else (lhs.root.name if isinstance(lhs, Term) else None)
            r_name = rhs.name if hasattr(rhs, 'name') else (rhs.root.name if isinstance(rhs, Term) else None)
            
            if l_name and l_name in z3_vars: z3_lhs = z3_vars[l_name]
            else: continue
            
            if r_name and r_name in z3_vars: z3_rhs = z3_vars[r_name]
            else: continue
        else:
            continue

        # Apply the relation
        if rel == ">": 
            solver.add(z3_lhs > z3_rhs)
        elif rel == "<": 
            solver.add(z3_lhs < z3_rhs)
        elif rel == ">=": 
            solver.add(z3_lhs >= z3_rhs)
        elif rel == "<=": 
            solver.add(z3_lhs <= z3_rhs)
        elif rel == "==": 
            solver.add(z3_lhs == z3_rhs)
        elif rel == "!=": 
            solver.add(z3_lhs != z3_rhs)

    return solver.check() != z3.unsat

def prove_term_equivalence(t1: Term, t2: Term, extra_constraints, variable_order) -> bool:
    #proves if t1==t2 is mathematically necessary given the constraints
    solver = z3.Solver()
    solver.set("timeout", 20000) 
    z3_vars = {}

    def collect_vars(obj):
        if isinstance(obj, VariableWeight): 
            return {obj.name}
        if isinstance(obj, WeightOperation):
            if not obj.args: return set()
            return set.union(*(collect_vars(a) for a in obj.args))
        if isinstance(obj, (Variable, Constant)): 
            return {obj.name}
        if isinstance(obj, Term) and isinstance(obj.root, (Variable, Constant)): 
            return {obj.root.name}
        return set()
        
    all_vars = set()
    for constraint in extra_constraints:
        if len(constraint) ==4:
            _, lhs, rel, rhs = constraint
        elif len(constraint) == 3:
            lhs, rel, rhs = constraint
        else:
            continue
        all_vars.update(collect_vars(lhs))
        all_vars.update(collect_vars(rhs))

        for v in variable_order.keys():
            if hasattr(v, 'name'):
                all_vars.add(v.name)
            elif isinstance(v, Term) and hasattr(v.root, 'name'):
                all_vars.add(v.root.name)

        for name in all_vars:
            z3_vars[name] = z3.Int(name)
            solver.add(z3_vars[name] >= 1)

        vars_in_order = [k for k in variable_order.keys() if hasattr(k, 'name') or isinstance(k, Term) and hasattr(k.root, 'name')]
        sorted_vars = sorted(vars_in_order, key=lambda v: variable_order[v], reverse=True)
        for i in range(len(sorted_vars)-1):
            h_name = sorted_vars[i].name if hasattr(sorted_vars[i], 'name') else sorted_vars[i].root.name
            l_name = sorted_vars[i+1].name if hasattr(sorted_vars[i+1], 'name') else sorted_vars[i+1].root.name
            if h_name in z3_vars and l_name in z3_vars:
                solver.add(z3_vars[h_name] >= z3_vars[l_name])
        
        #Add extra constraints
        for constraint in extra_constraints:
            if len(constraint) == 4:
                _, lhs, rel, rhs = constraint
                try:
                    z3_lhs = symbolic_weight_to_z3(lhs, z3_vars)
                    z3_rhs = symbolic_weight_to_z3(rhs, z3_vars)
                except: 
                    continue
            elif len(constraint) == 3:
                lhs, rel, rhs = constraint
                l_name = lhs.name if hasattr(lhs, 'name') else (lhs.root.name if isinstance(lhs, Term) else None)
                r_name = rhs.name if hasattr(rhs, 'name') else (rhs.root.name if isinstance(rhs, Term) else None)
                if l_name in z3_vars and r_name in z3_vars:
                    z3_lhs, z3_rhs = z3_vars[l_name], z3_vars[r_name]
                else: 
                    continue
            else: 
                continue
            if rel == ">": 
                solver.add(z3_lhs > z3_rhs)
            elif rel == "<": 
                solver.add(z3_lhs < z3_rhs)
            elif rel == ">=": 
                solver.add(z3_lhs >= z3_rhs)
            elif rel == "<=": 
                solver.add(z3_lhs <= z3_rhs)
            elif rel == "==": 
                solver.add(z3_lhs == z3_rhs)

    z3_sin = z3.Function('sin', z3.IntSort(), z3.IntSort())
    z3_cos = z3.Function('cos', z3.IntSort(), z3.IntSort())
    solver.add(z3_sin(0) == 0)
    solver.add(z3_cos(0) == 1)
    
    def term_to_z3_arithmetic(t):
        if isinstance(t.root, (QuoteInteger, QuoteReal)):
            return z3.IntVal(int(t.root.value))
        if isinstance(t.root, (Variable, Constant)):
            return z3_vars.get(t.root.name)
        if isinstance(t.root, Function_Symbol):
            if t.root.name == "quote":
                return term_to_z3_arithmetic(t.arguments[0])
            
            args = [term_to_z3_arithmetic(arg) for arg in t.arguments]
            if any(a is None for a in args): 
                return None
            
            if t.root.name == "+": 
                return z3.Sum(args)
            if t.root.name == "*": 
                return z3.Product(args)
            if t.root.name == "-": 
                return args[0] - args[1] if len(args) == 2 else -args[0]
            if t.root.name == "^": 
                base = args[0]
                exponent = args[1]
                
                return z3.If(exponent == 0, z3.IntVal(1),
                             z3.If(exponent == 1, base,
                                   z3.If(base == 0, z3.IntVal(0),
                                         z3.If(base == 1, z3.IntVal(1),
                                               base ** exponent))))
            if t.root.name == "sin":
                return z3_sin(args[0])
            if t.root.name == "cos":
                return z3_cos(args[0])
                
        raise ValueError(f"The following term was not able to be converted into a Z3 constraint {t}")
    
    trig_arguments = set()
    def collect_trig_args(t: Term):
        if isinstance(t.root, Function_Symbol):
            if t.root.name in ['sin', 'cos']:
                # Found a trig function, save its argument
                trig_arguments.add(t.arguments[0])
            
            # Recurse
            for arg in t.arguments:
                collect_trig_args(arg)

    collect_trig_args(t1)
    collect_trig_args(t2)

    for arg_term in trig_arguments:
        try:
            z_arg = term_to_z3_arithmetic(arg_term)
            if z_arg is not None:
                # Add the Pythagorean identity specifically for this variable
                solver.add( (z3_sin(z_arg) * z3_sin(z_arg)) + (z3_cos(z_arg) * z3_cos(z_arg)) == 1 )
                # print(f"  [Z3] Injected trig identity for {arg_term}")
                solver.add(z3_sin(-z_arg) == -z3_sin(z_arg)) # sin(-x) = -sin(x)
                solver.add(z3_cos(-z_arg) == z3_cos(z_arg))  # cos(-x) = cos(x)
        except Exception:
            pass
            
    try:
        #print("  [Z3-EQUIV] Converting terms to Z3...")
        z1 = term_to_z3_arithmetic(t1)
        z2 = term_to_z3_arithmetic(t2)
        
                
        solver.add(z1 != z2)
        result = solver.check()
        
        return result == z3.unsat
        
    except Exception as e:
        #print(f"  [Z3-EQUIV] Error during Z3 setup: {e}")
        raise e
    

def compare_terms_lexicographically(Term1, Term2, function_symbol_registry, constant_order, static_analysis=False, variable_order={}, extra_constraints=[]):
    #print("entering compare_terms_lexicographically")
    Term1_Argument_List = Term1.arguments
    if isinstance(Term1.root, Function_Symbol):
        Term1_Function_Symbol = Term1.root
        if Term1_Function_Symbol.name == 'quote':
            Term1_Precedence = -1
        else:
            Term1_Precedence = function_symbol_registry[Term1_Function_Symbol.name].lexicographic_precedence_level
        
    elif isinstance(Term1.root, Constant):
        Term1_Precedence = 0
    elif isinstance(Term1.root, (QuoteInteger, QuoteReal)):
        Term1_Precedence = -1
    elif isinstance(Term1.root, Variable):
        if not static_analysis:
            raise TypeError(f"During runtime variables such as '{Term1.root}' should not be encountered, only ground terms.")
    else:
        raise ValueError(f"Term1: {Term1}, has unexpected structure. ")
    
    #Get precedence for Term 2
    Term2_Argument_List = Term2.arguments
    if isinstance(Term2.root, Function_Symbol):
        Term2_Function_Symbol = Term2.root
        if Term2_Function_Symbol.name == 'quote':
            Term2_Precedence = -1
        else:
            Term2_Precedence = function_symbol_registry[Term2_Function_Symbol.name].lexicographic_precedence_level
        
    elif isinstance(Term2.root, Constant):
        Term2_Precedence = 0
    elif isinstance(Term2.root, (QuoteInteger, QuoteReal)):
        Term2_Precedence = -1
    elif isinstance(Term2.root, Variable):
        if not static_analysis:
            raise TypeError(f"During runtime variables such as '{Term2.root}' should not be encountered, only ground terms.")
        #Term2_Precedence = 0.5 ### Work will need to be done to fix this, we should iterate over all possible variable precedences: we could fall anywhere in the function symbol registry. May need to do a case split.
    else:
        raise ValueError(f"Term2: {Term2}, has an unexpected structure.")

        
    #If Both Constants 
    if isinstance(Term1.root, Constant) and isinstance(Term2.root, Constant):
        if Term1_Precedence == 0 and Term2_Precedence == 0:
            if constant_order[str(Term1)] > constant_order[str(Term2)]:
                return True
            else:
                return False

    #If only one quote term
    t1_is_quote = isinstance(Term1.root, Function_Symbol) and Term1.root.name == 'quote'
    t2_is_quote = isinstance(Term2.root, Function_Symbol) and Term2.root.name == 'quote'
    if t1_is_quote and not t2_is_quote:
        return False
    elif t2_is_quote and not t1_is_quote:
        return True
    
    #If both Quote Terms 
    if not static_analysis and isinstance(Term1.root, Function_Symbol) and Term1.root.name == 'quote' and isinstance(Term2.root, Function_Symbol) and Term2.root.name == 'quote':
         val1 = evaluate_quote_term_runtime(Term1.arguments[0])
         val2 = evaluate_quote_term_runtime(Term2.arguments[0])
         return val1 > val2
    
    #A combination of constants, function symbols and quote terms
    if isinstance(Term1.root, (Constant, Function_Symbol, QuoteInteger, QuoteReal)) and isinstance(Term2.root, (Constant, Function_Symbol, QuoteInteger, QuoteReal)):
        if Term1_Precedence > Term2_Precedence:
            return True
        elif Term2_Precedence > Term1_Precedence:
            return False
        else: #If both are function symbols compare the arguments
            is_t1_literal = isinstance(Term1.root, (QuoteInteger, QuoteReal))
            is_t2_literal = isinstance(Term2.root, (QuoteInteger, QuoteReal))

            # Case 1: Both are Literals -> Compare Values
            if is_t1_literal and is_t2_literal:
                return Term1.root.value > Term2.root.value

            if Term1.root.name == 'quote':
                pass
            else:
                for i in range(len(Term1_Argument_List)):
                    arg1 = Term1_Argument_List[i]
                    arg2 = Term2_Argument_List[i]
                    if compare_terms_lexicographically(arg1, arg2, function_symbol_registry, constant_order, static_analysis=static_analysis, variable_order=variable_order, extra_constraints=extra_constraints):
                        return True
                    elif compare_terms_lexicographically(arg2, arg1, function_symbol_registry, constant_order, static_analysis=static_analysis, variable_order=variable_order, extra_constraints=extra_constraints):
                        return False
                return False

    if isinstance(Term1.root, QuoteInteger) and isinstance(Term2.root, IntegerVariable):
        if static_analysis:
            if Term1.root.value==0:
                return False
            
    if isinstance(Term1.root, IntegerVariable) and isinstance(Term2.root, QuoteInteger):
        if static_analysis:
            if Term2.root.value==0:
                return True

    
    ### Two variables or variables and constants together
    def get_order_key(t:Term):
        if isinstance(t.root, Variable):
            return t.root
        if isinstance(t.root, Function_Symbol) and t.root.name == "quote":
            quoted_value = t.arguments[0]
            if isinstance(quoted_value.root, Variable):
                return quoted_value.root
            return t
        if isinstance(t.root, (Constant, QuoteInteger, QuoteReal)):
            return t.root
        return None

    key1 = get_order_key(Term1)
    key2 = get_order_key(Term2)

    if key1 is not None and key2 is not None:
        if key1 in variable_order and key2 in variable_order:
            if variable_order[key1] ==  variable_order[key2]:
                return False
            elif variable_order[key1] >  variable_order[key2]:
                return True
            elif variable_order[key2] >  variable_order[key1]:
                return False


    ### Variables and Quote Terms which contain variables
    is_t1_semantic = isinstance(Term1.root, Variable) or (isinstance(Term1.root, Function_Symbol) and Term1.root.name == 'quote')
    is_t2_semantic = isinstance(Term2.root, Variable) or (isinstance(Term2.root, Function_Symbol) and Term2.root.name == 'quote')

    if is_t1_semantic and not is_t2_semantic:
        return False
    if is_t2_semantic and not is_t1_semantic:
        return True
    
    
    if static_analysis and (is_t1_semantic or is_t2_semantic):
        def _unwrap_quote(t:Term):
            if isinstance(t.root, Function_Symbol) and t.root.name == 'quote':
                return t.arguments[0]
            return t

        t1_unwrapped = _unwrap_quote(Term1)
        t2_unwrapped = _unwrap_quote(Term2)
        
        w1 = quote_term_to_symbolic_weight(t1_unwrapped)
        w2 = quote_term_to_symbolic_weight(t2_unwrapped)
        solver = z3.Solver()
        z3_vars= {}

        def collect_vars(w):
            if isinstance(w, VariableWeight):
                return {w.name}
            if isinstance(w, WeightOperation):
                if not w.args:
                    return set()
                return set().union(*(collect_vars(a) for a in w.args))
            return set()

        all_vars = collect_vars(w1).union(collect_vars(w2))


        for name in all_vars:
            z3_vars[name] = z3.Int(name)
            ### Carefully Investigate
            solver.add(z3_vars[name] >= 1) #We are assuming that variables are non-negative so we are able to determine if X+X>X or not. Maybe this should actually require splitting over cases?
            ### Carefully Investigate above
        vars_only = [k for k in variable_order.keys() if isinstance(k, Variable)]
        
        sorted_vars = sorted(vars_only, key=lambda v: variable_order[v], reverse = True)
        for i in range(len(sorted_vars) -1):
            high = sorted_vars[i].name
            low = sorted_vars[i+1].name
            if high in z3_vars and low in z3_vars:
                solver.add(z3_vars[high] >= z3_vars[low])
        for constraint in extra_constraints:
            if len(constraint) != 4:
                continue
        
            c_metric_idx, c_lhs, c_rel, c_rhs = constraint
            if c_metric_idx == LEXICOGRAPHIC_METRIC_INDEX:
                c_vars = collect_vars(c_lhs).union(collect_vars(c_rhs))

                
                if c_vars.issubset(all_vars):
                    z3_c_lhs = symbolic_weight_to_z3(c_lhs, z3_vars)
                    z3_c_rhs = symbolic_weight_to_z3(c_rhs, z3_vars)
                    if c_rel == ">":
                        solver.add(z3_c_lhs > z3_c_rhs)
                    elif c_rel == "<":
                        solver.add(z3_c_lhs < z3_c_rhs)
                    elif c_rel == "<=": 
                        solver.add(z3_c_lhs <= z3_c_rhs)
                    elif c_rel == ">=": 
                        solver.add(z3_c_lhs >= z3_c_rhs)
                    elif c_rel == "==": 
                        solver.add(z3_c_lhs == z3_c_rhs)
                    else:
                        raise ValueError(f"Unexpected relation in extra_constraints: {c_rel}")
                        
        z3_w1 = symbolic_weight_to_z3(w1, z3_vars)
        z3_w2 = symbolic_weight_to_z3(w2, z3_vars)

        solver.push()
        solver.add(z3.Not(z3_w1 > z3_w2))
        if solver.check() == z3.unsat:
            return True # Proven T1 > T2
        solver.pop()

        # 5. Check Strict Less (Reverse)
        solver.push()
        solver.add(z3.Not(z3_w2 > z3_w1))
        if solver.check() == z3.unsat:
            return False # Proven T2 > T1
        solver.pop()
        
        # 6. Check Equality
        solver.push()
        solver.add(z3.Not(z3_w1 == z3_w2))
        if solver.check() == z3.unsat:
            return False # They are equal, so T1 is not strictly greater
        solver.pop()
        
        
        solver.push()
        solver.add(z3_w1 > z3_w2)
        if solver.check() == z3.unsat:
            solver.pop()
            return False 
        solver.pop()

        raise IndeterminateWeightError(w1, w2, LEXICOGRAPHIC_METRIC_INDEX)
            
    raise VariableConstantComparisonError(f"Comparison needed between {Term1} and {Term2}")
    
    if static_analysis:
        # Print the rank of the roots if they exist in the order
        t1_key = Term1.root if isinstance(Term1.root, Variable) else None
        t2_key = Term2.root if isinstance(Term2.root, Variable) else None
        print(f"  Var Order T1: {variable_order.get(t1_key, 'N/A')}")
        print(f"  Var Order T2: {variable_order.get(t2_key, 'N/A')}")
    raise NotImplementedError(f"Have not implemented lexicographic comparison of types {type(Term1.root)} and {type(Term2.root)}. ")

def prove_lexicographic_greater_for_single_case(lhs_term, rhs_term, skolem_variables, variable_order, function_symbol_registry, constant_order, memo_cache, substitution, extra_constraints=[]):
    lhs_symbolic_weight_vector = get_weight(lhs_term, function_symbol_registry, constant_order, variable_order, static_analysis = True, memo_cache=memo_cache, extra_constraints=extra_constraints)
    rhs_symbolic_weight_vector = get_weight(rhs_term, function_symbol_registry, constant_order, variable_order, static_analysis = True, memo_cache=memo_cache, extra_constraints=extra_constraints)
    
    return recursively_prove_vector_is_greater(lhs_term, rhs_term, lhs_weight_vec = lhs_symbolic_weight_vector, rhs_weight_vec = rhs_symbolic_weight_vector,
                                               skolem_variables=skolem_variables, variable_order=variable_order, metric_index=0,
                                              function_symbol_registry=function_symbol_registry, constant_order=constant_order, substitution=substitution,
                                               extra_constraints=extra_constraints)


#def build_z3_multiset_comparison_expression(solver: z3.Solver, vector1_symbolic: list[SymbolicWeight], vector2_symbolic: list[SymbolicWeight], z3_vars: dict, relation:str) -> z3.BoolRef:
    #Builds a Z3 expression for unordered vector metrics
#    vec1_z3 = [symbolic_weight_to_z3(w, z3_vars) for w in vector1_symbolic]
#    vec2_z3 = [symbolic_weight_to_z3(w, z3_vars) for w in vector2_symbolic]#
#
#    sorted_vec1_z3 = _add_z3_permutation_constraints(solver, vec1_z3, "lhs_m5")
#    sorted_vec2_z3 = _add_z3_permutation_constraints(solver, vec2_z3, "rhs_m5")
#
#    return build_z3_lex_comparison_expression(sorted_vec_1_z3,sorted_vec_2_z3, z3_vars, relation) 
    

def z3_sort_descending(z3_exprs):
    if not z3_exprs:
        return []
    current_exprs = list(z3_exprs)
    n = len(current_exprs)

    for i in range(n):
        for j in range(0, n-i-1):
            a = current_exprs[j]
            b = current_exprs[j+1]
            # Create symbolic Max and Min
            # If a >= b, then (a, b) remains (a, b)
            # If a < b,  then (a, b) becomes (b, a)
            # Logic: new_a = If(a >= b, a, b) -> Max
            #        new_b = If(a >= b, b, a) -> Min
            current_exprs[j]     = z3.If(a >= b, a, b)
            current_exprs[j + 1] = z3.If(a >= b, b, a)
    return current_exprs

def build_z3_lex_comparison_expression(vector1_symbolic: list[SymbolicWeight], vector2_symbolic: list[SymbolicWeight], z3_vars, relation, unordered_vector: bool= False):
    vec1_z3 = [symbolic_weight_to_z3(item, z3_vars) for item in vector1_symbolic]
    vec2_z3 = [symbolic_weight_to_z3(item, z3_vars) for item in vector2_symbolic]
    
    if unordered_vector:
        vec1_z3 = z3_sort_descending(vec1_z3)
        vec2_z3 = z3_sort_descending(vec2_z3)

    if relation == '>':
        # Logic for v1 > v2: (v1[0]>v2[0]) OR (v1[0]==v2[0] AND v1[1]>v2[1]) OR ...
        components = []
        previously_equal_conditions = []
        for i in range(min(len(vec1_z3), len(vec2_z3))):
            greater_at_this_position = vec1_z3[i] > vec2_z3[i]
            components.append(z3.And(previously_equal_conditions + [greater_at_this_position]))
            previously_equal_conditions.append(vec1_z3[i] == vec2_z3[i])

        if len(vec1_z3) > len(vec2_z3):
            components.append(z3.And(previously_equal_conditions))

        return z3.Or(components)

    elif relation == '==':
        # Logic for v1 == v2: (v1[0]==v2[0]) AND (v1[1]==v2[1]) AND ... AND len(v1)==len(v2)
        if len(vec1_z3) != len(vec2_z3):
            return z3.BoolVal(False)

        equal_conditions = [vec1_z3[i] == vec2_z3[i] for i in range(len(vec1_z3))]
        return z3.And(equal_conditions)

    else:
        raise ValueError(f"Unsupported relation: '{relation}' for Z3 lex comparison")
    

def recursively_prove_vector_is_greater(lhs_term: Term, rhs_term: Term, lhs_weight_vec: list[list[SymbolicWeight]], rhs_weight_vec: list[list[SymbolicWeight]], skolem_variables, variable_order, metric_index, function_symbol_registry, constant_order, substitution, extra_constraints = []):
    if metric_index >= len(lhs_weight_vec):
        return compare_terms_lexicographically(lhs_term, rhs_term, function_symbol_registry, constant_order, static_analysis=True, variable_order=variable_order, extra_constraints=extra_constraints)

    
    solver = z3.Solver()
    solver.set("timeout", 5000)

    def get_z3_name(obj):
        if hasattr(obj, 'name'):
            return f"W_{obj.name}_metric{metric_index}"
        return f"W_{str(obj).replace('.', '_')}_metric{metric_index}"

    all_vars_in_order = [v for v in variable_order.keys() if isinstance(v, (Variable, IntegerVariable))]

    all_relevant_vars = set(skolem_variables).union(all_vars_in_order)

    z3_variables_for_this_metric = {get_z3_name(var): z3.Int(get_z3_name(var)) for var in all_relevant_vars}
    for var in all_relevant_vars:
        z3_var = z3_variables_for_this_metric[get_z3_name(var)]
        if isinstance(var, IntegerVariable):
            solver.add(z3_var >= 1)
        else:
            solver.add(z3_var >= 0)
    
        
    def get_z3_expr(item):
        z3_name = get_z3_name(item)
        if z3_name in z3_variables_for_this_metric: #if a variable, we assign a weight
            return z3_variables_for_this_metric[z3_name]
        else: #Is a constant term or a quote, in this case we simply compute the metric value
            if isinstance(item, Term):
                dummy_term = item
            else:
                dummy_term = Term(item)
            weight_sym = compute_single_metric(dummy_term, metric_index, True, variable_order, {}, function_symbol_registry, constant_order, extra_constraints=extra_constraints)

            if isinstance(weight_sym, list):
                if len(weight_sym) ==0:
                    weight_sym = ConstantWeight(0)
                elif len(weight_sym) ==1:
                    item = weight_sym[0]
                    if isinstance(item, ConstantWeight):
                        if item.value <= 0: #### FlashPoint1: Ensures that we cannot have negative weights come in.
                            weight_sym = ConstantWeight(0)
                        else:
                            weight_sym = item
                elif len(weight_sym) == 2 and weight_sym[-1].value==ConstantWeight(-1):
                    weight_sym = weight_sym[0]
                else:
                    raise ValueError(f"We received a list {weight_sym} as the weight for {dummy_term}. We only expect single entried weights for atomic terms. This will require more investigation.")
            return symbolic_weight_to_z3(weight_sym, {})
    all_entities = list(variable_order.keys())

    sorted_entities = sorted(all_entities, key=lambda e: variable_order.get(e,0), reverse=True)

    sorted_variables = [e for e in sorted_entities if isinstance(e, (Variable, IntegerVariable))]
    
    for i in range(len(sorted_variables)-1):
        term_with_higher_precedence = sorted_entities[i]
        term_with_lower_precedence = sorted_entities[i+1]

        z3_var_high = get_z3_expr(term_with_higher_precedence)
        z3_var_low = get_z3_expr(term_with_lower_precedence)

        solver.add(z3_var_high >= z3_var_low) ###FIX Should be greater than or equal to unless metrix_index = total_number_of_metrics-1
    

    z3_vars_for_builder = {}
    for var in skolem_variables:
        z3_vars_for_builder[var.name] = z3_variables_for_this_metric[get_z3_name(var)]

    z3_vars_for_constraints = {}
    for var in all_relevant_vars:
        z3_vars_for_constraints[var.name] = z3_variables_for_this_metric[get_z3_name(var)]

    def collect_vars_from_constraint(c_item):
        if isinstance(c_item, list):
            return set().union(*(collect_vars_from_constraint(x) for x in c_item))
        if isinstance(c_item, VariableWeight):
            return {c_item.name}
        if isinstance(c_item, WeightOperation):
            return set().union(*(collect_vars_from_constraint(arg) for arg in c_item.args))
        return set()
    
    #Apply extra constraints from case-splits
    for constraint in extra_constraints:
        if len(constraint) == 4:
            c_metric_idx, c_lhs, c_rel, c_rhs = constraint
            c_vars = collect_vars_from_constraint(c_lhs).union(collect_vars_from_constraint(c_rhs))
            for v_name in c_vars:
                if v_name not in z3_vars_for_constraints:
                    # Map to the current metric's variable if it exists, otherwise create it
                    z3_name = f"W_{v_name}_metric{metric_index}"
                    if z3_name in z3_variables_for_this_metric:
                        z3_vars_for_constraints[v_name] = z3_variables_for_this_metric[z3_name]
                    else:
                        # If the variable is not in the current terms, we must create a new Z3 var for it
                        # and ensure it shares the same name format so it links up if it appears later.
                        new_z3_var = z3.Int(z3_name)
                        z3_variables_for_this_metric[z3_name] = new_z3_var
                        z3_vars_for_constraints[v_name] = new_z3_var
                        # Assume standard non-negative constraint for these "external" variables
                        solver.add(new_z3_var >= 0)
            
            if c_metric_idx == metric_index:
                # 1. Handle Vector (List) Constraints
                if isinstance(c_lhs, list):
                    if c_rel == ">":
                        solver.add(build_z3_lex_comparison_expression(c_lhs, c_rhs, z3_vars_for_constraints, '>'))
                    elif c_rel == "<":
                        solver.add(build_z3_lex_comparison_expression(c_rhs, c_lhs, z3_vars_for_constraints, '>'))
                    elif c_rel == ">=":
                        gt = build_z3_lex_comparison_expression(c_lhs, c_rhs, z3_vars_for_constraints, '>')
                        eq = build_z3_lex_comparison_expression(c_lhs, c_rhs, z3_vars_for_constraints, '==')
                        solver.add(z3.Or(gt, eq))
                    elif c_rel == "<=":
                        gt = build_z3_lex_comparison_expression(c_rhs, c_lhs, z3_vars_for_constraints, '>')
                        eq = build_z3_lex_comparison_expression(c_lhs, c_rhs, z3_vars_for_constraints, '==')
                        solver.add(z3.Or(gt, eq))
                    elif c_rel == "==":
                        solver.add(build_z3_lex_comparison_expression(c_lhs, c_rhs, z3_vars_for_constraints, '=='))
            
                # 2. Handle Atomic Constraints
                else:
                    z3_c_lhs = symbolic_weight_to_z3(c_lhs, z3_vars_for_constraints)
                    z3_c_rhs = symbolic_weight_to_z3(c_rhs, z3_vars_for_constraints)
    
                    if c_rel == ">":
                        solver.add(z3_c_lhs > z3_c_rhs)
                    elif c_rel == "<":
                        solver.add(z3_c_lhs < z3_c_rhs)
                    elif c_rel == ">=":
                        solver.add(z3_c_lhs >= z3_c_rhs)
                    elif c_rel == "<=":
                        solver.add(z3_c_lhs <= z3_c_rhs)
                    elif c_rel == "==":
                        solver.add(z3_c_lhs == z3_c_rhs)
    
    lhs_metric_symbolic = lhs_weight_vec[metric_index]
    rhs_metric_symbolic = rhs_weight_vec[metric_index]
    

    #print(f"\n[DEBUG] Checking Metric {metric_index}")
    #print(f"  LHS Weight: {lhs_metric_symbolic}")
    #print(f"  RHS Weight: {rhs_metric_symbolic}")
    
    
    is_greater_expr = build_z3_lex_comparison_expression(lhs_metric_symbolic, rhs_metric_symbolic, z3_vars_for_builder, '>')
    is_equal_expr = build_z3_lex_comparison_expression(lhs_metric_symbolic, rhs_metric_symbolic, z3_vars_for_builder, '==')
    

    # --- Perform the Z3 Proofs ---
    solver.push()
    ### First we check if LHS > RHS
    solver.add(z3.Not(is_greater_expr))
    if solver.check() == z3.unsat:
        solver.pop()
        return True
    solver.pop()

    solver.push()
    ### Second we check for equality, if they are equal we recurse:
    ###18/12/2025 Update - we actually check for >=, because it may not be possible to show ==. But if we can show >= (given that we already know not >) that should be sufficient.
    ### We recurse if LHS >= RHS
    is_gte_expr = z3.Or(is_greater_expr, is_equal_expr)
    solver.add(z3.Not(is_gte_expr))
    if solver.check() == z3.unsat:
        solver.pop()
        return recursively_prove_vector_is_greater(lhs_term, rhs_term, lhs_weight_vec, rhs_weight_vec, skolem_variables, variable_order, metric_index + 1, function_symbol_registry, constant_order, substitution, extra_constraints=extra_constraints)
    solver.pop()

    solver.push()
    solver.add(is_greater_expr)
    if solver.check() == z3.unsat:
        solver.pop()
        return False 
    solver.pop()
    
    solver.push()
    solver.add(is_greater_expr)
    if solver.check() == z3.sat: #In this case it is possible to be both greater and possible to be smaller, so we must split over cases.
        solver.pop()
        raise IndeterminateWeightError(lhs_metric_symbolic, rhs_metric_symbolic, metric_index)
    solver.pop()

    return False


def vector_comparison_greater_than(Term1: Term, Term2: Term, function_symbol_registry: Dict[str, List[Union[str, int]]], constant_order: Dict[str, int], static_analysis: bool = False, variable_order: Dict[str, int] = {}, memo_cache: Dict[str, int]={}, substitution: dict=None, extra_constraints=[]) -> bool:
    
    class IndeterminateComparisonError(Exception):
        """Raised when Z3 can neither prove >, <, nor == for two items."""
        def __init__(self, item1, item2, model):
            self.item1 = item1
            self.item2 = item2
            self.model = model
            super().__init__(
                f"Z3 comparison is indeterminate. Cannot prove >, <, or == for:\n"
                f"  Item 1: {item1}\n"
                f"  Item 2: {item2}\n"
                f"Z3 can find models for both '>' and '<=' (or '>' and '<'). A possible counterexample model for '>' is: {model}"
            )
        
    #Works for ground terms
    def recursive_lexicographic_compare(vec1, vec2) -> int:
        for i in range(min(len(vec1), len(vec2))):
            item1 = vec1[i]
            item2 = vec2[i]
            is_item1_list = isinstance(item1, list)
            is_item2_list = isinstance(item2, list)

            if is_item1_list != is_item2_list:
                raise TypeError(f"Mismatched types in weight vectors. Cannot compare {type(item1)=} with {type(item1)=}.")

            if is_item1_list:
                result = recursive_lexicographic_compare(item1, item2)
                if result != 0:
                    return result
            else: #both items should be ints or floats
                if item1 > item2:
                    return 1
                if item1< item2:
                    return -1

        if len(vec1) > len(vec2):
            return 1
        if len(vec2) > len(vec1):
            return -1
        return 0
    
    def z3_lexicographical_compare(solver, vec1_z3, vec2_z3):
        #Builds a z3 expression for the lexicographical comparison vec1_z3> vec2_z3
        conditions = []
        prev_equalities = []
        for i in range(min(len(vec1_z3), len(vec2_z3))):
            greater_at_this_pos = z3.And(prev_equalities + [vec1_z3[i] > vec2_z3[i]])
            conditions.append(greater_at_this_pos)
            prev_equalities.append(vec1_z3[i] == vec2_z3[i])
        if len(vec1_z3) > len(vec2_z3):
            conditions.append(z3.And(prev_equalities))
        return z3.Or(conditions)

    #Main comparison logic (draws on the existing functions)
    if not static_analysis:
        weight1 = get_weight(Term1, function_symbol_registry, constant_order, variable_order=variable_order, static_analysis=False, extra_constraints=extra_constraints)
        weight2 = get_weight(Term2, function_symbol_registry, constant_order, variable_order=variable_order, static_analysis=False, extra_constraints=extra_constraints)
        comparison_result = recursive_lexicographic_compare(weight1, weight2)
        if comparison_result ==1:
            return True
        elif comparison_result ==-1:
            return False
        else:
            return compare_terms_lexicographically(Term1, Term2, function_symbol_registry, constant_order, static_analysis=False, variable_order=variable_order, extra_constraints = extra_constraints)
            
        return compare_weights_gtr(weight1, weight2, Term1, Term2)
    else:
        skolem_variables = []
        for t in Term1.subterms + Term2.subterms:
            if isinstance(t.root, Variable) and t.root not in skolem_variables:
                 skolem_variables.append(t.root)
        
        return prove_lexicographic_greater_for_single_case(Term1, Term2, skolem_variables, variable_order, function_symbol_registry, constant_order, memo_cache, substitution, extra_constraints=extra_constraints)