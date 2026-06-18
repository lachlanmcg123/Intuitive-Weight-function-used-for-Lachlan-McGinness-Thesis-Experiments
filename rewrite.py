from typing import Dict, Tuple, List
from term import Term, Variable, Function_Symbol, Constant, QuoteInteger, QuoteReal, Substitution, create_quote_integer, create_wrapped_quote
from rules import Rewrite_Rule, Guard, Relation 
import math


##Call MatchFail
class MatchError(Exception):
    pass


### Match is a python keyword - don't do this!
def match(pattern: Term, target: Term) -> Substitution:
    """
    Tries to match a pattern Term against a target Term.
    Returns a substitution dictionary if successful.
    Raises MatchError if it fails.
    """
    
    substitution: Substitution = {}

    def _match_recursive(p: Term, t: Term):
        if isinstance(p.root, Variable):
            if p.root in substitution:
                if substitution[p.root] != t:
                    raise MatchError(f"Variable {p.root.name} cannot match both {substitution[p.root]} and {t}")
            else:
                substitution[p.root] = t
            return 
        
        if isinstance(p.root, (QuoteInteger, QuoteReal)):
            if isinstance(t.root, (QuoteInteger, QuoteReal)):
                if p.root.value == t.root.value:
                    return
            raise MatchError(f"QuoteTerm mismatch: {p.root} vs {t.root}")
        
        if type(p.root) is not type(t.root) or p.root.name != t.root.name:
            raise MatchError(f"Root mismatch:{p.root} vs {t.root}")

        if isinstance(p.root, Function_Symbol):
            if p.root.arity != t.root.arity:
                raise MatchError(f"Arity mismatch for function {p.root.name}")

            for p_arg, t_arg in zip(p.arguments, t.arguments):
                _match_recursive(p_arg, t_arg)

    _match_recursive(pattern, target)
    return (substitution)


def apply_substitution(term: Term, substitution: Substitution) -> Term:
    """
    Applies a substitution to a term, returning a new term.
    """
    # Base Case 1: The term is a variable found in the substitution.
    if isinstance(term.root, Variable) and term.root in substitution:
        return substitution[term.root]

    # Base Case 2: The term is a constant or a variable not in the substitution.
    if isinstance(term.root, Variable) or isinstance(term.root, Constant):
        return term

    # Recursive Step: The term is a function application.
    # We need to apply the substitution to all of its arguments.
    new_args = [apply_substitution(arg, substitution) for arg in term.arguments]
    if isinstance(term.root, Function_Symbol) and all(isinstance(arg.root, Function_Symbol) and arg.root.name == 'quote' for arg in new_args):
        try:
            val = None
            values = [arg.arguments[0].root.value for arg in new_args]

            if term.root.name == "+":
                val = values[0] + values[1]
            elif term.root.name == "-":
                val = values[0] - values[1]
            elif term.root.name == "*":
                val = values[0] * values[1]
            elif term.root.name == "/":
                val = values[0] / values[1]
            elif term.root.name == "^": 
                val = values[0]**values[1]
            elif term.root.name == "sin":
                val = math.sin(values[0])
            elif term.root.name == "cos":
                val = math.cos(values[0])
            if val is not None:
                if isinstance(val, float) and val.is_integer():
                    return create_wrapped_quote(Term(create_quote_integer(int(val))))
                elif isinstance(val, int):
                     return create_wrapped_quote(Term(create_quote_integer(val)))
                else:
                     return create_wrapped_quote(Term(create_quote_real(val)))
        except Exception:
            pass
    if isinstance(term.root, Function_Symbol) and term.root.name == 'quote':
        def _flatten_nested_quotes(t: Term) -> Term:
            # If we find a quote, strip it and recurse on its content
            # This handles [[X]] -> X, and also [0 * [X]] -> 0 * X
            if isinstance(t.root, Function_Symbol) and t.root.name == 'quote':
                return _flatten_nested_quotes(t.arguments[0])
            
            # If it's a function, recurse into arguments to find hidden quotes
            if isinstance(t.root, Function_Symbol):
                flattened_args = [_flatten_nested_quotes(arg) for arg in t.arguments]
                return Term(t.root, flattened_args)
            
            # Constants/Variables/Literals return as is
            return t

        def _evaluate_inner_arithmetic(t: Term):
            if isinstance(t.root, (QuoteInteger, QuoteReal)):
                return t.root.value

            elif isinstance(t.root, Function_Symbol) and t.root.name in ['+', '-', '*', '/', '^', 'sin', 'cos']:
                arg_vals = [_evaluate_inner_arithmetic(arg) for arg in t.arguments]

                if any(v is None for v in arg_vals):
                    return None
                try:
                    if t.root.name == '+': return arg_vals[0] + arg_vals[1]
                    if t.root.name == '-': return arg_vals[0] - arg_vals[1]
                    if t.root.name == '*': return arg_vals[0] * arg_vals[1]
                    if t.root.name == '/': return arg_vals[0] / arg_vals[1]
                    if t.root.name == '^': return arg_vals[0] ** arg_vals[1]
                    if t.root.name == 'sin': return math.sin(arg_vals[0])
                    if t.root.name == 'cos': return math.cos(arg_vals[0])
                except Exception:
                    return None
            return None
        
        if new_args:
            flattened_content = _flatten_nested_quotes(new_args[0])
            # Try to evaluate the arithmetic inside the quote
            val = _evaluate_inner_arithmetic(flattened_content)
            if val is not None:
                # If evaluation succeeded, return a new quote containing the result
                if isinstance(val, int) or (isinstance(val, float) and val.is_integer()):
                    return create_wrapped_quote(Term(create_quote_integer(int(val))))
                else:
                    return create_wrapped_quote(Term(create_quote_real(val)))

            return Term(term.root, [flattened_content])
    return Term(term.root, new_args)

def rewrite(rule: Rewrite_Rule, term: Term, function_symbol_registry, parameter_order, variable_order={}, static_analysis=False, extra_constraints=[]) -> Term:
    """
    Attempts to apply a single rewrite rule to a term.
    If successful, returns the new rewritten term.
    Otherwise, returns the original term unchanged.
    """
    try:
        # 1. Find a substitution that matches the rule's LHS to the term.
        sub = match(rule.LHS, term)

        # 2. Check the guards.
        for guard in rule.Guard_List:
            # Apply the substitution to both sides of the guard to get ground terms.
            guard_lhs = apply_substitution(guard.left_term, sub)
            guard_rhs = apply_substitution(guard.right_term, sub)

            
            if not guard.relation.evaluate(guard_lhs, guard_rhs, function_symbol_registry, parameter_order, variable_order=variable_order, static_analysis=static_analysis, extra_constraints=extra_constraints):
                return term # If any guard is false, the rule does not apply.

        # 3. If all guards pass, apply the substitution to the rule's RHS.
        return apply_substitution(rule.RHS, sub)

    except MatchError:
        # If matching fails, the rule doesn't apply.
        return term

def apply_rewrite_rule_at_any_position(rule: Rewrite_Rule, term: Term, function_symbol_registry, constant_order, variable_order={}, static_analysis=False, extra_constraints=[]) -> Tuple[Term, bool]:
    #Recursively traverses a term to find the first possible application of a given rule.
    #We use an "innermost" strategy where we try the roots before the parent
    # returns a Tuple with a (potentially rewritten) term and a boolean indicating if a rewrite occured (true) or not (false)
    
    if not term.arguments: #A constant or variable cannot be rewritten
        return (term, False)
    
    # [DEBUG FLOW START]
    if isinstance(term.root, Function_Symbol) and term.root.name == "quote":
            pass
    else:
        arguments = list(term.arguments)
        for i, argument in enumerate(arguments): #Recurse down into arguements and apply rewrite rules there first
            rewritten_argument, success = apply_rewrite_rule_at_any_position(rule, argument, function_symbol_registry, constant_order, variable_order=variable_order, static_analysis=static_analysis, extra_constraints=extra_constraints)
                
            if success:
                arguments[i] = rewritten_argument #update argument with rewritten term
                rebuilt_term = Term(term.root, arguments)
                return (rebuilt_term, True)
        
    #Attempt to rewrite current term 
    rewritten_term = rewrite(rule, term, function_symbol_registry, constant_order, variable_order=variable_order, static_analysis=static_analysis, extra_constraints=extra_constraints)
    
    if rewritten_term != term: #In this case we were able to make a rewrite
        return (rewritten_term, True)
    
    #If we reach here then then no rewrite was possible here or at any level below. 
    return (term, False)



def apply_ruleset_once(rules: List[Rewrite_Rule], term: Term, function_symbol_registry, constant_order, debug=False, variable_order={}, static_analysis=False, extra_constraints=[]) -> Tuple[Term, bool]:
    for rule in rules:
        resulting_term, rewrite_success = apply_rewrite_rule_at_any_position(rule, term, function_symbol_registry, constant_order, variable_order=variable_order, static_analysis=static_analysis, extra_constraints=extra_constraints)
        if rewrite_success:
            if debug:
                print(f"Applied Rule: {rule}")
                print(f"Result: {resulting_term}")
            return resulting_term, True

    return term, False


def normal_form(rules: List[Rewrite_Rule], term: Term, function_symbol_registry, constant_order, debug=False, variable_order={}, static_analysis=False, extra_constraints=[]) -> Term:
    current_term = term

    step_count = 0
    MAX_STEPS = 1000
    while True:
        if step_count > MAX_STEPS:
            if debug or static_analysis:
                print(f"Warning, the number of steps required to reach normal form has exceeded the limit of {MAX_STEPS}. Aborting to prevent infinite loop.")
                print(f"Stuck at: {current_term}")
            break

            if step_count > 20: 
                print(f"  [Step {step_count}] Current: {current_term}")
                
        rewritten_term, success = apply_ruleset_once(rules, current_term, function_symbol_registry, constant_order, debug, variable_order=variable_order, static_analysis=static_analysis, extra_constraints=extra_constraints)

        if success:
            
            if step_count > 100:
                print(f"      -> Rewrite steps so far: {step_count}. Rewrote to: {rewritten_term}")
            
            current_term = rewritten_term
            step_count += 1
        else:
            break
        

    return current_term
