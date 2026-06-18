from dataclasses import dataclass, field
from term import Term, Function_Symbol, Constant, Variable, IntegerVariable, get_constant, get_variable, build_term, function_symbol_registry, constant_registry, variable_registry, constant_order, create_quote_integer, create_quote_real, get_integer_variable, QuoteInteger, QuoteReal, create_wrapped_quote
from weights import get_weight, vector_comparison_greater_than
from enum import Enum
from typing import List
import parsley

class Relation(Enum): ### We now have a relation class. We should be able to use weights to implement each of the relations.
    GT = '>'
    LT = '<'
    GTE = '>='
    LTE = '<='
    EQ = '='
    NOT_CONTAINS = '!contains'

    def evaluate(self, left_value, right_value, function_symbol_registry, constant_order, variable_order={}, static_analysis=False, extra_constraints=[]) -> bool:
        if self == Relation.GT:
            return vector_comparison_greater_than(left_value, right_value, function_symbol_registry, constant_order, static_analysis=static_analysis, variable_order=variable_order, extra_constraints=extra_constraints)
        if self == Relation.LT:
            return vector_comparison_greater_than(right_value, left_value, function_symbol_registry, constant_order, static_analysis=static_analysis, variable_order=variable_order, extra_constraints=extra_constraints)
        if self == Relation.GTE:
            if left_value == right_value:
                return True
            else:
                return vector_comparison_greater_than(left_value, right_value, function_symbol_registry, constant_order, static_analysis=static_analysis, variable_order=variable_order, extra_constraints=extra_constraints)
        if self == Relation.LTE:
            if left_value == right_value:
                return True
            else:
                return vector_comparison_greater_than(right_value, left_value, function_symbol_registry, constant_order, static_analysis=static_analysis, variable_order=variable_order, extra_constraints=extra_constraints)
        if self == Relation.EQ:
            return left_value == right_value
        if self == Relation.NOT_CONTAINS:
            return not _term_contains(left_value, right_value)
        raise NotImplementedError(f"Evaluation for {self.name} is not implemented.")
    

@dataclass(frozen=True)
class Guard:
    left_term: Term
    relation: Relation
    right_term: Term


@dataclass(frozen=True)
class Rewrite_Rule:
    LHS: Term
    RHS: Term
    Guard_List: List[Guard] = field(default_factory=list)
    
    def __post_init__(self):
        if not isinstance(self.LHS, Term):
            raise ValueError("LHS must be a Term")
        if not isinstance(self.RHS, Term):
            raise ValueError("RHS must be a Term")
        if not isinstance(self.Guard_List, list):
            pass #We now allow guards to be tuples as well as lists
            #raise ValueError("Guard_List must be a (potentially empty) list")
        object.__setattr__(self, 'Guard_List', tuple(self.Guard_List))

    def __repr__(self):
        return f"Rule({self.LHS} -> {self.RHS} | {self.Guard_List})"





#construct grammar for TRS rules
rule_grammar = """
# A rule without conditions is a LHS term, an arrow, a RHS term, and a period.
rewrite_rule = polynomial_term:lhs ws '->' ws polynomial_term:rhs (ws '|' ws guard_list)?:guards ws '.' -> Rewrite_Rule(lhs, rhs, guards or [])

relation = '>=' | '<=' |'>' | '<' |  '='
guard = polynomial_term:left ws relation:rel ws polynomial_term:right -> Guard(left, Relation(rel), right)
guard_list = guard:first (ws ',' ws guard)*:rest -> [first] + rest

ws = ' '*
integer = <'-'? digit+>
real = <'-'? digit+ '.' digit+>
identifier = <letter (letterOrDigit|'_')*>

#Level 4
polynomial_term = monomial_term:left_term (ws <'+'|'-'>:op ws monomial_term:r -> (op,r))*:right_terms -> build_term(left_term,right_terms)

#Level 3
monomial_term = exponential_term:left_term (ws <'*'|'/'>:op ws exponential_term:r ->(op,r))*:right_terms -> build_term(left_term, right_terms)

#Level 2 - Exponential_term
exponential_term = (unary_term:u_base (ws '^' ws exponential_term:u_power) -> Term(function_symbol_registry['^'],[u_base,u_power])) | unary_term

#Level 1 - Unary Term
unary_term = (<'sin' | 'cos'>:name '(' ws polynomial_term:poly ws ')' -> Term(function_symbol_registry[name], [poly])) | 
    ('-' ws unary_term:t -> Term(function_symbol_registry['*'], [create_wrapped_quote(Term(create_quote_integer(-1))), t])) |
    primary_term

# Level 0 - Highest precedence
primary_term = '[' ws polynomial_term:t ws ']' -> create_quote_term(t)
    | identifier:c -> Term(get_variable(c))
    | real:r -> create_wrapped_quote(Term(create_quote_real(r)))
    | integer:i -> create_wrapped_quote(Term(create_quote_integer(i)))
    | '(' ws polynomial_term:poly ws ')'-> poly  #Primaries are indivisible things in the expressions, either individual constants/variables or expressions wrapped in parentheses
"""
### Rule grammar uses get_variable in the place of get_constant

def create_quote_term(inner_term):
    # Helper to recursively unwrap literals (integers/reals) inside the quoted term.
    # This ensures that [0 * X] becomes quote(*(0, X)) instead of quote(*(quote(0), X)).
    def unwrap_literals(t):
        # If we see quote(literal), strip the quote to get the raw literal
        if isinstance(t.root, Function_Symbol) and t.root.name == 'quote':
            if isinstance(t.arguments[0].root, (QuoteInteger, QuoteReal)):
                return t.arguments[0]
        
        # Recurse into function arguments (e.g. for *)
        if isinstance(t.root, Function_Symbol):
            new_args = [unwrap_literals(arg) for arg in t.arguments]
            return Term(t.root, new_args)
        
        return t

    # 1. Clean the inner term (convert quote(0) -> 0)
    cleaned_inner = unwrap_literals(inner_term)

    # 2. Wrap the result in a quote
    return Term(function_symbol_registry['quote'], [cleaned_inner])

Rule_Parser = parsley.makeGrammar(rule_grammar, {
    "Term": Term,
    "get_constant": get_constant,
    "get_variable": get_variable,
    "get_integer_variable": get_integer_variable,
    "function_symbol_registry": function_symbol_registry,
    "build_term": build_term,
    "Rewrite_Rule": Rewrite_Rule,
    "Guard": Guard,
    "Relation": Relation,
    "create_quote_integer": create_quote_integer,
    "create_quote_real": create_quote_real,
    "create_quote_term": create_quote_term,
    "create_wrapped_quote": create_wrapped_quote,
})

test_rule_string = "X + Y -> Y + X | Y > X."
parsed_rule = Rule_Parser(test_rule_string).rewrite_rule()


def load_rules_from_file(filepath: str) -> List[Rewrite_Rule]:
    parsed_rules = []
    try:
        with open(filepath, 'r') as f:
            #Removes comments which trail on lines
            for line in f:
                clean_line = line.split('%',1)[0].strip()
                
                if not clean_line: #Ignores empty lines (or lines that are only comments)
                    continue

                try:
                    parsed_rule = Rule_Parser(clean_line).rewrite_rule()
                    parsed_rules.append(parsed_rule)
                except Exception as e:
                    print(f"Warning: Could not parse rule string: \n'{clean_line.strip()}' \nError: {e}\n")

    except FileNotFoundError:
        print(f"Error: the file '{filepath}' was not found.")
        return []
            
    return parsed_rules

def _term_contains(haystack: Term, needle: Term) -> bool:
    if haystack == needle: 
        return True
    
    # Handle the parser's wrapping of integers: -1 might be inside a quote
    if isinstance(needle.root, Function_Symbol) and needle.root.name == 'quote':
        inner_needle = needle.arguments[0]
        if haystack == inner_needle:
            return True
            
    # Recursive step
    for arg in haystack.arguments:
        if _term_contains(arg, needle):
            return True
    return False


