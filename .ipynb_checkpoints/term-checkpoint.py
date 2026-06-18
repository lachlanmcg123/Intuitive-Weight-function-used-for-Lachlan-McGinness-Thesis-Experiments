import re
from dataclasses import dataclass, field
from typing import List, Union, Dict, Tuple
import parsley

#function_symbol_list = [["+",2, 1], ["-",2, 1], ["*",2, 2], ["/",2, 2], ["^",2, 3], ["sin",1, 4], ["cos",1, 4]] #[name, arity, associativity_precedence_level]

function_symbol_registry = {}
constant_registry = {}
variable_registry = {}
quote_integer_registry = {}
quote_real_registry = {}
integer_variable_registry = {}

@dataclass(frozen=True)
class QuoteInteger:
    value: int

@dataclass(frozen=True)
class QuoteReal:
    value: float

@dataclass(frozen=True)
class Function_Symbol:
    name: str
    arity: int
    precedence_level: int
    lexicographic_precedence_level: int

function_symbol_list = [["+",2, 1], ["-",2, 1], ["*",2, 2], ["/",2, 2], ["^",2, 3], ["cos",1, 4], ["sin",1, 4], ["quote",1 ,-1]] #[name, arity, associativity_precedence_level], the order of these symbols defines their lexicographic precedence.

for index, function_symbol in enumerate(function_symbol_list):
    function_symbol = Function_Symbol(function_symbol[0], function_symbol[1], function_symbol[2], index+1)
    function_symbol_registry[function_symbol.name] = function_symbol

@dataclass(frozen=True)
class Constant:
    name: str

sorted_constant_keys = sorted(constant_registry.keys())
constant_order = {}
for index, key in enumerate(sorted_constant_keys, start=1):
    constant_order[key] = index

@dataclass(frozen=True)
class Variable:
    name: str

@dataclass(frozen=True)
class IntegerVariable(Variable):
    pass

def get_integer_variable(name):
    if name not in integer_variable_registry:
        integer_variable_registry[name] = IntegerVariable(name)
    return integer_variable_registry[name]

#Maybe this should be an abstract base clss (ABC) - Will help if we want to add extra classes later. 
@dataclass(frozen=True)
class Term:
    root: Union[Function_Symbol, Constant, Variable, QuoteInteger, QuoteReal]
    arguments: Tuple['Term'] = field(default_factory=list, repr=False)

    def __post_init__(self):
        object.__setattr__(self, 'arguments', tuple(self.arguments))
        if isinstance(self.root, (Constant, Variable, QuoteInteger, QuoteReal)):
            if self.arguments:
                raise ValueError("Constant, Variable, QuoteInteger and QuoteReal terms must not have arguments")
        elif isinstance(self.root, Function_Symbol):
            if not isinstance(self.arguments,tuple):
                raise TypeError("Function terms must have a list of arguments")
            if len(self.arguments) != self.root.arity:
                raise ValueError(f"Function '{self.root.name}' expects {self.root.arity} arguments, but got {len(self.arguments)} instead.")
            for subterm in self.arguments:
                if not isinstance(subterm, Term):
                    raise TypeError("Subterms must be of the type Term.")
            # [DEBUG] Aggressive Nested Quote Check
            if self.root.name == 'quote':
                # Check immediate child
                if self.arguments:
                    child = self.arguments[0]
                    if isinstance(child.root, Function_Symbol) and child.root.name == 'quote':
                        print(f"\n[DEBUG] CRITICAL: Nested Quote Detected in __post_init__!")
                        print(f"  Outer: {self.root.name}")
                        print(f"  Inner: {child}")
                        import traceback
                        traceback.print_stack()
                        # raise ValueError("Nested quotes are forbidden.") # Uncomment to stop immediately
        else:
            raise TypeError("Root must be a Constant, Variable, QuoteInteger, QuoteReal or Function_Symbol")
    
    @property
    def subterms(self):
        local_subterms = [self]
        for argument in self.arguments:
            local_subterms.extend(argument.subterms)
        return local_subterms
        

    def __repr__(self):
        if isinstance(self.root, (Constant, Variable)):
            return f"{self.root.name}"
        elif isinstance(self.root, (QuoteInteger, QuoteReal)):
            return str(self.root.value)
        else:
            args = ", ".join(repr(arg) for arg in self.arguments)
            return f"{self.root.name}({args})"


Substitution = Dict[Variable, Term]

def get_constant(name):
    if name not in constant_registry:
        constant_registry[name] = Constant(name)
    return constant_registry[name]

def get_variable(name):
    if name not in variable_registry:
        variable_registry[name] = Variable(name)
    return variable_registry[name]

def create_quote_integer(value_str):
    value = int(value_str)
    if value not in quote_integer_registry:
        quote_integer_registry[value] = QuoteInteger(value)
    return quote_integer_registry[value]

def create_quote_real(value_str):
    value = float(value_str)
    if value not in quote_real_registry:
        quote_real_registry[value] = QuoteReal(value)
    return quote_real_registry[value]

def build_term(left,right_terms):
    for function_symbol, right_term in right_terms:
        corresponding_function = function_symbol_registry[function_symbol]
        left = Term(corresponding_function, [left, right_term])
    return left

def create_wrapped_quote(value_term: Term) -> Term:
    quote_func = function_symbol_registry['quote']
    return Term(quote_func, [value_term])

#Basic Elements
grammar = """
ws = ' '*
integer = <'-'? digit+>
real = <'-'? digit+ '.' digit+>
number = <digit+>
identifier = <letter (letterOrDigit|'_')*>
"""

#Expression Structure
term_grammar = """

#Level 4
polynomial_term = monomial_term:left_term (ws <'+'|'-'>:op ws monomial_term:r -> (op,r))*:right_terms -> build_term(left_term,right_terms)

#Level 3
monomial_term = exponential_term:left_term (ws <'*'|'/'>:op ws exponential_term:r ->(op,r))*:right_terms -> build_term(left_term, right_terms)

#Level 2 - Exponential_term
exponential_term = (unary_term:u_base (ws '^' ws exponential_term:u_power) -> Term(function_symbol_registry['^'],[u_base,u_power])) | unary_term

#Level 1 - Unary Term
unary_term = (<'sin' | 'cos'>:name '(' ws polynomial_term:poly ws ')' -> Term(function_symbol_registry[name], [poly])) | 
    ('-' ws unary_term:t -> Term(function_symbol_registry['*'], create_wrapped_quote(Term(create_quote_integer(-1))), t)) |
    primary_term

# Level 0 - Highest precedence
primary_term = identifier:c -> Term(get_constant(c))
    | real:r -> create_wrapped_quote(Term(create_quote_real(r)))
    | integer:i -> create_wrapped_quote(Term(create_quote_integer(i)))
    | '(' ws polynomial_term:poly ws ')'-> poly  #Primaries are indivisible things in the expressions, either individual parameters or expressions wrapped in parentheses
"""

grammar += term_grammar

Term.parser = parsley.makeGrammar(grammar,
    {
        "Term": Term,
        "get_constant": get_constant,
        "get_variable": get_variable,
        "function_symbol_registry": function_symbol_registry,
        "build_term": build_term,
        "create_quote_integer": create_quote_integer,
        "create_quote_real": create_quote_real,
        "create_wrapped_quote": create_wrapped_quote,
    })

def parsley_parse(cls, expression_string):
    return cls.parser(expression_string).polynomial_term()

Term.parse = classmethod(parsley_parse)

def generate_constant_order():
    """
    Generates a lexicographical (alphabetical) ordering from the current
    state of the global constant_registry.
    Returns a dictionary mapping constant names to their precedence level.
    """
    # Get all the constant names from the registry's keys
    sorted_keys = sorted(constant_registry.keys())
    
    # Build a dictionary mapping each name to its sorted position (e.g., 'a':1, 'b':2)
    order = {key: index + 1 for index, key in enumerate(sorted_keys)}
    return order
