from term import Term, Variable, Substitution, Constant, QuoteInteger, QuoteReal, Function_Symbol
from typing import List, Set, Iterator, Tuple, Dict
from rules import Rule_Parser
import itertools

def find_variables_from_terms(terms: List[Term]) -> Set[Variable]:
    #Finds all unique variables from within a list of terms

    all_vars = set()

    def find_variables_recursive(t: Term):
        if isinstance(t.root, Variable):
            all_vars.add(t.root)

        for arg in t.arguments:
            find_variables_recursive(arg)

    for term in terms:
        find_variables_recursive(term)

    return all_vars

def generate_partitions(elements: list) -> Iterator[List[List]]:
    #Generates all possible partitions of a set of elements.
    #Example: [1, 2] -> [[1], [2]] and [[1, 2]]
    if not elements:
        yield []
        return
    first = elements[0]
    rest = elements[1:]
    for smaller_partition in generate_partitions(rest):
        for i in range(len(smaller_partition)):
            yield smaller_partition[:i] + [[first] + smaller_partition[i]] + smaller_partition[i+1:]
        yield [[first]] + smaller_partition




def varrange(terms: List[Term]) -> Iterator[Tuple[Substitution, Dict[str, int]]]: #Dictionary is the variable names (skolem constants) and their precdences
    #Generates all possible Skolemizing substitutions and orderings over the Skolem Constants
    variables = find_variables_from_terms(terms)
    
    var_list = sorted([v.name for v in variables]) #Sorts the variables
    for partition in generate_partitions(var_list):
        skolem_constants = []
        substitution: Substitution = {}
        for i, group in enumerate(partition):
            skolem_name = f"SK_{i}"
            skolem_term = Term(Variable(skolem_name))
            skolem_constants.append(skolem_name)

            for var in group:
                substitution[Variable(var)] = skolem_term 
        
        for permutation in itertools.permutations(skolem_constants):
            precedence = len(permutation)
            Skolemized_Variable_Order = {}
            for skolem_name in permutation:
                Skolemized_Variable_Order[Variable(skolem_name)] = precedence
                precedence -= 1
            yield (substitution, Skolemized_Variable_Order)

def merge_sorted_lists_with_ties(list1: list, list2: list):
    if not list1:
        yield [[x] for x in list2]
        return
    if not list2:
        yield [[x] for x in list1]
        return
    head1 = list1[0]
    head2 = list2[0]
    rest1 = list1[1:]
    rest2 = list2[1:]

    for tail in merge_sorted_lists_with_ties(rest1, list2):
        yield [[head1]] + tail

    for tail in merge_sorted_lists_with_ties(list1, rest2):
        yield [[head2]] + tail

    for tail in merge_sorted_lists_with_ties(rest1, rest2):
        yield [[head1, head2]] + tail

def generate_variable_constant_orderings(variable_order: Dict[Variable, int], constants: List[Term]):
    sorted_vars = sorted(variable_order.keys(), key=lambda v: variable_order[v], reverse = True)
    
    processed_constants = []
    for c in constants:
        if isinstance(c.root, Function_Symbol) and c.root.name == 'quote':
            processed_constants.append(c)
        else:
            processed_constants.append(c.root)

    def _get_sort_key(item):
        if isinstance(item, Term) and isinstance(item.root, Function_Symbol) and item.root.name == 'quote':
            inner = item.arguments[0]
            if hasattr(inner.root, 'value'):
                return inner.root.value
        return str(item)
        
    sorted_consts = sorted(processed_constants, key=_get_sort_key, reverse = True)

    for merged_buckets in merge_sorted_lists_with_ties(sorted_vars, sorted_consts):
        combined_order = {}
        current_rank = len(merged_buckets)
        for bucket in merged_buckets:
            for item in bucket:
                combined_order[item] = current_rank
            current_rank -= 1

    constraints = []

    for i in range(len(merged_buckets)):
        current_bucket = merged_buckets[i]
        ### Constraint A: All items in the same bucket are equal
        first_item = current_bucket[0]
        for other_item in current_bucket[1:]:
            constraints.append((first_item, "==", other_item))

        ### Constraint B: All items this bucket are greater than the items in the next bucket
        if i < len(merged_buckets) -1:
            next_bucket = merged_buckets[i+1]
            next_item = next_bucket[0]
            constraints.append((first_item, ">", next_item))

    yield combined_order, constraints
        

def find_constants_in_terms(terms: List[Term]) -> List[Term]:
    """Finds all unique QuoteIntegers, QuoteReals, and Constants in a list of terms."""
    constants = set()
    def _recurse(t):
        if isinstance(t.root, Function_Symbol) and t.root.name == 'quote':
            #if isinstance(t.arguments[0].root, (QuoteInteger, QuoteReal)):
            if not find_variables_from_terms([t]):
                constants.add(t)
            return
        if isinstance(t.root, Constant):
            constants.add(t)
            return
        for arg in t.arguments:
            _recurse(arg)
            
    for term in terms:
        _recurse(term)
    return list(constants)

def generate_search_space(terms: List[Term]) -> Iterator[Tuple[Substitution, Dict, List]]:
    """
    Generates the complete search space for static analysis.
    Yields: (substitution, combined_order, constraints)
    """
    # 1. Identify Variables and Constants
    variables = list(find_variables_from_terms(terms))
    constants = find_constants_in_terms(terms)
    
    # 2. Sort Constants (Fixed Order) - Logic adapted from generate_variable_constant_orderings
    def _get_sort_key(item):
        if isinstance(item, Term) and isinstance(item.root, Function_Symbol) and item.root.name == 'quote':
            inner = item.arguments[0]
            if hasattr(inner.root, 'value'): 
                return (0, inner.root.value) # Priority 0 for Numbers
        
        # Case 2: Literal Object -> QuoteInteger(1)
        if hasattr(item, 'value'): 
            return (0, item.value) # Priority 0 for Numbers
            
        # Case 3: Named Constant -> Constant("C")
        return (1, str(item)) # Priority 1 for Strings
    
    # Normalize constants to be consistent (Terms vs Roots)
    processed_constants = []
    for c in constants:
        if isinstance(c.root, Function_Symbol) and c.root.name == 'quote':
            processed_constants.append(c)
        else:
            processed_constants.append(c.root)
            
    sorted_consts = sorted(processed_constants, key=_get_sort_key, reverse=True)

    # 3. Iterate Partitions of Variables (Handling Equality: X = Y)
    var_names = sorted([v.name for v in variables])
    for partition in generate_partitions(var_names):
        
        # Build Substitution: Map all vars in a group to the same Skolem Constant
        substitution = {}
        skolem_vars = []
        for i, group in enumerate(partition):
            skolem_name = f"SK_{i}"
            skolem_var = Variable(skolem_name)
            skolem_term = Term(skolem_var)
            skolem_vars.append(skolem_var)
            for v_name in group:
                substitution[Variable(v_name)] = skolem_term
        
        # 4. Iterate Permutations of Skolem Vars (Handling Strict Order: SK_0 > SK_1)
        for skolem_perm in itertools.permutations(skolem_vars):
            # skolem_perm is a tuple of Variables in descending order
            
            # 5. Interleave with Constants (Handling: SK_0 > 1 > SK_1)
            # We treat the skolem permutation as a sorted list (descending)
            for merged_buckets in merge_sorted_lists_with_ties(list(skolem_perm), sorted_consts):
                
                # 6. Build Final Order and Constraints
                combined_order = {}
                constraints = []
                current_rank = len(merged_buckets)
                
                for i, bucket in enumerate(merged_buckets):
                    # Assign Rank
                    for item in bucket:
                        combined_order[item] = current_rank
                    
                    # Constraint A: Equality within bucket
                    first_item = bucket[0]
                    for other_item in bucket[1:]:
                        constraints.append((first_item, "==", other_item))
                    
                    # Constraint B: Inequality between buckets
                    if i < len(merged_buckets) - 1:
                        next_bucket = merged_buckets[i+1]
                        next_item = next_bucket[0]
                        constraints.append((first_item, ">", next_item))
                    
                    current_rank -= 1
                        
                yield substitution, combined_order, constraints

