import sympy
from sympy.logic.boolalg import to_cnf
from sympy.logic.boolalg import Or, And, Not
import itertools

def cnf(belief, newbelief):
    anded_formula = belief[0]
    not_new_belief = sympy.Not(newbelief)

    for formula in belief[1:]: 
        anded_formula = sympy.And(anded_formula,formula)

    full_belief = sympy.And(anded_formula,not_new_belief)

    cnfed_formula = sympy.to_cnf(full_belief)
    return cnfed_formula

def resolution(cnf_expression):
    clauses = set(cnf_expression.args if isinstance(cnf_expression, And) else [cnf_expression])
    original_clauses = clauses.copy()
    new_clauses = True

    while new_clauses:
        new_clauses = set()
        for clause1 in list(clauses):
            for clause2 in list(clauses):
                if clause1 is not clause2:
                    resolvent = resolve(clause1, clause2)
                    if resolvent is False:
                        print(f"Resolving {clause1} and {clause2} yields a contradiction.")
                        return False  # Indicate contradiction found
                    elif resolvent and resolvent not in clauses:
                        new_clauses.add(resolvent)
                        print(f"Resolving {clause1} and {clause2} yields {resolvent}.")

        if new_clauses:
            clauses.update(new_clauses)
        else:
            print("No new resolvents can be derived; resolution complete.")

    if sympy.false in clauses:
        print("The empty clause is derived; contradiction found.")
        return False
    else:
        print("No contradiction found; resolved clauses:")
        for clause in clauses - original_clauses:
            print(clause)
        return clauses  # Return all clauses if no contradiction is found


def resolve(clause1, clause2):
    literals1 = set(clause1.args if isinstance(clause1, Or) else [clause1])
    literals2 = set(clause2.args if isinstance(clause2, Or) else [clause2])

    for lit1 in literals1:
        for lit2 in literals2:
            if lit1 == ~lit2 or ~lit1 == lit2:  # Check for complementary literals
                new_literals = (literals1.union(literals2) - {lit1, lit2})
                if new_literals:
                    return Or(*new_literals)  # Return new clause formed by resolving the pair
                else:
                    return False  # Return False indicating an empty clause (contradiction)
    return None  # Return None if no resolution is possible

def check_implication(beliefs, formula):
    test_formula = sympy.And(*beliefs, sympy.Not(formula))
    contradiction_found = resolution(to_cnf(test_formula)) == False
    return contradiction_found  # True if 'beliefs' imply 'formula'

def find_remainder_sets(belief_base, phi):
    remainders = []
    # Generate all possible non-empty subsets of the belief base
    for r in range(1, len(belief_base) + 1):
        for subset in itertools.combinations(belief_base, r):
            if phi not in subset:  # Optionally check if phi is directly in the subset
                implies_phi = check_implication(subset, phi)
                print(f"Testing subset: {subset}")
                if not implies_phi:
                    print(f"Subset {subset} does NOT imply {phi}, adding to remainders.")
                    remainders.append(subset)
                else:
                    print(f"Subset {subset} implies {phi}, hence not a remainder.")
    print(f"Found {len(remainders)} valid remainder(s).")
    return remainders

def select_remainder_based_on_entrenchment(remainders, entrenchment):
    # Ensuring at least one remainder is selected if available
    max_entrenchment_value = -1
    selected_remainder = None
    for remainder in remainders:
        entrenchment_value = sum(entrenchment.get(belief, 0) for belief in remainder)
        if entrenchment_value > max_entrenchment_value:
            max_entrenchment_value = entrenchment_value
            selected_remainder = remainder
    return selected_remainder or []  # Return an empty list if no remainders are selected

# Update the contraction function to handle cases where no remainder is selected
def contract(belief_base, phi, entrenchment):
    remainders = find_remainder_sets(belief_base, phi)
    selected_remainder = select_remainder_based_on_entrenchment(remainders, entrenchment)
    return selected_remainder if selected_remainder is not None else belief_base

def revise_belief_base(belief_base, new_belief, entrenchment):
    """
    Expands the belief base by optionally contracting with the negation of the new belief
    and then adding the new belief to ensure consistency.
    """
    # Contract the belief base with the negation of the new belief to resolve potential inconsistencies
    negated_new_belief = sympy.Not(new_belief)
    contracted_base = contract(belief_base, negated_new_belief, entrenchment)
    
    contracted_base = list(contracted_base) 
    # Now add the new belief to the contracted belief base
    expanded_base = contracted_base + [new_belief]
    return expanded_base

# Following are tests for rationality postulates of contraction
def test_success_postulate(belief_base, phi, entrenchment):
    contracted_base = contract(belief_base, phi, entrenchment)
    print("Testing Success Postulate:")
    print(f"Belief Base after contracting {phi}: {contracted_base}")
    return phi not in contracted_base

def test_inclusion_postulate(belief_base, phi, entrenchment):
    contracted_base = contract(belief_base, phi, entrenchment)
    print("Testing Inclusion Postulate:")
    is_included = all(belief in belief_base for belief in contracted_base)
    print(f"Is every element in the contracted base also in the original base? {is_included}")
    return is_included

def test_vacuity_postulate(belief_base, phi, entrenchment):
    if not check_implication(belief_base, phi):  # Assume this checks if phi is a consequence of B
        contracted_base = contract(belief_base, phi, entrenchment)
        print("Testing Vacuity Postulate:")
        print(f"Contracted base when {phi} is not a consequence should be unchanged: {contracted_base}")
        vacuity = contracted_base == belief_base
        return vacuity
    return True  # Vacuity not applicable if phi is a consequence of B


def test_extensionality_postulate(belief_base, phi, psi, entrenchment):
    contracted_with_phi = contract(belief_base, phi, entrenchment)
    contracted_with_psi = contract(belief_base, psi, entrenchment)
    print("Testing Extensionality Postulate:")
    print(f"Contracted with {phi}: {contracted_with_phi}")
    print(f"Contracted with {psi}: {contracted_with_psi}")
    extentionality = contracted_with_phi == contracted_with_psi
    return extentionality

def test_success_postulate_revision(belief_base, phi, entrenchment):
    revised_base = revise_belief_base(belief_base, phi, entrenchment)
    success = phi in revised_base  # This check should be adjusted if revision outputs a formal expression.
    print(f"Testing Success Postulate for revision with {phi}: {'Passed' if success else 'Failed'}")
    return success

def test_inclusion_postulate_revision(belief_base, phi, entrenchment):
    revised_base = revise_belief_base(belief_base, phi, entrenchment)
    inclusion = set(revised_base).issubset(set(belief_base + [phi]))
    print(f"Testing Inclusion Postulate for revision with {phi}: {'Passed' if inclusion else 'Failed'}")
    return inclusion

def test_vacuity_postulate_revision(belief_base, phi, entrenchment):
    if check_implication(belief_base, Not(phi)):
        revised_base = revise_belief_base(belief_base, phi, entrenchment)
        vacuity = revised_base == belief_base
        print(f"Testing Vacuity Postulate for revision with {phi}: {'Passed' if vacuity else 'Failed'}")
        return vacuity
    print(f"Vacuity Postulate for revision not applicable as {phi} is not a consequence of B.")
    return True  # Consider it passed if phi is not a consequence of B

def test_consistency_postulate_revision(belief_base, phi, entrenchment):
    for belief in belief_base:
        # List of Every element in belief_base except from belief
        belief_base_minus_belief = [b for b in belief_base if b != belief]
        cnf_expression = cnf(belief_base_minus_belief, belief)
        resolution_result = resolution(cnf_expression)
        if resolution_result is True:
            print("The initial belief base was inconsistent.")
            return True
    
    revised_base = revise_belief_base(belief_base, phi, entrenchment)
    for belief in revised_base:
        revised_base_minus_belief = [b for b in revised_base if b != belief]
        cnf_expression = cnf(revised_base_minus_belief, belief)
        resolution_result = resolution(cnf_expression)
        if resolution_result is True:
            print("The revised belief base is inconsistent.")
            return False
    
    print("The revised belief base is consistent.")
    return True

def test_extensionality_postulate_revision(belief_base, phi, psi, entrenchment):
    revised_with_phi = revise_belief_base(belief_base, phi, entrenchment)
    revised_with_psi = revise_belief_base(belief_base, psi, entrenchment)
    extensionality = revised_with_phi == revised_with_psi
    print(f"Testing Extensionality Postulate for revision with {phi} and {psi}: {'Passed' if extensionality else 'Failed'}")
    return extensionality


if __name__ == '__main__':
    # Define inputs
    p, q, r, s = sympy.symbols('p q r s')
    initial_belief = [p, p & q, r]
    entrenchment = {p: 3, p & q: 2, r: 1}
    phi = p
    psi = Not(Not(phi))  # Logical equivalent to phi

    # Test Success Postulate
    if test_success_postulate(initial_belief, phi, entrenchment) == True:
        print("**********Success Postulate holds!")
    else:
        print("**********Success Postulate does not hold!")

    # Test Inclusion Postulate
    if test_inclusion_postulate(initial_belief, phi, entrenchment) == True:
        print("**********Inclusion Postulate holds!")
    else:
        print("**********Inclusion Postulate does not hold!")

    # Test Vacuity Postulate
    if test_vacuity_postulate(initial_belief, phi, entrenchment) == True:
        print("**********Vacuity Postulate holds!")
    else:
        print("**********Vacuity Postulate does not hold!")

    # Test Extensionality Postulate
    if test_extensionality_postulate(initial_belief, phi, psi, entrenchment) == True:
        print("**********Extensionality Postulate holds!")
    else:
        print("**********Extensionality Postulate does not hold!")

    # Test Success Postulate for revision
    if test_success_postulate_revision(initial_belief, phi, entrenchment) == True:
        print("**********Success Postulate for revision holds!")
    else:
        print("**********Success Postulate for revision does not hold!")

    # Test Inclusion Postulate for revision
    if test_inclusion_postulate_revision(initial_belief, phi, entrenchment) == True:
        print("**********Inclusion Postulate for revision holds!")
    else:
        print("**********Inclusion Postulate for revision does not hold!")

    # Test Vacuity Postulate for revision
    if test_vacuity_postulate_revision(initial_belief, phi, entrenchment) == True:
        print("**********Vacuity Postulate for revision holds!")
    else:
        print("**********Vacuity Postulate for revision does not hold!")

    # Test for Consistency Postulate for revision
    if test_consistency_postulate_revision(initial_belief, phi, entrenchment) == True:
        print("**********Consistency Postulate for revision holds!")
    else:
        print("**********Consistency Postulate for revision does not hold!")
    
    # Test Extensionality Postulate for revision
    if test_extensionality_postulate_revision(initial_belief, phi, psi, entrenchment) == True:
        print("**********Extensionality Postulate for revision holds!")
    else:
        print("**********Extensionality Postulate for revision does not hold!")
    
    
    ## Following code if you want to test CNF and resolution functions
    """
    full_cnf = cnf(initial_belief, new_belief=p) # Testing CNF
    print("FULL CNF; ", full_cnf)
    print(resolution(full_cnf))

    resolution_result = resolution(full_cnf) # Testing resolution

    if resolution_result is False: # Resolution returns false when there is found a contradiction
        print("Consistent!")
    else:
        print("Not Consistent!")
    """
    

