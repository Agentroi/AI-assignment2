import sympy
from sympy.logic.boolalg import to_cnf
from sympy.logic.boolalg import Or, And, Not, Equivalent, Implies
import itertools

def cnf(belief, newbelief):
    """
    CNF conversion of the belief base with the new belief, uses sympy to convert to CNF.
    """
    if belief == []:
        return sympy.to_cnf(newbelief)
    else:
        anded_formula = belief[0]
        not_new_belief = sympy.Not(newbelief)

        for formula in belief[1:]: 
            anded_formula = sympy.And(anded_formula,formula)

        full_belief = sympy.And(anded_formula,not_new_belief)

        cnfed_formula = sympy.to_cnf(full_belief)
        return cnfed_formula

def resolution(cnf_expression):
    """
    Resolution algorithm to check for contradictions in the CNF expression.
    """
    clauses = set(cnf_expression.args if isinstance(cnf_expression, And) else [cnf_expression])
    new_clauses = True

    while new_clauses: # Repeat until no new clauses are generated
        new_clauses = set()
        for clause1 in list(clauses):
            for clause2 in list(clauses):
                if clause1 is not clause2:
                    resolvent = resolve(clause1, clause2)
                    if resolvent is False:
                        return False  # Indicate contradiction found
                    elif resolvent and resolvent not in clauses:
                        new_clauses.add(resolvent)

        if new_clauses:
            clauses.update(new_clauses)
        else:
            break

    if sympy.false in clauses:
        return False
    else:
        return clauses  # Return all clauses if no contradiction is found


def resolve(clause1, clause2):
    """
    Helper function to resolve two clauses.
    """
    literals1 = set(clause1.args if isinstance(clause1, Or) else [clause1])
    literals2 = set(clause2.args if isinstance(clause2, Or) else [clause2])

    for lit1 in literals1: # Iterate over all literals in clause1
        for lit2 in literals2:
            if lit1 == ~lit2 or ~lit1 == lit2:  # Check for complementary literals
                new_literals = (literals1.union(literals2) - {lit1, lit2})
                if new_literals:
                    return Or(*new_literals)  # Return new clause formed by resolving the pair
                else:
                    return False  # Return False indicating an empty clause (contradiction)
    return None  # Return None if no resolution is possible

def check_implication(beliefs, formula):
    """
    Check if the given beliefs imply the given formula.
    """
    test_formula = sympy.And(*beliefs, sympy.Not(formula))
    contradiction_found = resolution(to_cnf(test_formula)) == False
    return contradiction_found 

def find_remainder_sets(belief_base, phi):
    """
    Find all possible remainders of the belief base with respect to the new belief.
    """
    remainders = []
    # Generate all possible non-empty subsets of the belief base
    for r in range(1, len(belief_base) + 1):
        for subset in itertools.combinations(belief_base, r):
            if phi not in subset: 
                implies_phi = check_implication(subset, phi)
                if not implies_phi:
                    remainders.append(subset)
    return remainders

def select_remainder_based_on_entrenchment(remainders, entrenchment):
    """
    Select the remainder with the highest entrenchment value based on the given entrenchment function.
    """
    # Ensuring at least one remainder is selected if available
    max_entrenchment_value = -1
    selected_remainder = None
    for remainder in remainders:
        entrenchment_value = sum(entrenchment.get(belief, 0) for belief in remainder)
        if entrenchment_value > max_entrenchment_value:
            max_entrenchment_value = entrenchment_value
            selected_remainder = remainder
    return selected_remainder or []  # Return an empty list if no remainders are selected

def contract(belief_base, phi, entrenchment):
    """
    Contract the belief base with the negation of the new belief to ensure consistency.
    """
    remainders = find_remainder_sets(belief_base, phi)
    selected_remainder = select_remainder_based_on_entrenchment(remainders, entrenchment)
    return selected_remainder if selected_remainder is not None else belief_base

def revise_belief_base(belief_base, new_belief, new_priority, entrenchment):
    """
    Expands the belief base by optionally contracting with the negation of the new belief
    and then adding the new belief to ensure consistency.
    """
    # Contract the belief base with the negation of the new belief to resolve potential inconsistencies
    negated_new_belief = sympy.Not(new_belief)
    contracted_base = contract(list(belief_base.keys()), negated_new_belief, entrenchment)
    
    contracted_base = {belief: belief_base.get(belief, 0) for belief in contracted_base}
    # Now add the new belief to the contracted belief base
    contracted_base[new_belief] = new_priority
    return contracted_base # Return the revised belief base

### AGM Postulate Tests ###
def test_success_postulate(belief_base, phi, entrenchment):
    """
    Test the success postulate for belief contraction.
    """
    contracted_base = contract(belief_base, phi, entrenchment)
    return phi not in contracted_base

def test_inclusion_postulate(belief_base, phi, entrenchment):
    """
    Test the inclusion postulate for belief contraction.
    """
    contracted_base = contract(belief_base, phi, entrenchment)
    is_included = all(belief in belief_base for belief in contracted_base)
    return is_included

def test_vacuity_postulate(belief_base, phi, entrenchment):
    """
    Test the vacuity postulate for belief contraction.
    """
    if check_implication(belief_base, Not(phi)):  
        contracted_base = contract(belief_base, phi, entrenchment)
        vacuity = contracted_base == belief_base
        return vacuity
    return True

def test_extensionality_postulate(belief_base, phi, psi, entrenchment):
    """
    Test the extensionality postulate for belief contraction.
    """
    contracted_with_phi = contract(belief_base, phi, entrenchment)
    contracted_with_psi = contract(belief_base, psi, entrenchment)
    extentionality = contracted_with_phi == contracted_with_psi
    return extentionality

def test_success_postulate_revision(belief_base, phi, priority, entrenchment):
    """
    Test the success postulate for belief revision.
    """
    revised_base = revise_belief_base(belief_base, phi, priority, entrenchment)
    success = phi in revised_base 
    return success

def test_inclusion_postulate_revision(belief_base, phi, priority, entrenchment):
    """
    Test the inclusion postulate for belief revision.
    """
    revised_base = revise_belief_base(belief_base, phi, priority, entrenchment)
    original_beliefs_plus_new = set(belief_base.keys() | {phi})
    inclusion = set(revised_base.keys()).issubset(original_beliefs_plus_new)
    return inclusion

def test_vacuity_postulate_revision(belief_base, phi, priority, entrenchment):
    """
    Test the vacuity postulate for belief revision.
    """
    if check_implication(belief_base, Not(phi)):
        revised_base = revise_belief_base(belief_base, phi, priority, entrenchment)
        vacuity = revised_base == belief_base
        return vacuity
    return True 

def test_consistency_postulate_revision(belief_base, phi, priority, entrenchment):
    """
    Test the consistency postulate for belief revision.
    """
    for belief in belief_base:
        # List of Every element in belief_base except from belief
        belief_base_minus_belief = [b for b in belief_base if b != belief]
        cnf_expression = cnf(belief_base_minus_belief, belief)
        resolution_result = resolution(cnf_expression)
        if resolution_result is True:
            print("The initial belief base was inconsistent.")
            return True
    
    revised_base = revise_belief_base(belief_base, phi, priority, entrenchment)
    for belief in revised_base:
        revised_base_minus_belief = [b for b in revised_base if b != belief]
        cnf_expression = cnf(revised_base_minus_belief, belief)
        resolution_result = resolution(cnf_expression)
        if resolution_result is True:
            return False
        
    return True

def test_extensionality_postulate_revision(belief_base, phi, psi, priority, entrenchment):
    """
    Test the extensionality postulate for belief revision.
    """
    revised_with_phi = revise_belief_base(belief_base, phi, priority, entrenchment)
    revised_with_psi = revise_belief_base(belief_base, psi, priority, entrenchment)
    extensionality = revised_with_phi == revised_with_psi
    return extensionality

def run_contraction_tests(belief_base, phi, entrenchment):
    """
    Run the postulate tests for belief contraction.
    """
    print("Running contraction tests...")
    if test_success_postulate(belief_base, phi, entrenchment):
        print("Success Postulate holds!")
    else:
        print("Success Postulate does not hold!")

    if test_inclusion_postulate(belief_base, phi, entrenchment):
        print("Inclusion Postulate holds!")
    else:
        print("Inclusion Postulate does not hold!")

    if test_vacuity_postulate(belief_base, phi, entrenchment):
        print("Vacuity Postulate holds!")
    else:
        print("Vacuity Postulate does not hold!")

    if test_extensionality_postulate(belief_base, phi, Not(Not(phi)), entrenchment): 
        print("Extensionality Postulate holds!")
    else:
        print("Extensionality Postulate does not hold!")

def run_revision_tests(belief_base, phi, new_priority, entrenchment):
    """
    Run the postulate tests for belief revision.
    """
    print("Running revision tests...")
    if test_success_postulate_revision(belief_base, phi, new_priority, entrenchment):
        print("Success Postulate for revision holds!")
    else:
        print("Success Postulate for revision does not hold!")

    if test_inclusion_postulate_revision(belief_base, phi, new_priority, entrenchment):
        print("Inclusion Postulate for revision holds!")
    else:
        print("Inclusion Postulate for revision does not hold!")

    if test_vacuity_postulate_revision(belief_base, phi, new_priority, entrenchment):
        print("Vacuity Postulate for revision holds!")
    else:
        print("Vacuity Postulate for revision does not hold!")

    if test_consistency_postulate_revision(belief_base, phi, new_priority, entrenchment):
        print("Consistency Postulate for revision holds!")
    else:
        print("Consistency Postulate for revision does not hold!")

    if test_extensionality_postulate_revision(belief_base, phi, Not(Not(phi)), new_priority, entrenchment):
        print("Extensionality Postulate for revision holds!")
    else:
        print("Extensionality Postulate for revision does not hold!")


def parse_formula(input_str):
    "Function to parse the input string into a sympy formula."
    return sympy.sympify(input_str)

def user_interface():
    belief_base = {}

    print("Welcome to the Belief Revision Agent!")
    print("Please use the following syntax: 'p & q' for 'p AND q', 'p | q' for 'p OR q', and '~p' for 'NOT p'.")
    print("For equivalance, use Equvialent(p,q) and for implication, use p >> q")
    print("Please initialize your belief base. Enter beliefs and their priorities (enter 'done' when finished):")

    while True:
        belief_input = input("Enter a belief (syntax: 'p & q') or 'done': ")
        if belief_input == 'done':
            break
        priority_input = int(input("Enter the priority for this belief: "))
        belief_base[parse_formula(belief_input)] = priority_input
    
    entrenchment = {belief: priority for belief, priority in belief_base.items()}

    while True:
        # Display the current belief base:
        print("\nCurrent belief base:")
        if belief_base == {}:
            print("The belief base is empty.")
        else:
            for belief, priority in belief_base.items():
                print(f"{belief} (Priority: {priority})")

        print("\nSelect an action:")
        print("1. Add a new belief to the belief base")
        print("2. Perform a resolution on the belief base")
        print("3. Contract a belief from the belief base")
        print("4. Revise the belief base")
        print("5. Exit")

        choice = input("Enter your choice (1-5): ")

        if choice == '1': 
            new_belief = parse_formula(input("Enter a new belief to add: "))
            if new_belief in belief_base:
                print(f"The belief {belief_base} already exists in the belief base.")
            else:
                new_priority = int(input("Enter the priority for this new belief: "))
                belief_base[new_belief] = new_priority
                print(f"New belief '{new_belief}' added to the belief base with priority {new_priority}.")
            continue

        elif choice == '2':
            new_belief = parse_formula(input("Enter a new belief to perform resolution with: "))
            cnf_expression = cnf(list(belief_base.keys()), new_belief)
            resolution_result = resolution(cnf_expression)
            if resolution_result is False:
                print(f"Resolution with {new_belief} is complete. The belief base is consistent.")
            else:
                print(f"Resolution with {new_belief} is complete. The belief base is inconsistent.")

        elif choice == '3':
            if not belief_base:
                print("Contraction cannot be performed on an empty belief base.")
            else:
                phi = parse_formula(input("Enter a belief to contract: "))
                if phi not in belief_base:
                    print("The belief to contract is not in the belief base.")
                    continue
                contracted_belief_base = contract(list(belief_base.keys()), phi, entrenchment)
                belief_base = {belief: belief_base.get(belief, 0) for belief in contracted_belief_base}
                print("Operation complete.")
                run_contraction_tests(belief_base, phi, entrenchment)  # Run contraction tests
                continue 
        
        elif choice == '4':
                new_belief = parse_formula(input("Enter a new belief to revise the belief base: "))
                new_priority = int(input("Enter the priority for this new belief: "))
                belief_base = revise_belief_base(belief_base, new_belief, new_priority, entrenchment)
                print("Operation complete.")
                run_revision_tests(belief_base, new_belief, new_priority, entrenchment)  # Run revision tests
                continue 

        elif choice == '5':
            print("Exiting the system.")
            break
        else:
            print("Invalid choice. Please try again.")
            continue

if __name__ == '__main__':
    user_interface()
