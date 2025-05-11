import time
import copy
UNASSIGNED = -1
FALSE = 0
TRUE = 1

def citeste_formula(nume_fisier):
    formula = []
    with open(nume_fisier, 'r') as f:
        for linie in f:
            clauza = list(map(int, linie.strip().split()))
            clauza = [lit for lit in clauza if lit != 0]
            if clauza:
                formula.append(set(clauza))
    return formula

def simple_var_strategy(assignment, clauses):
    """Alege prima variabilă neatribuită."""
    for clause in clauses:
        for lit in clause:
            var = abs(lit)
            if assignment[var] == UNASSIGNED:
                return var
    return None

def propagate(assignment, clauses, watchers, watch_list, literal_assigned):
    to_propagate = [literal_assigned]

    while to_propagate:
        lit = to_propagate.pop()

        for clause_idx in list(watch_list.get(-lit, [])):
            clause = clauses[clause_idx]
            found_new_watch = False

            for l in clause:
                var = abs(l)
                val = assignment[var]
                if (l > 0 and val != FALSE) or (l < 0 and val != TRUE):
                    watchers[clause_idx].remove(-lit)
                    watchers[clause_idx].append(l)
                    watch_list.setdefault(l, set()).add(clause_idx)
                    watch_list[-lit].remove(clause_idx)
                    found_new_watch = True
                    break

            if not found_new_watch:
                satisfied = False
                for l in clause:
                    var = abs(l)
                    val = assignment[var]
                    if (l > 0 and val == TRUE) or (l < 0 and val == FALSE):
                        satisfied = True
                        break
                if not satisfied:
                    return False

    return True

# ======= DPLL CU TWO-WATCHED LITERALS =======
def dpll(assignment, level, clauses, var_strategy, watchers, watch_list, steps=0):
    var_to_assign = var_strategy(assignment, clauses)
    if var_to_assign is None:
        for clause in clauses:
            is_clause_satisfied = False
            for lit_in_clause in clause:
                var_of_lit = abs(lit_in_clause)
                val_of_var = assignment[var_of_lit]
                if (lit_in_clause > 0 and val_of_var == TRUE) or \
                        (lit_in_clause < 0 and val_of_var == FALSE):
                    is_clause_satisfied = True
                    break
            if not is_clause_satisfied:
                return False, steps
        return True, steps
    for value_to_try in (TRUE, FALSE):
        original_assignment_copy = assignment[:]
        watchers_copy = {k: list(v) for k, v in watchers.items()}
        watch_list_copy = {k: set(v) for k, v in watch_list.items()}
        assignment[var_to_assign] = value_to_try
        lit_that_was_assigned = var_to_assign if value_to_try == TRUE else -var_to_assign

        if propagate(assignment, clauses, watchers, watch_list, lit_that_was_assigned):

            result, step_count = dpll(assignment, level + 1, clauses, var_strategy, watchers, watch_list, steps + 1)
            steps = step_count
            if result:
                return True, steps
            else:

                steps += 1
        assignment[:] = original_assignment_copy
        watchers.clear()
        watchers.update(watchers_copy)
        watch_list.clear()
        watch_list.update(watch_list_copy)

    return False, steps

# ======= REZOLUTIE SIMPLA =======
def rezolva(c1, c2):
    """Generează toate rezolventele posibile pentru două clauze."""
    rezolvante = set()
    for lit in c1:
        if -lit in c2:
            rez = (c1 | c2) - {lit, -lit}
            rezolvante.add(frozenset(rez))
    return rezolvante

def rezolutie(formula):
    """Algoritm de rezoluție."""
    formula = [frozenset(c) for c in formula]
    cunoscut = set(formula)
    pasi = 0

    while True:
        new = set()
        pairs = [(ci, cj) for i, ci in enumerate(formula) for j, cj in enumerate(formula) if i < j]
        pasi += len(pairs)

        for (ci, cj) in pairs:
            rezolvante = rezolva(ci, cj)
            if frozenset() in rezolvante:
                return False, pasi
            new.update(rezolvante)

        if new.issubset(cunoscut):
            return True, pasi

        formula.extend(new - cunoscut)
        cunoscut.update(new)

# ======= DP =======
def dp(formula):
    """Implementare Davis-Putnam simplificată."""
    formula = [frozenset(c) for c in formula]
    pasi = 0

    while True:
        if not formula:
            return True, pasi
        if any(not clauza for clauza in formula):
            return False, pasi

        toate_literalurile = {lit for clauza in formula for lit in clauza}
        if not toate_literalurile:
            return True, pasi

        lit = next(iter(toate_literalurile))

        clauze_cu_lit = [c for c in formula if lit in c]
        clauze_cu_neg = [c for c in formula if -lit in c]

        noi_clauze = set()
        for c1 in clauze_cu_lit:
            for c2 in clauze_cu_neg:
                rez = (c1 | c2) - {lit, -lit}
                noi_clauze.add(frozenset(rez))
                pasi += 1

        formula = [c for c in formula if lit not in c and -lit not in c]
        formula.extend(noi_clauze)

# ======= MAIN =======
if __name__ == "__main__":
    formula_originala = citeste_formula('clauze.txt')


    print("\n------ Rezoluție ------")
    start_time = time.time()
    rezultat, pasi = rezolutie(copy.deepcopy(formula_originala))
    timp_exec = time.time() - start_time
    print("SATISFIABIL" if rezultat else "NESATISFIABIL")
    print(f"Timp execuție: {timp_exec:.6f} secunde")
    print(f"Număr de pași: {pasi}")

    print("\n------ DPLL ------")
    num_vars = max(abs(lit) for clause in formula_originala for lit in clause)
    assignment = [UNASSIGNED] * (num_vars + 1)
    watchers = {i: [] for i in range(len(formula_originala))}
    watch_list = {}

    for idx, clause in enumerate(formula_originala):
        lits = list(clause)
        if len(lits) >= 2:
            watchers[idx] = [lits[0], lits[1]]
            watch_list.setdefault(lits[0], set()).add(idx)
            watch_list.setdefault(lits[1], set()).add(idx)
        elif len(lits) == 1:
            watchers[idx] = [lits[0]]
            watch_list.setdefault(lits[0], set()).add(idx)

    start_time = time.time()
    rezultat, pasi = dpll(assignment, 0, formula_originala, simple_var_strategy, watchers, watch_list, steps=0)
    timp_exec = time.time() - start_time
    print("SATISFIABIL" if rezultat else "NESATISFIABIL")
    print(f"Timp execuție: {timp_exec:.6f} secunde")
    print(f"Număr de pași: {pasi}")
    print("\n------ DP ------")
    start_time = time.time()
    rezultat, pasi = dp(copy.deepcopy(formula_originala))
    timp_exec = time.time() - start_time
    print("SATISFIABIL" if rezultat else "NESATISFIABIL")
    print(f"Timp execuție: {timp_exec:.6f} secunde")
    print(f"Număr de pași: {pasi}")
