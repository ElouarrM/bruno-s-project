from flask import Flask, request, render_template, jsonify
from typing import List, Dict, Set, Tuple
from dataclasses import dataclass
import itertools

# ==== Définition des classes ====
@dataclass(frozen=True)
class Argument:
    support: frozenset
    claim: str

@dataclass
class ABAFramework:
    language: Set[str]
    rules: List[Tuple[str, List[str]]]
    assumptions: Set[str]
    contraries: Dict[str, str]
    preferences: List[Tuple[Set[str], Set[str]]]

# ==== Fonctions de parsing ====
def parse_aba_input(text: str) -> ABAFramework:
    lines = [line.strip() for line in text.strip().split('\n') if line.strip()]
    language, assumptions, contraries, rules, preferences = set(), set(), {}, [], []
    
    for line in lines:
        if line.startswith('L:'):
            lang_str = line.split(':', 1)[1].strip()
            language = set(s.strip() for s in lang_str.strip('[]').split(','))
        elif line.startswith('A:'):
            assump_str = line.split(':', 1)[1].strip()
            assumptions = set(s.strip() for s in assump_str.strip('[]').split(','))
        elif line.startswith('C('):
            parts = line.split(':')
            assumption = parts[0].strip()[2:-1]
            contrary = parts[1].strip()
            contraries[assumption] = contrary
        elif line.startswith('[') and ']:' in line:
            rule_name, rule_body = line.split(']:')
            head_body = rule_body.strip().split('<-')
            head = head_body[0].strip()
            body = [b.strip() for b in head_body[1].split(',')] if len(head_body) > 1 and head_body[1].strip() else []
            rules.append((head, body))
        elif line.startswith('PREF:'):
            pref_str = line.split(':', 1)[1].strip()
            parts = pref_str.split('>')
            if len(parts) == 2:
                preferred = set(p.strip() for p in parts[0].split(','))
                less_preferred = set(p.strip() for p in parts[1].split(','))
                preferences.append((preferred, less_preferred))
    
    return ABAFramework(language, rules, assumptions, contraries, preferences)

# ==== Conversion en framework atomique ====
def convert_to_atomic(framework: ABAFramework) -> ABAFramework:
    """
    Convertit un framework ABA en framework atomique selon Définition 24.
    Pour chaque s ∈ L\A, on introduit:
    - s_d (s is derivable)
    - s_nd (s is not derivable)
    avec contraires: s_d = s_nd et s_nd = s
    """
    new_language = framework.language.copy()
    new_assumptions = framework.assumptions.copy()
    new_contraries = framework.contraries.copy()
    new_rules = []
    
    # Pour chaque littéral non-hypothèse
    non_assumptions = framework.language - framework.assumptions
    
    for s in non_assumptions:
        # Ajouter les nouvelles hypothèses
        s_d = f"{s}_d"
        s_nd = f"{s}_nd"
        
        new_language.add(s_d)
        new_language.add(s_nd)
        new_assumptions.add(s_d)
        new_assumptions.add(s_nd)
        
        # Définir les contraires: s_d = s_nd et s_nd = s
        new_contraries[s_d] = s_nd
        new_contraries[s_nd] = s
    
    # Modifier les règles: remplacer les non-hypothèses par leurs versions _d
    for head, body in framework.rules:
        new_body = []
        for b in body:
            if b in non_assumptions:
                new_body.append(f"{b}_d")
            else:
                new_body.append(b)
        new_rules.append((head, new_body))
    
    return ABAFramework(
        new_language,
        new_rules,
        new_assumptions,
        new_contraries,
        framework.preferences
    )

# ==== Conversion en framework non-circulaire ====
def convert_to_non_circular(framework: ABAFramework) -> ABAFramework:
    """
    Convertit un framework ABA en framework non-circulaire selon Définition 31.
    Copie chaque règle k fois (k = |L\A|) avec des indices pour éviter les cycles.
    """
    k = len(framework.language - framework.assumptions)
    if k == 0:
        k = 1
    
    new_language = framework.language.copy()
    new_rules = []
    
    # Créer les nouvelles versions des littéraux non-hypothèses
    non_assumptions = framework.language - framework.assumptions
    for s in non_assumptions:
        for i in range(1, k + 1):
            if i < k:
                new_language.add(f"{s}_{i}")
    
    # Copier et adapter les règles
    for head, body in framework.rules:
        is_atomic = all(b in framework.assumptions for b in body)
        
        if is_atomic:
            # Règles atomiques : k copies
            for i in range(1, k + 1):
                if i < k:
                    new_head = f"{head}_{i}" if head not in framework.assumptions else head
                else:
                    new_head = head
                new_rules.append((new_head, body))
        else:
            # Règles non-atomiques : k-1 copies
            for j in range(2, k + 1):
                new_head = f"{head}_{j}" if j < k else head
                new_body = []
                for b in body:
                    if b in framework.assumptions:
                        new_body.append(b)
                    else:
                        new_body.append(f"{b}_{j-1}")
                new_rules.append((new_head, new_body))
    
    return ABAFramework(
        new_language,
        new_rules,
        framework.assumptions,
        framework.contraries,
        framework.preferences
    )

# ==== Vérification de circularité ====
def is_circular(framework: ABAFramework) -> bool:
    """Vérifie si le framework contient des dépendances circulaires"""
    # Construire un graphe de dépendances
    graph = {literal: set() for literal in framework.language}
    
    for head, body in framework.rules:
        for b in body:
            if b in graph and head in graph:
                graph[b].add(head)
    
    # Détection de cycle par DFS
    def has_cycle_dfs(node, visited, rec_stack):
        visited.add(node)
        rec_stack.add(node)
        
        for neighbor in graph.get(node, []):
            if neighbor not in visited:
                if has_cycle_dfs(neighbor, visited, rec_stack):
                    return True
            elif neighbor in rec_stack:
                return True
        
        rec_stack.discard(node)
        return False
    
    visited = set()
    for node in graph:
        if node not in visited:
            if has_cycle_dfs(node, visited, set()):
                return True
    
    return False

# ==== Génération des arguments ====
def generate_arguments(framework: ABAFramework) -> Set[Argument]:
    arguments = set()
    
    # Arguments triviaux
    for a in framework.assumptions:
        arguments.add(Argument(support=frozenset([a]), claim=a))
    
    changed = True
    max_iterations = 100
    iteration = 0
    
    while changed and iteration < max_iterations:
        changed = False
        iteration += 1
        new_args = set()
        
        for head, body in framework.rules:
            if not body:
                arg = Argument(support=frozenset([]), claim=head)
                if arg not in arguments:
                    new_args.add(arg)
                    changed = True
            else:
                combos = find_argument_combinations(body, arguments)
                for supp in combos:
                    arg = Argument(support=supp, claim=head)
                    if arg not in arguments and arg not in new_args:
                        new_args.add(arg)
                        changed = True
        
        arguments.update(new_args)
    
    return arguments

def find_argument_combinations(body: List[str], arguments: Set[Argument]) -> Set[frozenset]:
    if not body:
        return {frozenset()}
    
    lists = []
    for b in body:
        matching_args = [arg for arg in arguments if arg.claim == b]
        if not matching_args:
            return set()
        lists.append(matching_args)
    
    combos = set()
    for args_tuple in itertools.product(*lists):
        combined = set()
        for arg in args_tuple:
            combined.update(arg.support)
        combos.add(frozenset(combined))
    
    return combos

# ==== Calcul des attaques ====
def compute_attacks(arguments: Set[Argument], framework: ABAFramework) -> Set[Tuple[Argument, Argument]]:
    attacks = set()
    for a1 in arguments:
        for a2 in arguments:
            for assumption in a2.support:
                if assumption in framework.contraries and a1.claim == framework.contraries[assumption]:
                    attacks.add((a1, a2))
                    break
    return attacks

def is_preferred(supp1: frozenset, supp2: frozenset, preferences: List[Tuple[Set[str], Set[str]]]) -> bool:
    for preferred, less in preferences:
        if supp1 & preferred and supp2 & less:
            return True
    return False

def compute_preference_attacks(arguments: Set[Argument], framework: ABAFramework, normal_attacks: Set[Tuple[Argument, Argument]]):
    normal, reverse = set(), set()
    
    for (a1, a2) in normal_attacks:
        attacker_preferred = is_preferred(a1.support, a2.support, framework.preferences)
        attacked_preferred = is_preferred(a2.support, a1.support, framework.preferences)
        
        if attacked_preferred and not attacker_preferred:
            reverse.add((a2, a1))
        else:
            normal.add((a1, a2))
    
    return normal, reverse

# ==== Application Flask ====
app = Flask(__name__)

@app.route('/')
def index():
    return render_template('index.html')

@app.route('/generate', methods=['POST'])
def generate_aba():
    try:
        input_text = request.form['aba_input']
        apply_atomic = request.form.get('apply_atomic', 'false') == 'true'
        apply_non_circular = request.form.get('apply_non_circular', 'false') == 'true'
        
        print(f"DEBUG: apply_atomic = {apply_atomic}")
        print(f"DEBUG: apply_non_circular = {apply_non_circular}")
        
        # Parser le framework original
        original_framework = parse_aba_input(input_text)
        framework = original_framework
        
        transformations_applied = []
        
        # Appliquer les transformations
        if apply_non_circular:
            circular = is_circular(framework)
            if circular:
                framework = convert_to_non_circular(framework)
                transformations_applied.append("Non-circular conversion applied (framework was circular)")
            else:
                transformations_applied.append("Non-circular conversion checked (framework already non-circular)")
        
        if apply_atomic:
            framework = convert_to_atomic(framework)
            transformations_applied.append("Atomic conversion applied")
        
        # ... reste du code

        
        # Générer les arguments et attaques
        arguments = generate_arguments(framework)
        attacks = compute_attacks(arguments, framework)
        normal_attacks, reverse_attacks = compute_preference_attacks(arguments, framework, attacks)
        
        result = {
            'original_framework': {
                'language': sorted(list(original_framework.language)),
                'assumptions': sorted(list(original_framework.assumptions)),
                'contraries': original_framework.contraries,
                'rules_count': len(original_framework.rules)
            },
            'transformed_framework': {
                'language': sorted(list(framework.language)),
                'assumptions': sorted(list(framework.assumptions)),
                'contraries': framework.contraries,
                'rules_count': len(framework.rules),
                'is_atomic': all(all(b in framework.assumptions for b in body) for head, body in framework.rules if body)
            },
            'transformations_applied': transformations_applied,
            'arguments': [
                {'support': sorted(list(a.support)), 'claim': a.claim} 
                for a in sorted(arguments, key=lambda x: (x.claim, len(x.support)))
            ],
            'attacks': {
                'normal': [
                    {
                        'attacker': {'support': sorted(list(a.support)), 'claim': a.claim},
                        'attacked': {'support': sorted(list(b.support)), 'claim': b.claim}
                    }
                    for a, b in normal_attacks
                ],
                'reverse': [
                    {
                        'attacker': {'support': sorted(list(a.support)), 'claim': a.claim},
                        'attacked': {'support': sorted(list(b.support)), 'claim': b.claim}
                    }
                    for a, b in reverse_attacks
                ]
            },
            'statistics': {
                'total_arguments': len(arguments),
                'total_normal_attacks': len(normal_attacks),
                'total_reverse_attacks': len(reverse_attacks)
            }
        }
        
        return jsonify(result)
        
    except Exception as e:
        import traceback
        return jsonify({
            'error': str(e),
            'traceback': traceback.format_exc()
        }), 400

if __name__ == '__main__':
    app.run(debug=True, port=5000)
