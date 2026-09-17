"""生成竞赛图 SAT 证书，并将 RUP 推理展开成普通 Lean 证明。

SAT 求解器与本生成器均不属于逻辑信任基础；最终以 Lean 检查为准。
"""

from __future__ import annotations

import argparse
import itertools
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CACHE = ROOT / '.research-cache' / 'certificates'
OUT = ROOT / 'SunPrize' / 'Certificates'


def disjunction(expressions: list[str]) -> str:
    return ' ∨ '.join([*expressions, 'False'])


def conjunction(expressions: list[str]) -> str:
    return ' ∧ '.join([*expressions, 'True'])


def inject(position: int, proof: str) -> str:
    result = f'(Or.inl {proof})'
    for _ in range(position):
        result = f'(Or.inr {result})'
    return result


def build_problem(n: int, k: int):
    pairs = list(itertools.combinations(range(n), 2))
    triples = list(itertools.combinations(range(n), 3))
    edges = {pair: i + 1 for i, pair in enumerate(pairs)}
    cycles = {triple: len(edges) + i + 1 for i, triple in enumerate(triples)}
    atoms = {variable: f'(g {a} {b} = true)' for (a, b), variable in edges.items()}
    atoms.update({variable: f'(cyclic g {a} {b} {c})' for (a, b, c), variable in cycles.items()})
    clauses: list[list[int]] = []
    proofs: dict[int, str] = {}

    def add(clause: list[int], proof: str):
        clauses.append(clause)
        proofs[len(clauses)] = proof

    for a, b, c in triples:
        variables = [edges[a, b], edges[b, c], edges[a, c], cycles[a, b, c]]
        for index, (ab, bc, ac) in enumerate(itertools.product([False, True], repeat=3)):
            cycle = ab == bc and ab != ac
            values = [ab, bc, ac, not cycle]
            clause = [-v if value else v for v, value in zip(variables, values)]
            add(clause, f'by exact cycleClause{index} (g {a} {b}) (g {b} {c}) (g {a} {c})')
    for subset in itertools.combinations(range(n), k):
        clause = [cycles[t] for t in itertools.combinations(subset, 3)]
        bounds = ['(by decide)'] * k
        add(clause, 'by exact obstruction ' + ' '.join(map(str, subset)) + ' ' + ' '.join(bounds))
    return edges, atoms, clauses, proofs, add


def literal(atoms: dict[int, str], signed: int) -> str:
    proposition = atoms[abs(signed)]
    return proposition if signed > 0 else f'¬ {proposition}'


def eliminate(clause: list[int], evidence: str, established: dict[int, str], goal: int | None) -> str:
    """在一条析取上分类，利用已知的反面消去所有非目标文字。"""
    if not clause:
        return evidence if goal is None else f'(False.elim {evidence})'
    first, *rest = clause
    if first == goal:
        left = 'current'
    else:
        contradiction = f'({established[-first]} current)' if first > 0 else f'(current {established[-first]})'
        left = contradiction if goal is None else f'(False.elim {contradiction})'
    right = eliminate(rest, 'remaining', established, goal)
    return f'(Or.elim {evidence} (fun current => {left}) (fun remaining => {right}))'


def read_lrat(path: Path, original: list[list[int]]):
    database = {i + 1: clause for i, clause in enumerate(original)}
    steps = {}
    final = None
    for line in path.read_text().splitlines():
        words = line.split()
        if not words or words[1] == 'd':
            continue
        row = list(map(int, words))
        stop = row.index(0)
        ident, clause, hints = row[0], row[1:stop], row[stop + 1:-1]
        if any(hint <= 0 for hint in hints):
            raise ValueError('本生成器只接受正向 RUP 提示')
        database[ident] = clause
        steps[ident] = hints
        if not clause:
            final = ident
            break
    if final is None:
        raise ValueError('证书未推出空子句')
    needed = {final}
    stack = [final]
    while stack:
        for dependency in steps.get(stack.pop(), []):
            if dependency not in needed:
                needed.add(dependency)
                stack.append(dependency)
    return database, steps, needed, final


def emit(name, atoms, clauses, initial_proofs, extra, binders, lean, imported='SunPrize.Basic'):
    CACHE.mkdir(parents=True, exist_ok=True)
    OUT.mkdir(parents=True, exist_ok=True)
    cnf_path = CACHE / f'{name}.cnf'
    lrat_path = CACHE / f'{name}.lrat'
    cnf_path.write_text(f'p cnf {len(atoms)} {len(clauses)}\n' + ''.join(' '.join(map(str, c)) + ' 0\n' for c in clauses))
    solver = lean.with_name('cadical' + lean.suffix)
    run = subprocess.run([str(solver), '-q', '--lrat', '--no-binary', str(cnf_path), str(lrat_path)], capture_output=True, text=True, timeout=180)
    if run.returncode != 20:
        raise RuntimeError(run.stdout + run.stderr)
    database, steps, needed, final = read_lrat(lrat_path, clauses)
    arguments = 'g obstruction normal'
    imports = f'import {imported}\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option linter.unusedVariables false\n\nnamespace SunPrize\n\n'
    chunks = [imports, extra]
    for ident in sorted(needed):
        clause = database[ident]
        result_type = disjunction([literal(atoms, item) for item in clause])
        chunks.append(f'private theorem step{ident} {binders} : {result_type} := ')
        if ident not in steps:
            chunks.append(initial_proofs[ident] + '\n\n')
            continue
        chunks.append('by\n  apply Classical.byContradiction\n  intro denied\n')
        established = {}
        for position, item in enumerate(clause):
            chunks.append(f'  have absent{position} : ¬ ({literal(atoms, item)}) := fun present => denied {inject(position, "present")}\n')
            established[-item] = f'absent{position}' if item > 0 else f'(Classical.not_not.mp absent{position})'
        finished = False
        for position, hint in enumerate(steps[ident]):
            premise = database[hint]
            if any(item in established for item in premise):
                raise ValueError(f'提示已满足：{ident}/{hint}')
            unassigned = [item for item in premise if -item not in established]
            if len(unassigned) > 1:
                raise ValueError(f'提示不是单元传播：{ident}/{hint}')
            reference = f'(step{hint} {arguments})'
            if not unassigned:
                chunks.append('  exact ' + eliminate(premise, reference, established, None) + '\n\n')
                finished = True
                break
            item = unassigned[0]
            chunks.append(f'  have propagated{position} : {literal(atoms, item)} := ' + eliminate(premise, reference, established, item) + '\n')
            established[item] = f'propagated{position}'
        if not finished:
            raise ValueError(f'未推出矛盾：{ident}')
    chunks.append(f'theorem {name} {binders} : False := step{final} {arguments}\n\n#print axioms {name}\n\nend SunPrize\n')
    destination = OUT / f'{name}.lean'
    destination.write_text(''.join(chunks), encoding='utf-8')
    print(name, '原始子句', len(clauses), '保留推理', len(needed), '源文件字节', destination.stat().st_size, flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--lean', type=Path, required=True)
    parser.add_argument('--only', choices=['seven','fifteen','both'], default='both')
    args = parser.parse_args()
    if args.only in ['seven','both']:
        edges, atoms, clauses, proofs, add = build_problem(7,4)
        pairs = list(edges)
        representatives = {}
        for permutation in itertools.permutations(range(7)):
            code = sum(1 << i for i,(a,b) in enumerate(pairs) if (permutation[b]-permutation[a])%7 in (1,2,4))
            representatives.setdefault(code, permutation)
        rows = sorted(representatives.items())
        if len(rows) != 240:
            raise ValueError('佩利竞赛图的不同编号应恰好有 240 个')
        tables = ['import SunPrize.Basic\nimport Mathlib.Data.Fin.VecNotation\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\nnamespace SunPrize\n\n']
        tables.append('def canonicalCodes : Fin 240 → Nat := ![' + ', '.join(str(code) for code,_ in rows) + ']\n\n')
        tables.append('def canonicalRows : Fin 240 → Fin 7 → Fin 7 := ![\n' + ',\n'.join('  ![' + ', '.join(map(str,row)) + ']' for _,row in rows) + ']\n\n')
        tables.append('def matchesBits (g : Nat → Nat → Bool) (code : Nat) : Prop :=\n  ' + conjunction([f'(if code.testBit {i} then g {a} {b} = true else ¬ g {a} {b} = true)' for i,(a,b) in enumerate(pairs)]) + '\n\n')
        tables.append('def paley (a b : Fin 7) : Bool := decide (((b.val + 7 - a.val) % 7) ∈ ([1, 2, 4] : List Nat))\n\n')
        tables.append('theorem canonicalRows_injective : ∀ index : Fin 240, Function.Injective (canonicalRows index) := by\n  unfold Function.Injective canonicalRows\n  decide\n\n')
        table_clauses = [f'(canonicalCodes index).testBit {i} = paley (canonicalRows index {a}) (canonicalRows index {b})' for i,(a,b) in enumerate(pairs)]
        tables.append('theorem canonicalCodes_correct : ∀ index : Fin 240,\n  ' + conjunction(table_clauses) + ' := by\n  unfold canonicalCodes canonicalRows paley\n  decide\n\nend SunPrize\n')
        (ROOT/'SunPrize'/'Tables.lean').write_text(''.join(tables), encoding='utf-8')
        for index,(code,_) in enumerate(rows):
            clause = [-edges[pair] if (code>>i)&1 else edges[pair] for i,pair in enumerate(pairs)]
            assignments = [-item for item in clause]
            body = ['by\n  apply Classical.byContradiction\n  intro denied\n', f'  apply normal {index}\n  change {conjunction([literal(atoms,item) for item in assignments])}\n']
            terms = []
            for position,item in enumerate(clause):
                refutation = f'(fun present => denied {inject(position,"present")})'
                terms.append(f'(Classical.not_not.mp {refutation})' if item < 0 else refutation)
            proof = 'True.intro'
            for term in reversed(terms):
                proof = f'(And.intro {term} {proof})'
            body.append('  exact ' + proof)
            add(clause,''.join(body))
        emit('sevenClassificationContradiction',atoms,clauses,proofs,'', '(g : Nat → Nat → Bool) (obstruction : Obstruction4 7 g) (normal : ∀ index : Fin 240, ¬ matchesBits g (canonicalCodes index))', args.lean, 'SunPrize.Tables')
    if args.only == 'seven':
        return
    edges, atoms, clauses, proofs, add = build_problem(15, 5)
    fixed = []
    for a, b in itertools.combinations(range(8), 2):
        direction = a == 0 or (b - a) % 7 in (1, 2, 4)
        fixed.append(edges[a, b] if direction else -edges[a, b])
    for position, item in enumerate(fixed):
        add([item], 'by exact Or.inl (' + 'normal' + '.2' * position + '.1)')
    extra = 'def NormalizedEight (g : Nat → Nat → Bool) : Prop :=\n  ' + conjunction([literal(atoms, item) for item in fixed]) + '\n\n'
    binders = '(g : Nat → Nat → Bool) (obstruction : Obstruction5 15 g) (normal : NormalizedEight g)'
    emit('normalizedFifteenContradiction', atoms, clauses, proofs, extra, binders, args.lean)


if __name__ == '__main__':
    main()
