import SunPrize.Graph

namespace SunPrize.Tournament

lemma obstruction4_of_no_transitive {n : Nat} (T : Tournament (Fin n))
    (hT : ¬ T.HasTransitive 4) : Obstruction4 n T.natMatrix := by
  intro a b c d hab hbc hcd hd
  by_contra denied
  have constraints : ¬ cyclic T.natMatrix a b c ∧ ¬ cyclic T.natMatrix a b d ∧
      ¬ cyclic T.natMatrix a c d ∧ ¬ cyclic T.natMatrix b c d := by
    simpa only [not_or, not_false_eq_true, and_true] using denied
  have ha : a < n := by omega
  have hb : b < n := by omega
  have hc : c < n := by omega
  let f : Fin 4 → Fin n := ![⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩]
  have increasing : StrictMono f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f, Fin.lt_def] <;> omega
  let e : Fin 4 ↪ Fin n := ⟨f, increasing.injective⟩
  apply hT
  apply HasTransitive.map (e := e)
  apply hasTransitive_of_transitive
  apply transitive_of_sorted_acyclic
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all [e, f, pullback, natMatrix, cyclic]

lemma obstruction5_of_no_transitive {n : Nat} (T : Tournament (Fin n))
    (hT : ¬ T.HasTransitive 5) : Obstruction5 n T.natMatrix := by
  intro a b c d e hab hbc hcd hde he
  by_contra denied
  have constraints : ¬ cyclic T.natMatrix a b c ∧ ¬ cyclic T.natMatrix a b d ∧
      ¬ cyclic T.natMatrix a b e ∧ ¬ cyclic T.natMatrix a c d ∧
      ¬ cyclic T.natMatrix a c e ∧ ¬ cyclic T.natMatrix a d e ∧
      ¬ cyclic T.natMatrix b c d ∧ ¬ cyclic T.natMatrix b c e ∧
      ¬ cyclic T.natMatrix b d e ∧ ¬ cyclic T.natMatrix c d e := by
    simpa only [not_or, not_false_eq_true, and_true] using denied
  have ha : a < n := by omega
  have hb : b < n := by omega
  have hc : c < n := by omega
  have hd : d < n := by omega
  let f : Fin 5 → Fin n := ![⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩, ⟨e, he⟩]
  have increasing : StrictMono f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f, Fin.lt_def] <;> omega
  let embedding : Fin 5 ↪ Fin n := ⟨f, increasing.injective⟩
  apply hT
  apply HasTransitive.map (e := embedding)
  apply hasTransitive_of_transitive
  apply transitive_of_sorted_acyclic
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all [embedding, f, pullback, natMatrix, cyclic]

end SunPrize.Tournament
