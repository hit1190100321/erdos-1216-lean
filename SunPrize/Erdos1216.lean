import SunPrize.Main
import Mathlib.Data.Finset.Lattice.Fold

namespace SunPrize

open Tournament

/-- 原题中的 f(n)：所有 n 点竞赛图共同保证的最大传递子图阶数。 -/
noncomputable def guaranteedOrder (n : Nat) : Nat := by
  classical
  exact ((Finset.range (n + 1)).filter
    (fun k => ∀ T : Tournament (Fin n), T.HasTransitive k)).sup id

lemma guaranteedOrder_spec (n : Nat) :
    (∀ T : Tournament (Fin n), T.HasTransitive (guaranteedOrder n)) ∧
    (∀ k, (∀ T : Tournament (Fin n), T.HasTransitive k) → k ≤ guaranteedOrder n) := by
  classical
  let s := (Finset.range (n + 1)).filter
    (fun k => ∀ T : Tournament (Fin n), T.HasTransitive k)
  have zero : 0 ∈ s := by
    simp only [s, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    intro T
    exact ⟨∅, by simp, by simp⟩
  have maximal : s.sup id ∈ s := by
    have h := Finset.sup_mem_of_nonempty (f := id) ⟨0, zero⟩
    simpa using h
  constructor
  · exact (Finset.mem_filter.mp maximal).2
  · intro k hk
    have bound : k ≤ n := by
      let ordered : Tournament (Fin n) := {
        arrow := fun a b => decide (a < b)
        noLoop := by intro a; simp
        opposite := by
          intro a b hab
          rcases lt_or_gt_of_ne hab with h | h
          · have hba : ¬ b < a := by omega
            simp [h, hba]
          · have hab' : ¬ a < b := by omega
            simp [h, hab'] }
      obtain ⟨t, ht, _⟩ := hk ordered
      simpa [ht] using Finset.card_le_card (Finset.subset_univ t)
    exact Finset.le_sup (s := s) (f := id)
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hk⟩)

theorem five_le_guaranteedOrder_fifteen : 5 ≤ guaranteedOrder 15 :=
  (guaranteedOrder_spec 15).2 5 every_fifteen_contains_five

/-- Erdős–Moser 等式猜想的完整否定：n = 15 即为反例。 -/
theorem erdos_1216_disproved :
    ¬ (∀ n : Nat, 0 < n → guaranteedOrder n = Nat.log2 n + 1) := by
  intro conjecture
  have h := five_le_guaranteedOrder_fifteen
  rw [conjecture 15 (by decide)] at h
  have logarithm : Nat.log2 15 = 3 := by decide
  rw [logarithm] at h
  omega

end SunPrize

#print axioms SunPrize.erdos_1216_disproved
