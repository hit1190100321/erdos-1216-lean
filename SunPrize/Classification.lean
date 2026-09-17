import SunPrize.Obstruction
import SunPrize.Certificates.sevenClassificationContradiction

namespace SunPrize

lemma bit_assignment_iff (a b : Bool) :
    (if b then a = true else ¬ a = true) ↔ a = b := by
  cases a <;> cases b <;> decide

lemma matches_canonical (g : Nat → Nat → Bool) (index : Fin 240)
    (h : matchesBits g (canonicalCodes index)) :
    ∀ a b : Fin 7, a < b →
      g a.val b.val = paley (canonicalRows index a) (canonicalRows index b) := by
  have correct := canonicalCodes_correct index
  simp only [matchesBits, bit_assignment_iff] at h
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all

lemma paley_noLoop : ∀ a : Fin 7, paley a a = false := by
  unfold paley
  decide

lemma paley_opposite : ∀ a b : Fin 7, a ≠ b → paley a b = !(paley b a) := by
  unfold paley
  decide

noncomputable def rowEquiv (index : Fin 240) : Fin 7 ≃ Fin 7 :=
  Equiv.ofBijective (canonicalRows index)
    ⟨canonicalRows_injective index,
      Finite.surjective_of_injective (canonicalRows_injective index)⟩

/-- 无四点传递子图的任意七点竞赛图，重编号后都是佩利竞赛图。 -/
theorem classify_seven (T : Tournament (Fin 7)) (hT : ¬ T.HasTransitive 4) :
    ∃ e : Fin 7 ≃ Fin 7, ∀ a b, T.arrow (e a) (e b) = paley a b := by
  classical
  have someIndex : ∃ index : Fin 240, matchesBits T.natMatrix (canonicalCodes index) := by
    by_contra denied
    simp only [not_exists] at denied
    exact sevenClassificationContradiction T.natMatrix (T.obstruction4_of_no_transitive hT) denied
  obtain ⟨index, hindex⟩ := someIndex
  have upper := matches_canonical T.natMatrix index hindex
  have full : ∀ a b : Fin 7,
      T.arrow a b = paley (canonicalRows index a) (canonicalRows index b) := by
    intro a b
    rcases lt_trichotomy a b with hab | rfl | hba
    · simpa using upper a b hab
    · rw [T.noLoop, paley_noLoop]
    · have hreverse : T.arrow b a = paley (canonicalRows index b) (canonicalRows index a) := by
        simpa using upper b a hba
      rw [T.opposite a b (ne_of_gt hba), hreverse,
        paley_opposite _ _ ((canonicalRows_injective index).ne (ne_of_lt hba))]
      simp
  refine ⟨(rowEquiv index).symm, ?_⟩
  intro a b
  have h := full ((rowEquiv index).symm a) ((rowEquiv index).symm b)
  change T.arrow ((rowEquiv index).symm a) ((rowEquiv index).symm b) =
    paley ((rowEquiv index) ((rowEquiv index).symm a))
      ((rowEquiv index) ((rowEquiv index).symm b)) at h
  simpa using h

end SunPrize
