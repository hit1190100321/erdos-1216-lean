import SunPrize.Basic
import Mathlib.Tactic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fintype.Sum

namespace SunPrize

/-- 每对不同顶点恰有一个方向的竞赛图。 -/
structure Tournament (V : Type*) where
  arrow : V → V → Bool
  noLoop : ∀ a, arrow a a = false
  opposite : ∀ a b, a ≠ b → arrow a b = !(arrow b a)

namespace Tournament

variable {V W : Type*}

def reverse (T : Tournament V) : Tournament V where
  arrow a b := T.arrow b a
  noLoop := T.noLoop
  opposite a b h := T.opposite b a h.symm

def pullback (T : Tournament W) (e : V ↪ W) : Tournament V where
  arrow a b := T.arrow (e a) (e b)
  noLoop a := T.noLoop (e a)
  opposite a b h := T.opposite (e a) (e b) (e.injective.ne h)

lemma ne_of_arrow (T : Tournament V) {a b : V} (h : T.arrow a b = true) : a ≠ b := by
  rintro rfl
  simp [T.noLoop] at h

lemma reverse_false (T : Tournament V) {a b : V} (h : T.arrow a b = true) :
    T.arrow b a = false := by
  rw [T.opposite b a (T.ne_of_arrow h).symm, h]
  rfl

/-- 有恰好 k 个顶点、边关系传递的诱导子图。 -/
def HasTransitive (T : Tournament V) (k : Nat) : Prop :=
  ∃ s : Finset V, s.card = k ∧
    ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s,
      T.arrow a b = true → T.arrow b c = true → T.arrow a c = true

lemma HasTransitive.map {T : Tournament W} {e : V ↪ W} {k : Nat}
    (h : (T.pullback e).HasTransitive k) : T.HasTransitive k := by
  classical
  rcases h with ⟨s, hs, ht⟩
  refine ⟨s.map e, by simpa using hs, ?_⟩
  intro a ha b hb c hc hab hbc
  rcases Finset.mem_map.mp ha with ⟨a', ha', rfl⟩
  rcases Finset.mem_map.mp hb with ⟨b', hb', rfl⟩
  rcases Finset.mem_map.mp hc with ⟨c', hc', rfl⟩
  exact ht a' ha' b' hb' c' hc' hab hbc

lemma HasTransitive.of_reverse {T : Tournament V} {k : Nat}
    (h : T.reverse.HasTransitive k) : T.HasTransitive k := by
  rcases h with ⟨s, hs, ht⟩
  exact ⟨s, hs, fun a ha b hb c hc hab hbc => ht c hc b hb a ha hbc hab⟩

lemma hasTransitive_of_transitive {n : Nat} (T : Tournament (Fin n))
    (h : ∀ a b c, T.arrow a b = true → T.arrow b c = true → T.arrow a c = true) :
    T.HasTransitive n := by
  refine ⟨Finset.univ, by simp, ?_⟩
  intro a _ b _ c _
  exact h a b c

lemma transitive_of_sorted_acyclic {n : Nat} (T : Tournament (Fin n))
    (h : ∀ a b c, a < b → b < c →
      ¬ cycleBits (T.arrow a b) (T.arrow b c) (T.arrow a c)) :
    ∀ a b c, T.arrow a b = true → T.arrow b c = true → T.arrow a c = true := by
  intro a b c hab hbc
  by_contra hnot
  have hac : T.arrow a c = false := Bool.eq_false_iff.mpr hnot
  have habne := T.ne_of_arrow hab
  have hbcne := T.ne_of_arrow hbc
  have hba := T.reverse_false hab
  have hcb := T.reverse_false hbc
  have hacne : a ≠ c := by
    rintro rfl
    simp_all
  have hca : T.arrow c a = true := by
    rw [T.opposite c a hacne.symm, hac]
    rfl
  rcases lt_or_gt_of_ne habne with hablt | hbalt
  · rcases lt_or_gt_of_ne hbcne with hbclt | hcblt
    · exact h a b c hablt hbclt (Or.inl ⟨hab, hbc, hac⟩)
    · rcases lt_or_gt_of_ne hacne with haclt | hcalt
      · exact h a c b haclt hcblt (Or.inr ⟨hac, hcb, hab⟩)
      · exact h c a b hcalt hablt (Or.inl ⟨hca, hab, hcb⟩)
  · rcases lt_or_gt_of_ne hacne with haclt | hcalt
    · exact h b a c hbalt haclt (Or.inr ⟨hba, hac, hbc⟩)
    · rcases lt_or_gt_of_ne hbcne with hbclt | hcblt
      · exact h b c a hbclt hcalt (Or.inl ⟨hbc, hca, hba⟩)
      · exact h c b a hcblt hbalt (Or.inr ⟨hcb, hba, hca⟩)

def natMatrix {n : Nat} (T : Tournament (Fin n)) (a b : Nat) : Bool :=
  if ha : a < n then if hb : b < n then T.arrow ⟨a, ha⟩ ⟨b, hb⟩ else false else false

@[simp] lemma natMatrix_apply {n : Nat} (T : Tournament (Fin n)) (a b : Fin n) :
    T.natMatrix a.val b.val = T.arrow a b := by
  simp [natMatrix]

end Tournament
end SunPrize
