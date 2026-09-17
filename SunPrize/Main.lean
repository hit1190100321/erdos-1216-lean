import SunPrize.Classification
import SunPrize.Extension
import SunPrize.Certificates.normalizedFifteenContradiction

namespace SunPrize.Tournament

/-- 将源点及其七个佩利出邻居扩展为整个十五点集合的重编号。 -/
lemma normalize_eight (T : Tournament (Fin 15)) (v : Fin 15)
    (e : Fin 7 ↪ Fin 15) (hv : ∀ i, T.arrow v (e i) = true)
    (hp : ∀ a b, T.arrow (e a) (e b) = paley a b) :
    ∃ σ : Equiv.Perm (Fin 15),
      NormalizedEight (T.pullback σ.toEmbedding).natMatrix := by
  let f : Fin 8 → Fin 15 := Fin.cases v (fun i => e i)
  have hf : Function.Injective f := by
    intro a b hab
    rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨a, rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b, rfl⟩
    · rfl
    · exact False.elim ((T.ne_of_arrow (hv b)) (by simpa [f] using hab))
    · exact False.elim ((T.ne_of_arrow (hv a)) (by simpa [f] using hab.symm))
    · exact congrArg Fin.succ (e.injective (by simpa [f] using hab))
  let inclusion : Fin 8 → Fin 15 := fun i => ⟨i.val, by omega⟩
  have hi : Function.Injective inclusion := by
    intro a b hab
    exact Fin.ext (congrArg (fun x : Fin 15 => x.val) hab)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair inclusion f hi hf
  refine ⟨σ, ?_⟩
  have source : σ 0 = v := hσ 0
  have neighbours : ∀ i : Fin 7, σ ⟨i.val + 1, by omega⟩ = e i := by
    intro i
    exact hσ i.succ
  have normalizedStar : ∀ i : Fin 7,
      (T.pullback σ.toEmbedding).arrow 0 ⟨i.val + 1, by omega⟩ = true := by
    intro i
    change T.arrow (σ 0) (σ _) = true
    rw [source, neighbours]
    exact hv i
  have normalizedPaley : ∀ i j : Fin 7,
      (T.pullback σ.toEmbedding).arrow ⟨i.val + 1, by omega⟩
        ⟨j.val + 1, by omega⟩ = paley i j := by
    intro i j
    change T.arrow (σ _) (σ _) = paley i j
    rw [neighbours, neighbours]
    exact hp i j
  have star0 := normalizedStar 0
  have star1 := normalizedStar 1
  have star2 := normalizedStar 2
  have star3 := normalizedStar 3
  have star4 := normalizedStar 4
  have star5 := normalizedStar 5
  have star6 := normalizedStar 6
  unfold NormalizedEight
  simp only [natMatrix]
  simp only [Fin.forall_fin_succ, Fin.val_zero, Fin.val_succ] at normalizedPaley
  simp_all [paley]

lemma five_of_seven_outgoing (T : Tournament (Fin 15)) (v : Fin 15)
    (e : Fin 7 ↪ Fin 15) (hv : ∀ i, T.arrow v (e i) = true) :
    T.HasTransitive 5 := by
  classical
  by_contra hT
  have noFour : ¬ (T.pullback e).HasTransitive 4 := by
    intro h4
    exact hT (T.adjoin_pullback_source v e hv h4)
  obtain ⟨p, hp⟩ := classify_seven (T.pullback e) noFour
  let reordered : Fin 7 ↪ Fin 15 := p.toEmbedding.trans e
  obtain ⟨σ, hnormal⟩ := T.normalize_eight v reordered (fun i => hv (p i)) hp
  have noFive : ¬ (T.pullback σ.toEmbedding).HasTransitive 5 :=
    fun h => hT h.map
  exact normalizedFifteenContradiction _
    ((T.pullback σ.toEmbedding).obstruction5_of_no_transitive noFive) hnormal

/-- 任意十五点竞赛图都包含五点传递诱导子图。 -/
theorem every_fifteen_contains_five (T : Tournament (Fin 15)) : T.HasTransitive 5 := by
  rcases T.outgoing_or_reverse with ⟨v, e, hv⟩ | ⟨v, e, hv⟩
  · exact T.five_of_seven_outgoing v e hv
  · exact (T.reverse.five_of_seven_outgoing v e hv).of_reverse

end SunPrize.Tournament

#print axioms SunPrize.Tournament.every_fifteen_contains_five
