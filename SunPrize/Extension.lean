import SunPrize.Graph

namespace SunPrize.Tournament

/-- 出邻域内的传递子图可通过加入源点扩大一个顶点。 -/
lemma adjoin_pullback_source {V : Type*} {n k : Nat} (T : Tournament V)
    (v : V) (e : Fin n ↪ V) (hv : ∀ i, T.arrow v (e i) = true)
    (h : (T.pullback e).HasTransitive k) : T.HasTransitive (k + 1) := by
  classical
  obtain ⟨s, hs, ht⟩ := h
  let t := s.map e
  have tcard : t.card = k := by simpa [t] using hs
  have outgoing : ∀ a ∈ t, T.arrow v a = true := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp ha
    exact hv i
  have incoming : ∀ a ∈ t, T.arrow a v = false :=
    fun a ha => T.reverse_false (outgoing a ha)
  have absent : v ∉ t := by
    intro hvs
    have := outgoing v hvs
    simp [T.noLoop] at this
  have transitive : ∀ a ∈ t, ∀ b ∈ t, ∀ c ∈ t,
      T.arrow a b = true → T.arrow b c = true → T.arrow a c = true := by
    intro a ha b hb c hc hab hbc
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hb
    obtain ⟨l, hl, rfl⟩ := Finset.mem_map.mp hc
    exact ht i hi j hj l hl hab hbc
  refine ⟨insert v t, by simp [absent, tcard], ?_⟩
  intro a ha b hb c hc hab hbc
  rcases Finset.mem_insert.mp ha with rfl | ha <;>
    rcases Finset.mem_insert.mp hb with rfl | hb <;>
    rcases Finset.mem_insert.mp hc with rfl | hc
  all_goals first | exact outgoing c hc | exact transitive a ha b hb c hc hab hbc | simp_all

lemma select_outgoing {V : Type*} [Fintype V] (T : Tournament V)
    (v : V) (s : Finset V) (hcard : 7 ≤ s.card)
    (hs : ∀ a ∈ s, T.arrow v a = true) :
    ∃ e : Fin 7 ↪ V, ∀ i, T.arrow v (e i) = true := by
  classical
  obtain ⟨t, hts, ht⟩ := Finset.exists_subset_card_eq hcard
  let f := (Finset.equivFinOfCardEq ht).symm
  let e : Fin 7 ↪ V := ⟨fun i => (f i).val, by
    intro i j hij
    exact f.injective (Subtype.ext hij)⟩
  exact ⟨e, fun i => hs _ (hts (f i).property)⟩

/-- 十五个顶点中，固定顶点至少有七个出邻居或七个入邻居。 -/
lemma outgoing_or_reverse (T : Tournament (Fin 15)) :
    (∃ v, ∃ e : Fin 7 ↪ Fin 15, ∀ i, T.arrow v (e i) = true) ∨
    (∃ v, ∃ e : Fin 7 ↪ Fin 15, ∀ i, T.reverse.arrow v (e i) = true) := by
  classical
  let v : Fin 15 := 0
  let s : Finset (Fin 15) := Finset.univ.erase v
  let p := fun a => T.arrow v a = true
  have total : (s.filter p).card + (s.filter (fun a => ¬ p a)).card = 14 := by
    rw [Finset.card_filter_add_card_filter_not]
    simp [s]
  by_cases many : 7 ≤ (s.filter p).card
  · left
    exact ⟨v, T.select_outgoing v (s.filter p) many
      (fun a ha => (Finset.mem_filter.mp ha).2)⟩
  · right
    have many' : 7 ≤ (s.filter (fun a => ¬ p a)).card := by omega
    refine ⟨v, T.reverse.select_outgoing v _ many' ?_⟩
    intro a ha
    obtain ⟨ha, hp⟩ := Finset.mem_filter.mp ha
    have hav : a ≠ v := (Finset.mem_erase.mp ha).1
    change T.arrow a v = true
    rw [T.opposite a v hav, Bool.eq_false_iff.mpr hp]
    rfl

end SunPrize.Tournament
