import OAI.Geometry.Hirsch.PairWeight

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

variable {Ω I : Type} [Fintype Ω] {p : Law Ω} (pins : Pins p I)

def Law.Independent (p : Law Ω) (a b : Ω → Prop) :=
  p.prob (fun x => a x ∧ b x) = p.prob a * p.prob b

namespace Pins

theorem family (s : Finset (Finset I)) : p.prob (fun x => ∃ t ∈ s, t ⊆ pins.success x) ≤ pins.mass s := by
  apply (p.union_finset s (fun t x => t ⊆ pins.success x)).trans_eq
  exact Finset.sum_congr rfl (fun t _ => pins.prob t)

theorem dynamic [Fintype I] (select : Ω → Finset (Finset I)) (event : Ω → Prop) (M K : ℕ)
    (count : ∀ x, (select x).card ≤ M) (size : ∀ x s, s ∈ select x → s.card = K)
    (active : ∀ x s, s ∈ select x → event x)
    (indep : ∀ s, p.Independent (fun x => s ∈ select x) (fun x => s ⊆ pins.success x)) :
    p.prob (fun x => ∃ s ∈ select x, s ⊆ pins.success x) ≤ M * p.prob event * pins.rate^K := by
  let valid := fun (s : Finset I) x => s ∈ select x
  have bound : ∑ s, p.prob (valid s) ≤ M * p.prob event := by
    apply p.multiplicity _ _ _ _ (fun s _ x hx => active x s hx)
    intro x
    simpa [valid] using count x
  calc
    _ ≤ ∑ s, p.prob (fun x => valid s x ∧ s ⊆ pins.success x) := p.union _
    _ = ∑ s, p.prob (valid s) * pins.rate^K := by
      apply Finset.sum_congr rfl
      intro s _
      rw [show p.prob _ = p.prob (valid s) * p.prob _ from indep s,pins.prob]
      by_cases he : s.card = K
      · rw [he]
      · have hn : ∀ x, ¬valid s x := fun x hx => he (size x s hx)
        simp [Law.prob,hn]
    _ ≤ _ := by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right bound (pow_nonneg pins.pos.le _)

end Pins

namespace Trial

variable {Z : Type} {place : I → Z} {K e d : ℕ} {tests : Tests place e d}

theorem Tests.Available.sub {s t : Finset I} (ha : tests.Available s) (ht : t ⊆ s) : tests.Available t := by
  intro g hg
  obtain ⟨l,hl,hh⟩ := ha g (ht hg)
  exact ⟨l,hl,fun j hj hm => hh j hj (ht hm)⟩

namespace Gates

variable {pins} {gamma alpha : ℝ} [Fintype I] (gate : Gates pins place K gamma alpha)

structure Draw (fresh : Pins p I) where
  available : Ω → Finset I
  old : ∀ x, gate.Possible (available x)
  pin : ∀ x, available x ⊆ pins.success x
  independent : ∀ (E : Finset I → Prop) s,
    p.Independent (fun x => E (available x)) (fun x => s ⊆ fresh.success x)

namespace Draw

variable {gate} {fresh : Pins p I} (draw : gate.Draw fresh)

def thin (x : Ω) := draw.available x ∩ fresh.success x

omit [Fintype I] in
theorem pinned (x : Ω) : draw.thin x ⊆ pins.success x := Finset.inter_subset_left.trans (draw.pin x)

theorem large (hs : gate.Serves tests) :
    ∃ leaves : Finset I → Finset (Finset I),
      (∀ x, tests.Frontier (draw.available x) K ∅ (leaves (draw.available x))) ∧
      p.prob (fun x => tests.long.Covers (draw.available x) ∧
        ∃ s ∈ leaves (draw.available x), s.card = K ∧ s ⊆ fresh.success x) ≤
        Tests.capacity K e d * p.prob (fun x => tests.long.Covers (draw.available x)) * fresh.rate^K := by
  have hex : ∀ a, ∃ leaves, leaves.card ≤ Tests.capacity K e d ∧
      (gate.Possible a → tests.Frontier a K ∅ leaves) := by
    intro a
    by_cases hp : gate.Possible a
    · obtain ⟨x,hx⟩ := hp
      obtain ⟨leaves,hl,hf⟩ := ((hs.available x).sub hx).frontier K
      exact ⟨leaves,hl,fun _ => hf⟩
    · exact ⟨∅,by simp,fun hh => (hp hh).elim⟩
  choose leaves hc hf using hex
  refine ⟨leaves,fun x => hf _ (draw.old x),?_⟩
  let sel := fun a => (leaves a).filter (fun s => tests.long.Covers a ∧ s.card = K)
  apply le_trans _ (fresh.dynamic (sel ∘ draw.available) (fun x => tests.long.Covers (draw.available x)) _ K
    (fun x => (Finset.card_filter_le ..).trans (hc _)) (fun _ _ hh => (Finset.mem_filter.mp hh).2.2)
    (fun _ _ hh => (Finset.mem_filter.mp hh).2.1) (fun s => draw.independent (fun a => s ∈ sel a) s))
  exact p.mono (fun _ ⟨hh,s,hs,hk,hp⟩ => ⟨s,Finset.mem_filter.mpr ⟨hs,hh,hk⟩,hp⟩)

theorem extract (hs : gate.Serves tests) (near : Trial I) (paths : ℕ → Trial I) {loss U : ℝ}
    (lower : ∀ j ≤ K, (paths 0).Refines (paths (j+1)))
    (upper : (paths (K+1)).Refines tests.short)
    (hloss : ∀ j ≤ K, pins.mass ((gate.cuts (paths j) (paths (j+1))).filter (fun s => ¬near.Minimal s)) ≤ loss)
    (crude : p.prob (fun x => tests.long.Covers (draw.available x)) ≤ U) :
    p.prob (fun x => tests.long.Covers (draw.thin x) ∧
      ¬∃ s ∈ gate.cuts near (paths 0), s ⊆ draw.thin x) ≤ Tests.capacity K e d * U * fresh.rate^K + (K+1)*loss := by
  obtain ⟨leaves,hf,hl⟩ := draw.large hs
  let large := fun x => tests.long.Covers (draw.available x) ∧
    ∃ s ∈ leaves (draw.available x), s.card = K ∧ s ⊆ fresh.success x
  let bad := fun j => (gate.cuts (paths j) (paths (j+1))).filter (fun s => ¬near.Minimal s)
  let small := fun x => ∃ j ∈ Finset.range (K+1), ∃ s ∈ bad j, s ⊆ pins.success x
  have hb : p.prob small ≤ (K+1)*loss := by
    apply (p.union_finset (Finset.range (K+1)) (fun j x => ∃ s ∈ bad j, s ⊆ pins.success x)).trans
    calc
      _ ≤ ∑ _ ∈ Finset.range (K+1), loss := Finset.sum_le_sum fun j hj =>
        (pins.family _).trans (hloss j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
      _ = _ := by simp
  have hlarge : p.prob large ≤ Tests.capacity K e d * U * fresh.rate^K := hl.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left crude (by positivity)) (pow_nonneg fresh.pos.le _))
  apply le_trans _ ((p.either large small).trans (add_le_add hlarge hb))
  apply p.mono
  rintro x ⟨hc,hn⟩
  have sub : draw.thin x ⊆ draw.available x := Finset.inter_subset_left
  obtain ⟨s,hm,hsub⟩ := (hf x).2 _ sub (Finset.empty_subset _) hc
  obtain ⟨⟨_,hk⟩,he | he⟩ := (hf x).1 s hm
  · exact .inl ⟨hc.mono sub,s,hm,he,hsub.trans Finset.inter_subset_right⟩
  · obtain ⟨j,hj,t,ht,hc',hmin⟩ := plateau paths hk (upper s he)
    have hthin := ht.trans hsub
    have hsize := (Finset.card_le_card ht).trans hk
    obtain ⟨y,hy⟩ := draw.old x
    have hp : gate.Possible t := ⟨y,(hthin.trans sub).trans hy⟩
    have hh : ¬near.Minimal t := fun h => hn ⟨t,gate.mem_cuts.mpr ⟨hsize,lower _ hj _ hc',h,hp⟩,hthin⟩
    exact .inr ⟨j,Finset.mem_range.mpr (by omega),t,Finset.mem_filter.mpr
      ⟨gate.mem_cuts.mpr ⟨hsize,hc',hmin,hp⟩,hh⟩,hthin.trans (draw.pinned x)⟩

end Draw
end Gates
end Trial
end OAI.Geometry.Hirsch.Layer
