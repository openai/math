import OAI.ThreeFlat.Diagonal.CompressorPacking

namespace OAI
/-! # The three surviving roles have distinct bases -/

namespace ThreeFlat.Diagonal.CompressorPacking

open Computability.VPVNP.Compression
open scoped Classical

variable {V H Tag L : Type*} {d c : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c)

abbrev base (s : Site V Tag L) : V × Tag := (s.1,s.2.1)
abbrev shift (e : V × Fin d) := (P.siteShift e).1

omit [AddCommGroup H] [AddCommGroup L] in
private theorem zero_mem (x : V) : (0 : Tag) ∈ tagSteps (shift P) x := by simp [tagSteps]

omit [AddCommGroup H] [AddCommGroup L] in
private theorem shift_mem (x : V) (i : Fin d) : shift P (x,i) ∈ tagSteps (shift P) x := by
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)

omit [AddCommGroup H] in
private theorem thin_tag (layout : Bool) (x : Position V H Tag L c) (hx : ¬P.thick x) :
    ∃ a ∈ tagSteps (shift P) x.1.1,
      (P.placement layout x).2.1 = x.1.2.1 + P.offset x.1.1 + a := by
  cases layout
  · refine ⟨0,zero_mem P _,?_⟩
    simp only [PackingData.placement,hx,ite_false,add_zero]
    rfl
  · exact ⟨shift P (x.1.1,P.slotLabel x.2.2),shift_mem P _ _,by
      simp only [PackingData.placement,hx,ite_false,ite_true]; rfl⟩

private theorem role_tag (layout : Bool) (m : P.Motif) :
    ∃ a ∈ tagSteps (shift P) (P.C m).1.1,
      (if layout then P.roleB m else P.roleA m).2.1 =
        (P.C m).1.2.1 + P.offset (P.C m).1.1 + a := by
  cases layout
  · simpa using thin_tag P false (P.C m) (P.not_thick_C m)
  · simpa using thin_tag P true (P.C m) (P.not_thick_C m)

/-- (C,D) may reverse the direction of the original slot. In a binary
group its translation is the same in both directions. -/
private theorem motif_avoid (hn : ∀ a : Tag, -a = a)
    (good : TagConditions P.slots (shift P) P.offset) (m : P.Motif) :
    ∃ Δ : Tag, (P.D m).1.2.1 = (P.C m).1.2.1 + Δ ∧
      (∀ a ∈ tagSteps (shift P) (P.C m).1.1, P.offset (P.C m).1.1 ≠ Δ + a) ∧
      ∀ a ∈ tagSteps (shift P) (P.C m).1.1,
        ∀ b ∈ tagSteps (shift P) (P.D m).1.1,
        P.offset (P.C m).1.1 + P.offset (P.D m).1.1 ≠ Δ + a + b := by
  let e : V × Fin d := (m.val.1.1.1,m.val.1.2)
  let Δ := shift P e
  refine ⟨Δ, ?_⟩
  by_cases thick : P.thick (sourcePosition m.val)
  · simp only [PackingData.C, PackingData.D, thick, ite_true]
    change m.val.1.1.2.1 = m.val.1.1.2.1 + Δ + Δ ∧
      (∀ a ∈ tagSteps (shift P) (P.slots.target e).1, P.offset (P.slots.target e).1 ≠ Δ + a) ∧
      ∀ a ∈ tagSteps (shift P) (P.slots.target e).1, ∀ b ∈ tagSteps (shift P) e.1,
        P.offset (P.slots.target e).1 + P.offset e.1 ≠ Δ + a + b
    refine ⟨?_,?_,?_⟩
    · calc
        _ = m.val.1.1.2.1 + Δ - Δ := (add_sub_cancel_right ..).symm
        _ = _ := by rw [sub_eq_add_neg, hn Δ]
    · intro a ha
      simpa only [incident, Prod.mk.eta, Equiv.symm_apply_apply] using
        good.single (P.slots.target e).1 (.inr (P.slots.target e).2) a ha
    · intro a ha b hb
      simpa only [add_comm, add_left_comm, add_assoc] using good.pair e b a hb ha
  · simp only [PackingData.C, PackingData.D, thick, ite_false]
    exact ⟨rfl,fun a ha => good.single e.1 (.inl e.2) a ha,
      fun a ha b hb => good.pair e a b ha hb⟩

private theorem separated (hn : ∀ a : Tag, -a = a)
    (good : TagConditions P.slots (shift P) P.offset) (siteLayout dLayout : Bool) (m : P.Motif) :
    (if siteLayout then P.roleB m else P.roleA m).2.1 ≠ (P.roleD dLayout m).2.1 := by
  obtain ⟨Δ,hd,hOne,hTwo⟩ := motif_avoid P hn good m
  obtain ⟨a,ha,hSite⟩ := role_tag P siteLayout m
  intro eq
  rw [hSite] at eq
  by_cases hD : P.thick (P.D m)
  · have ht : (P.roleD dLayout m).2.1 = (P.D m).1.2.1 := by
      simp [PackingData.roleD,PackingData.placement,hD]
    rw [ht, hd, add_assoc] at eq
    apply hOne a ha
    have h := eq_sub_of_add_eq (add_left_cancel eq)
    simpa only [sub_eq_add_neg, hn] using h
  · obtain ⟨b,hb,hb'⟩ := thin_tag P dLayout (P.D m) hD
    change (P.C m).1.2.1 + P.offset (P.C m).1.1 + a = (P.placement dLayout (P.D m)).2.1 at eq
    rw [hb',hd,add_assoc,add_assoc,add_assoc] at eq
    have h := eq_sub_of_add_eq (add_left_cancel eq)
    apply hTwo a ha b hb
    rw [h,sub_eq_add_neg,hn a]
    have cancel : P.offset (P.D m).1.1 + P.offset (P.D m).1.1 = 0 := by
      nth_rw 2 [← hn (P.offset (P.D m).1.1)]
      exact add_neg_cancel _
    calc
      _ = (Δ + a + b) + (P.offset (P.D m).1.1 + P.offset (P.D m).1.1) := by abel
      _ = _ := by rw [cancel,add_zero]

/-- The three pairwise inequalities in either of the common layouts. -/
theorem distinct_bases (hn : ∀ a : Tag, -a = a)
    (good : TagConditions P.slots (shift P) P.offset) (layout : Bool) (m : P.Motif) :
    base (P.roleA m) ≠ base (P.roleB m) ∧ base (P.roleA m) ≠ base (P.roleD layout m) ∧
      base (P.roleB m) ≠ base (P.roleD layout m) := by
  refine ⟨fun h => ?_,fun h => separated P hn good false layout m (congrArg Prod.snd h),
    fun h => separated P hn good true layout m (congrArg Prod.snd h)⟩
  exact P.slots.ends_ne ((P.bundle m).1.1,(P.bundle m).2) (congrArg Prod.fst h).symm

end ThreeFlat.Diagonal.CompressorPacking

end OAI
