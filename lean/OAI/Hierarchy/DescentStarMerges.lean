import OAI.Hierarchy.DescentMatchedSlabs

namespace OAI
/-! # Components of the native whole-item contraction in the two common layouts -/

namespace Hierarchy.DescentPacking
open scoped Classical BigOperators
noncomputable section
variable {C U V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
variable (traffic : C → U → V → ℕ) (B : ℕ) (thin thick : C → List U)

abbrev SlabSlot (c : C) := Locations (slabPacking (traffic c) B (thin c) (thick c)).decisions
abbrev ThinSite := Σ c,SlabSlot traffic B thin thick c
abbrev OldSite := C ⊕ ThinSite traffic B thin thick
abbrev AllPairs := Σ c,Matched (traffic c) B (thin c) (thick c)

def thinSite (p : AllPairs traffic B thin thick) : ThinSite traffic B thin thick :=
  ⟨p.1,(oldThin (traffic p.1) B (thin p.1) (thick p.1) p.2).1⟩

/-- The first layout uses the source colony's thick center. The other layout
uses the single destination chosen for every bundle in the whole thin item. -/
def mergeCenter (layout : Bool) (bin : C → V → C) (p : AllPairs traffic B thin thick) : C :=
  if layout then bin p.1 (oldThick (traffic p.1) B (thin p.1) (thick p.1) p.2).1 else p.1

def ownerCenter (layout : Bool) (bin : C → V → C) :
    OldSite traffic B thin thick → Option C
  | .inl c => some c
  | .inr ⟨c,t⟩ => ((slabPacking (traffic c) B (thin c) (thick c)).decisions.get t).2.map
      (fun v => if layout then bin c v else c)

omit [Fintype C] [DecidableEq C] in
theorem pair_center (layout : Bool) (bin : C → V → C) (p : AllPairs traffic B thin thick) :
    ownerCenter traffic B thin thick layout bin (.inr (thinSite traffic B thin thick p))=
      some (mergeCenter traffic B thin thick layout bin p) := by
  rcases p with ⟨c,e⟩
  simp only [ownerCenter,thinSite,mergeCenter,matched_destination,Option.map_some]

/-- Exactly the old-old generator edges introduced by the matched demands.
Thin destinations meet a private auxiliary vertex and create no old-old edge. -/
inductive MergeStep (layout : Bool) (bin : C → V → C) :
    OldSite traffic B thin thick → OldSite traffic B thin thick → Prop
  | toCenter (p : AllPairs traffic B thin thick) : MergeStep layout bin
      (.inr (thinSite traffic B thin thick p)) (.inl (mergeCenter traffic B thin thick layout bin p))
  | toThin (p : AllPairs traffic B thin thick) : MergeStep layout bin
      (.inl (mergeCenter traffic B thin thick layout bin p)) (.inr (thinSite traffic B thin thick p))

omit [Fintype C] [DecidableEq C] in
theorem one_center (layout : Bool) (bin : C → V → C) {a b : OldSite traffic B thin thick}
    (path : Relation.ReflTransGen (MergeStep traffic B thin thick layout bin) a b) :
    ownerCenter traffic B thin thick layout bin a=ownerCenter traffic B thin thick layout bin b := by
  induction path with
  | refl => rfl
  | tail _ next ih =>
    apply ih.trans
    cases next with
    | toCenter p => exact pair_center traffic B thin thick layout bin p
    | toThin p => exact (pair_center traffic B thin thick layout bin p).symm

omit [Fintype C] [DecidableEq C] in
theorem centers_separate (layout : Bool) (bin : C → V → C) {c d : C}
    (path : Relation.ReflTransGen (MergeStep traffic B thin thick layout bin) (.inl c) (.inl d)) :
    c=d := Option.some.inj (one_center traffic B thin thick layout bin path)

omit [Fintype C] [DecidableEq C] in
theorem slots_bound (c : C) {A : ℕ} (pos : 0<B)
    (bound : amount (live (traffic c)) (thin c)≤A*B) :
    Fintype.card (SlabSlot traffic B thin thick c)≤A+1 := by
  have order := congrArg List.length (slabPacking (traffic c) B (thin c) (thick c)).order
  simp only [List.length_map] at order
  simp only [SlabSlot,Locations,Fintype.card_fin,order]
  exact thinPacks_count _ pos _ bound

omit [DecidableEq C] in
/-- A paid center can receive only the existing thin packs of the allowed
old source colonies. This counts every actual position including zero-load
or unmatched packs, so it applies uniformly across all summands. -/
theorem component_packs (layout : Bool) (bin : C → V → C) (c : C) (allow : Finset C)
    (sourceAllowed : c∈allow) (destAllowed : ∀d v,bin d v=c → d∈allow)
    {A : ℕ} (pos : 0<B) (bound : ∀d,amount (live (traffic d)) (thin d)≤A*B) :
    (Finset.univ.filter fun t : ThinSite traffic B thin thick =>
      Relation.ReflTransGen (MergeStep traffic B thin thick layout bin) (.inl c) (.inr t)).card
      ≤allow.card*(A+1) := by
  let slots := allow.sigma (fun d => (Finset.univ : Finset (SlabSlot traffic B thin thick d)))
  apply (Finset.card_le_card (t:=slots) ?_).trans
  · simp only [slots,Finset.card_sigma,Finset.card_univ]
    calc
      _ ≤ ∑ _∈allow,(A+1) := Finset.sum_le_sum fun d _ => slots_bound traffic B thin thick d pos (bound d)
      _ = _ := by simp
  · rintro ⟨d,j⟩ mem
    have path := (Finset.mem_filter.mp mem).2
    have same := one_center traffic B thin thick layout bin path
    change some c = Option.map _ _ at same
    unfold slots
    apply Finset.mem_sigma.mpr
    refine ⟨?_,Finset.mem_univ _⟩
    cases h : ((slabPacking (traffic d) B (thin d) (thick d)).decisions.get j).2 with
    | none =>
      rw [h] at same
      contradiction
    | some v =>
      rw [h, Option.map_some] at same
      have result := Option.some.inj same
      cases layout with
      | false =>
        have eq : c=d := by simpa using result
        simpa [←eq] using sourceAllowed
      | true => exact destAllowed d v (by simpa using result.symm)

end
end Hierarchy.DescentPacking

end OAI
