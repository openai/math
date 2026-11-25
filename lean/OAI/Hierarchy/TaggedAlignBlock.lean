import OAI.Hierarchy.TaggedAlignRows
import OAI.Hierarchy.TaggedAlignmentPrefix

namespace OAI
/-! # Correctness of the two-terminal alignment block

The local sort supplies a real prefix of nondecreasing digits. The row checks
and the exposed tagged factor then give a deterministic physical permutation,
including the dummy records in the unused lanes.
-/

namespace Hierarchy.Tagged.AlignBlock
open ThreeFlat Routing SortNetwork
open AlignShell AlignRows
open scoped BigOperators Classical
noncomputable section

variable {d j t w : ℕ} (real : Fin w) (digit : Fin d → Fin w) (input : Records (j+t) w)

private theorem keys_neq (i l : Row (j+t)) :
    digitValue digit input i ≠ digitValue digit input l ↔ key digit input i ≠ key digit input l := by
  constructor
  · exact fun h e=>h (BitVec.toFin_inj.mp e)
  · exact fun h e=>h (congrArg BitVec.toFin e)

private theorem local_iff (r : ℕ) (front : initial real input r) (g : Row (j+t) → Row (j+t)) :
    ((input 0 real = true → (g 0).val = 0) ∧ ∀ e, GoodEdge real digit input g e) ↔
      Align.LocalTags r (2^j) (key digit input) g := by
  have blank (i : Row (j+t)) : input i real = false ↔ r ≤ i.val := by
    simp [← Bool.not_eq_true, front i]
  constructor
  · rintro ⟨first,edges⟩
    constructor
    · intro i zero ir
      have ix : i = 0 := Fin.ext zero
      subst i
      exact first ((front 0).mpr ir)
    · intro i l succ
      have left : i.val<l.val := by omega
      let e : Edge (j+t) := ⟨i, succ.trans_lt l.isLt⟩
      have leq : next e = l := Fin.ext succ
      have h := edges e
      change (_ → _ → (g (next e)).val = _) ∧ (_ → _ → g i < g (next e)) at h
      simp only [leq,keys_neq] at h
      exact ⟨fun lr => h.1 ((front i).mpr (left.trans lr)) ((front l).mpr lr),
        fun ir => h.2 ((blank i).mpr ir) ((blank l).mpr (ir.trans left.le))⟩
  · rintro ⟨first,edges⟩
    constructor
    · intro zr
      exact first 0 rfl ((front _).mp zr)
    · intro e
      have h := edges e.1 (next e) rfl
      constructor
      · intro _ lr
        simpa only [keys_neq] using h.1 ((front _).mp lr)
      · intro ir _
        exact h.2 ((blank _).mp ir)

/-- The concrete tagged shell computes the canonical padded output, for every
input with a real prefix in sorted digit order. -/
theorem eval (F : Type*) [CommSemiring F] (output : Records (j+t) w) (r : ℕ)
    (room : r ≤ 2^(j+t)) (front : initial real input r) (sorted : Ordered real digit input)
    (e : Fin r ↪ Row (j+t)) (place : ∀ i, (e i).val = Align.realAddress (2^j)
      (fun l => key digit input (Align.split room (.inl l))) i) :
    let perm := (Align.split room).symm.trans (Align.complete e)
    (∑ hole : Fin (pins (j+t) w) → Bool,
      TypedWiring.value (AlignShell.shell (AlignRows.network F real digit))
        (Sum.elim (Sum.elim (pack input) (pack output)) hole) * coeff F (j+t) w hole) =
      if output = input ∘ perm.symm then 1 else 0 := by
  let perm := (Align.split room).symm.trans (Align.complete e)
  change _ = if output = input ∘ perm.symm then 1 else 0
  rw [AlignShell.eval]
  change (∑ g : Row (j+t) → Row (j+t),
    TypedWiring.value (AlignRows.network F real digit) (checkerPins input g) * taggedSwitch F g input output) = _
  simp_rw [AlignRows.eval real digit input sorted, local_iff real digit input r front]
  let fits := Align.LocalTags r (2^j) (key digit input)
  have iffG (g) : Function.Bijective g ∧ fits g ↔ g = perm := Align.canonical_tags room _ _ e place
  have outIff : (∀ i, output (perm i) = input i) ↔ output = input ∘ perm.symm := by
    constructor
    · intro h
      funext i
      simpa using h (perm.symm i)
    · rintro rfl i
      simp
  have term (g : Row (j+t) → Row (j+t)) :
      (if fits g then (1:F) else 0)*taggedSwitch F g input output =
      if g=perm ∧ output=input ∘ perm.symm then 1 else 0 := by
    by_cases eq : g = perm
    · subst g
      obtain ⟨bij,fit⟩ := (iffG perm).mpr rfl
      simp [taggedSwitch,Routed,fit,outIff]
    · by_cases fit : fits g
      · have bad : ¬Function.Bijective g := fun bij => eq ((iffG _).mp ⟨bij,fit⟩)
        have impossible : ¬Routed g input output := fun routed=>bad routed.1
        simp only [taggedSwitch,impossible,ite_false,fit,ite_true,one_mul,eq,false_and]
      · simp [fit,eq]
  unfold fits at term
  simp_rw [term]
  by_cases ok : output=input ∘ perm.symm <;> simp [ok]

end
end Hierarchy.Tagged.AlignBlock

end OAI
