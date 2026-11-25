import OAI.Hierarchy.TaggedWideRows

namespace OAI
/-! # The native common ID recovers the original absolute subslot suffix -/

noncomputable section
namespace Hierarchy.Tagged.WideStack
open TaggedShorterBudget ProtocolRAMReportedPorts TaggedShorterFields
open scoped Classical BigOperators
variable {T : Type*} [Fintype T] {n : T→ℕ}
  (groups γ : T→ℕ) (rows : ∀i,Fin (n i)→ProtocolRAMEmit.Row) (w m : ℕ)
  (unique : ∀t,Function.Injective (fun i=>(rows t i).link))

def originalPrefix (t : T) (e : (g : Fin (groups t)) × Fin (count (rows t) w m (γ t) g.val))
    (j : Fin ⌈dyadic (γ t)*w⌉₊) : Prop :=
  let u := (common (rows t) w m (γ t) e.1.val (unique t)).symm e.2
  u.2.val*⌈dyadic (γ t)*w⌉₊+j.val<(rows t u.1.val).width

omit [Fintype T] in
/-- The common link labels cover all and only the physically installed
subslots. This identifies the single stored raw-width test on a paid
physical endpoint with the original row's suffix condition. -/
theorem originalPrefix_iff (x : Lanes groups γ rows w m) :
    (∀t e j,x t e j=true → originalPrefix groups γ rows w m unique t e j) ↔
      highZeros (fun r : Occ groups γ rows w m=>(rows r.1 r.2.2.val).width)
        (fun r=>⌈dyadic (γ r.1)*w⌉₊) (fun r=>pieces (rows r.1) w r.2.2.val)
        (rowLanes groups γ rows w m unique x) := by
  constructor
  · intro ok r z j large
    let e := common (rows r.1) w m (γ r.1) r.2.1.val (unique r.1)
    cases bit : x r.1 ⟨r.2.1,e ⟨r.2.2,z⟩⟩ j
    · exact bit
    · have small := ok r.1 ⟨r.2.1,e ⟨r.2.2,z⟩⟩ j bit
      change (e.symm (e ⟨r.2.2,z⟩)).2.val*_+_<(rows r.1 (e.symm (e ⟨r.2.2,z⟩)).1.val).width at small
      have back : e.symm (e ⟨r.2.2,z⟩)=⟨r.2.2,z⟩ := e.symm_apply_apply _
      rw [back] at small
      exact (Nat.not_lt_of_ge large small).elim
  · intro zero t e j bit
    let E := common (rows t) w m (γ t) e.1.val (unique t)
    let u := E.symm e.2
    change u.2.val*⌈dyadic (γ t)*w⌉₊+j.val<(rows t u.1.val).width
    by_contra! miss
    have blank := zero ⟨t,e.1,u.1⟩ u.2 j miss
    change x t ⟨e.1,E ⟨u.1,u.2⟩⟩ j=false at blank
    have back : E ⟨u.1,u.2⟩=e.2 := E.apply_symm_apply _
    rw [back,bit] at blank
    contradiction

end Hierarchy.Tagged.WideStack

end
end OAI
