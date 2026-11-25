import OAI.Computability.BorderVNP.DiagonalJoinedPrivateBank
import OAI.Computability.BorderVNP.DiagonalPositiveExteriorPin

/-! # Reordering the actual exterior, joint preparations, cell banks and subtotal guesses -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open TeamContraction TeamContraction.ProcessorSlots CellMacro.Generator BorderVNP.Cube
open scoped Classical

variable {R n w axes b h K s : ℕ} {id : TableEntry axes b h K s → ℕ} {gen : Fragment IO}
    {X Raw Hist Claim : Type} {Route : Hist → Type} {Bank : Hist → Type}
    {Report : (i : Raw) → (q : Hist) → Route q → Type}
    (S : X → Fin (R+1) → PositiveTeam id gen n w)
    (J : ∀ x (p : (u : Fin (R+1)) → (S x u).Prefix),
      JoinedCells (fun u => (S x u).pub) (fun u => (S x u).postMemory) (fun u => (S x u).generated) p)

/-- A prefix ends before any local cell validator or subtotal check.
It includes the real exterior and all teams' pin, geometry and route returns. -/
abbrev JointBeforeCells := (x : X) × ((u : Fin (R+1)) → (S x u).Prefix)

/-- The substituted raw pin, public history, routed cube payload, subtotal
header and arbitrarily proposed local report digits of the prefix. -/
abbrev PreparedFields (Raw Hist Claim : Type) (Route : Hist → Type)
    (Report : (i : Raw) → (q : Hist) → Route q → Type) :=
  (i : Raw) × (q : Hist) × (v : Route q) × Claim × Report i q v

variable (prep : JointBeforeCells S ≃ PreparedFields Raw Hist Claim Route Report)
    (banks : ∀ f : PreparedFields Raw Hist Claim Route Report,
      (J (prep.symm f).1 (prep.symm f).2).Private ≃ Bank f.2.1)

/-- The original unfiltered native assignment on the physical wire and RAM
states corresponding to these transmitted fields and this guessed private bank. -/
noncomputable def sourceCandidate (i : Raw) (q : Hist) (v : Route q × Bank q) (r : Report i q v.1) (c : Claim) :
    let p := prep.symm ⟨i,q,v.1,c,r⟩
    PositiveAssignment (S p.1) (J p.1) :=
  ⟨(prep.symm ⟨i,q,v.1,c,r⟩).2,(banks ⟨i,q,v.1,c,r⟩).symm v.2⟩

/-- The return predicate on that same unaltered native assignment. -/
def sourcePass (i : Raw) (q : Hist) (v : Route q × Bank q) (r : Report i q v.1) (c : Claim) : Prop :=
  let p := prep.symm ⟨i,q,v.1,c,r⟩
  positivePass (S p.1) (J p.1) (sourceCandidate S J prep banks i q v r c)

/-- First decode the prefix alone, then move the local private vectors next
to their payloads. The report and claim fields stay free until the actual
positive predicate on their original native prefix has been applied. -/
noncomputable def acceptedPrefixBankEquiv :
    AcceptedExterior S J ≃
      ((i : Raw) × (q : Hist) × (v : Route q × Bank q) × (r : Report i q v.1) ×
        {c : Claim // sourcePass S J prep banks i q v r c}) := by
  let B := fun z : JointBeforeCells S => (J z.1 z.2).Private
  let whole : (Σ z : JointBeforeCells S, B z) ≃ Σ f : PreparedFields Raw Hist Claim Route Report, Bank f.2.1 :=
    (Equiv.sigmaCongrLeft' (β:=B) prep).trans (Equiv.sigmaCongrRight banks)
  let test (f : Σ f : PreparedFields Raw Hist Claim Route Report, Bank f.2.1) :=
    sourcePass S J prep banks f.1.1 f.1.2.1 (f.1.2.2.1,f.2) f.1.2.2.2.2 f.1.2.2.2.1
  let collect : AcceptedExterior S J ≃ {z : Σ z : JointBeforeCells S, B z // test (whole z)} :=
    { toFun a := by
        let z : Σ z : JointBeforeCells S, B z := ⟨⟨a.1,a.2.val.1⟩,a.2.val.2⟩
        refine ⟨z,?_⟩
        have eq := whole.symm_apply_apply z
        have same : positivePass (S (whole.symm (whole z)).1.1) (J (whole.symm (whole z)).1.1)
            ⟨(whole.symm (whole z)).1.2,(whole.symm (whole z)).2⟩ := by rw [eq]; exact a.2.property
        exact same
      invFun z := by
        refine ⟨z.val.1.1,⟨⟨z.val.1.2,z.val.2⟩,?_⟩⟩
        have same : positivePass (S (whole.symm (whole z.val)).1.1) (J (whole.symm (whole z.val)).1.1)
            ⟨(whole.symm (whole z.val)).1.2,(whole.symm (whole z.val)).2⟩ := z.property
        exact whole.symm_apply_apply z.val ▸ same
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let spell : {f // test f} ≃ ((i : Raw) × (q : Hist) × (v : Route q × Bank q) ×
      (r : Report i q v.1) × {c : Claim // sourcePass S J prep banks i q v r c}) :=
    { toFun a := ⟨a.val.1.1,a.val.1.2.1,(a.val.1.2.2.1,a.val.2),a.val.1.2.2.2.2,a.val.1.2.2.2.1,a.property⟩
      invFun a := ⟨⟨⟨a.1,a.2.1,a.2.2.1.1,a.2.2.2.2.val,a.2.2.2.1⟩,a.2.2.1.2⟩,a.2.2.2.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (collect.trans (Equiv.subtypeEquivOfSubtype (p:=test) whole)).trans spell

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
