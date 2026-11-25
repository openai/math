import OAI.Computability.BorderVNP.FiniteEvaluatorPublicFiber

/-! # Group the finite-field routed terms by their actual received shared lists -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.FieldRawLayout

open Crossing BorderVNP.Cube Cube.Physical Cube.Scatter.Assignment
open scoped BigOperators Classical
set_option synthInstance.maxSize 2048
set_option maxRecDepth 6000

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
  {F : Type*} [Field F] {T : N.Tables F} {L : FieldPacketPlan N F} {S : FieldSiteDirectory N T}
  (V : FieldRawLayout L S) (R : ℕ)

/-- The two real transmission outputs visible to every successful joint
run before the independent private team choices are made. -/
def receivedWords (z : V.Public R) :
    LengthDeclaration L.dimension L.alphabet × (Symbols L.alphabet → List Bool) :=
  (z.val.declaration,z.val.shared)

/-- Exactly the declarations and full shared word arrays produced by
the genuine routed assignments of this selected terminal network. -/
abbrev Received := Set.range (V.receivedWords R)

/-- The received public class of one full checked native word. -/
def receive (z : V.Public R) : V.Received R := ⟨V.receivedWords R z,z,rfl⟩

private theorem receive_surjective : Function.Surjective (V.receive R) := fun z =>
  ⟨z.property.choose,Subtype.ext z.property.choose_spec⟩

/-- Choose one routed assignment merely to name this fiber. Its original
private work bank and private team words do not affect the fiber. -/
noncomputable def receivedRaw (a : V.Received R) : V.Raw R :=
  (V.readPublic R a.property.choose,fun _ _ => false)

/-- Full accepted words yielding a specified received class are precisely
the private fiber used by the actual owned-group traversal. -/
noncomputable def receivedFiberEquiv (a : V.Received R) :
    {z : V.Public R // V.receive R z = a} ≃ V.PublicFiber R (V.receivedRaw R a) := by
  let z := a.property.choose
  have encoded : Routed.encode (V.owners R) (V.readPublic R z) = z.val :=
    congrArg Subtype.val ((Routed.wordsEquiv (V.owners R) L.bitWidth L.supply).apply_symm_apply z)
  have seen : V.receivedWords R z=a.val := a.property.choose_spec
  refine Equiv.subtypeEquivRight fun b => ?_
  change V.receive R b=a ↔ b.val.declaration=(Routed.encode (V.owners R) (V.readPublic R z)).declaration ∧
    b.val.shared=(Routed.encode (V.owners R) (V.readPublic R z)).shared
  rw [encoded,Subtype.ext_iff,←seen,Prod.ext_iff]
  rfl

/-- Genuine private words over a shared transmission are counted once
each. This fiber may contain many positive, negative, or zero contributions. -/
theorem value_by_received (bank : Ports bits) :
    letI : Fintype (V.Public R) := Fintype.ofEquiv _ (Routed.wordsEquiv (V.owners R) L.bitWidth L.supply)
    letI : Finite (V.Received R) := Finite.of_surjective _ (V.receive_surjective R)
    letI : Fintype (V.Received R) := Fintype.ofFinite _
    (∑ z : V.Public R, V.publicValue R bank z) =
      ∑ a : V.Received R, ∑ z : V.PublicFiber R (V.receivedRaw R a), V.publicValue R bank z.val := by
  let : Fintype (V.Public R) := Fintype.ofEquiv _ (Routed.wordsEquiv (V.owners R) L.bitWidth L.supply)
  let : Finite (V.Received R) := Finite.of_surjective _ (V.receive_surjective R)
  let : Fintype (V.Received R) := Fintype.ofFinite _
  refine (Fintype.sum_fiberwise (V.receive R) (V.publicValue R bank)).symm.trans ?_
  apply Finset.sum_congr rfl
  intro a _
  exact Fintype.sum_equiv (V.receivedFiberEquiv R a) _ _ (fun _ => rfl)

end FiniteDiagonal.FieldRawLayout

end BorderVNP
end Computability
end OAI
