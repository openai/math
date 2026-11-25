import OAI.Computability.BorderVNP.FiniteEvaluatorCubeRawDictionary
import OAI.Computability.BorderVNP.FiniteDiagonalPublicTerms

/-! # Accepted transmissions over a fixed common broadcast

Fixing the declaration and the complete selector-bearing shared rows leaves
exactly the native private packet choices. The words in this fiber record
each team's private bits in physical chronological order.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.FieldRawLayout

open Crossing BorderVNP.Cube Cube.Physical Cube.Scatter Cube.Scatter.Assignment
open Physical.NativeAssignments FiniteEvaluator
open scoped Classical BigOperators

set_option synthInstance.maxSize 2048
set_option maxRecDepth 6000

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
  {F : Type*} [Field F] {T : N.Tables F} {L : FieldPacketPlan N F} {S : FieldSiteDirectory N T}
  (V : FieldRawLayout L S) (R : ℕ) (raw : V.Raw R)

local notation "owners" => V.owners R
local notation "obs" => Assignment.Routed.encode owners (Prod.fst raw)
local notation "sel" => Sigma.fst (Prod.fst raw)
local notation "axis" => chosen L.bitWidth L.supply sel
local notation "enc" => nativeWordsEquiv L.bitWidth L.supply sel axis (owners sel)

/-- Checked public words whose declaration and shared lists are precisely
the observed transmission. Their private lists are unconstrained except
for the real decoder's length checks. -/
abbrev PublicFiber := {z : V.Public R // z.val.declaration=(obs).declaration ∧ z.val.shared=(obs).shared}

private theorem shared_eq (f : CubeTriple.Fiber raw.1.2) :
    (Assignment.Routed.encode owners (V.withPrivate R raw f).1).shared=(obs).shared := by
  funext p
  change commonSelectors sel axis p ++ ((enc f.val).1 p).val =
    commonSelectors sel axis p ++ ((enc raw.1.2).1 p).val
  rw [f.property]

/-- The observed packet fiber emits a checked triple of declaration, shared
lists and team-private lists. -/
noncomputable def publicOnFiber (f : CubeTriple.Fiber raw.1.2) : V.PublicFiber R raw :=
  ⟨(Assignment.Routed.wordsEquiv owners L.bitWidth L.supply) (V.withPrivate R raw f).1,
    rfl,V.shared_eq R raw f⟩

/-- Every checked choice of chronological team words over the observed
declaration and common lists decodes to exactly one actual private assignment. -/
noncomputable def publicFiberEquiv : CubeTriple.Fiber raw.1.2 ≃ V.PublicFiber R raw := by
  apply Equiv.ofBijective (V.publicOnFiber R raw)
  constructor
  · intro f g h
    have eq : (V.withPrivate R raw f).1 = (V.withPrivate R raw g).1 :=
      (Assignment.Routed.wordsEquiv owners L.bitWidth L.supply).injective (congrArg Subtype.val h)
    exact Subtype.ext (eq_of_heq (Sigma.mk.inj eq).2)
  · rintro ⟨⟨⟨decl,common,tapes⟩,accepted⟩,hd,hc⟩
    change decl=(obs).declaration at hd
    change common=(obs).shared at hc
    subst decl
    subst common
    let a := Assignment.Routed.physicalShared owners raw.1
    let privateWords : TeamPrivateWords L.bitWidth L.supply sel axis (owners sel) :=
      fun t => ⟨tapes t,accepted.sizes a (Assignment.Routed.encode_shared owners raw.1).symm t⟩
    let f := (enc).symm ((enc raw.1.2).1,privateWords)
    have hf : enc f=((enc raw.1.2).1,privateWords) := (enc).apply_symm_apply _
    let choice : CubeTriple.Fiber raw.1.2 := ⟨f,by simpa only using (congrArg Prod.fst hf)⟩
    refine ⟨choice,Subtype.ext (Subtype.ext (Assignment.Routed.Words.ext rfl (V.shared_eq R raw choice) ?_))⟩
    funext t
    change ((enc f).2 t).val=tapes t
    rw [hf]

/-- Decoding each accepted word fiber returns the same selectors and
the actual underlying distributed choices of its inverse. -/
theorem readPublic_fiber (f : CubeTriple.Fiber raw.1.2) :
    V.readPublic R (V.publicFiberEquiv R raw f).val=(V.withPrivate R raw f).1 :=
  (Assignment.Routed.wordsEquiv owners L.bitWidth L.supply).symm_apply_apply _

/-- An exact finite reindexing for the private work of one fixed routed
broadcast, including when a private list has length zero. -/
theorem sum_publicFiber [Fintype (CubeTriple.Fiber raw.1.2)] [Fintype (V.PublicFiber R raw)]
    (work : CubeTriple.Fiber raw.1.2 → F) :
    ∑ f, work f=∑ z, work ((V.publicFiberEquiv R raw).symm z) :=
  Fintype.sum_equiv (V.publicFiberEquiv R raw) _ _ fun _ => by rw [Equiv.symm_apply_apply]

end FiniteDiagonal.FieldRawLayout

end BorderVNP
end Computability
end OAI
