import OAI.Hierarchy.DescentTreeLaneAddresses
import OAI.Hierarchy.DescentProgramArgumentKeys

namespace OAI
/-! The actual p-word read on the public contact at a terminal exception-tree node. -/
namespace Hierarchy.DescentTreeLaneProgram
open Computability.BorderVNP.Crossing DescentKernelHistory DescentRouterSlots DescentContactTree DescentResetGates
open DescentNamedContact DescentOrderedReset DescentOrderedWords DescentTreeGateRefs DescentBundleHistory DescentLaneGates
open scoped BigOperators Classical
noncomputable section
set_option quotPrecheck false
variable {I C R W : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W]
variable (D : ℕ) (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W)
  (align : ∀s i,site s (input s i)=owner s (contact i)) (m p : ℕ) (hp : 0<p)
  (s : Bool) (w : W) {depth n : ℕ} (book : LinkId owner s w↪Node depth) (key : I↪Fin n)
local notation "wt" => (fun _ : I=>m*p)
local notation "raw" => DescentFixedExceptionalRouter.device D contact input site owner wt s w book
local notation "base" => DescentRouterBank.network D contact input site owner wt
local notation "lp" => link contact owner s w
local notation "code" => DescentFixedNamedContact.code book lp
variable (Y : ℕ) (e : DescentRouterSlots.Item contact owner s w) (b : Fin m)
local notation "q" => (⟨Fin.last depth,prefixAt code depth e⟩ : Physical.Site depth)
local notation "P" => program D contact input site owner align m p hp s w book key Y q
local notation "right" => (((P).op (⟨e,rfl⟩,b)).arg (1 : Fin 2))
local notation "widths" => boundaryWidth raw q
local notation "units" => (fun a=>widths a/p)
local notation "pin" => linkSlot D contact input site owner wt s w (lp e)

omit [Fintype R] in
/-- The reference retained in ofProgram at each covered word is the real contact.
Its contact-fiber bound also applies to the second word when a lane crosses a batch. -/
theorem leaf_contact_block (multiple : ∀a,widths a=units a*p) (j : Fin ((right).count units)) :
    let r:=laneBlock units multiple hp right j
    Sum.map Subtype.val Subtype.val r.port=.inr pin ∧
      r.block=(right).bundleStart+j.val ∧
      r.block/m<Fintype.card (Fibre contact (contact e.val)) :=by
  intro r
  have laneFields := following_fields D contact input site owner align m p hp s w book key Y e b (Fin.last depth)
  simp only [Fin.lastCases_last] at laneFields
  have linkAt : Sum.map Subtype.val Subtype.val (right).port=.inr pin:=congrArg Prod.fst laneFields
  have size (a : Boundary raw q) (atPin : Sum.map Subtype.val Subtype.val a=.inr pin) :
      widths a=Fintype.card (Fibre contact (contact e.val))*(m*p):=by
    rcases a with edge|sock
    · cases atPin
    · have address : sock.val=pin:=Sum.inr.inj atPin
      change DescentNetworkSubstitution.slotWidth base (s,w) sock.val=_
      rw [address,linkWidth]
      simp [DescentNamedContact.width, DescentRouterSlots.link]
      exact Or.inl (@Fintype.card_congr _ _ _ _ (Equiv.refl _))
  refine ⟨linkAt,rfl,(Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt b.isLt)).2 ?_⟩
  have fits:=((right).block units multiple hp j).isLt
  change r.block<widths (right).port/p at fits
  simpa [size (right).port linkAt,←Nat.mul_assoc,hp] using fits

end
end Hierarchy.DescentTreeLaneProgram

end OAI
