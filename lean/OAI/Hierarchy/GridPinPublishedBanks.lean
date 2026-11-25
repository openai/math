import OAI.Hierarchy.GridPinAddressImage
import OAI.Hierarchy.GridPinLiteralImage

namespace OAI
/-! # Simultaneous readback of filled literals and labelled endpoint address words -/

namespace Hierarchy.GridPinPublishedBanks
open Computability.VPVNP.BurstRAM PrivateRAM
open GridThrough GridThrough.Ordered GridPinLiteralImage GridPinAddressImage FactorPinIntervals
open scoped Fin.CommRing
noncomputable section

variable {r k n q d S N w : ℕ} (P : Layout (Cell k n×Fin q) S N d)
    (rail : Fin r↪Fin (S/2)) (direction : Fin r→Fin k)
    (paired : ∀ e,P.origin (pairPorts rail (e,true))=P.origin (pairPorts rail (e,false)))

/-- The native endpoint source is the absolute pin for the named physical rail, in
label/side order. The out-of-range value has no effect on the loop. -/
def endpointWord (i : ℕ) : Word w :=
  if h : i<r*2 then (code (P.address (pairPorts rail (sides.symm ⟨i,h⟩)))).val else 0

theorem endpoints_correct {i : ℕ} (hi : i<r*2) :
    endpointWord P rail i =
      (GridOrderedPinOrigins.slot (PinAssignment.ofFactorIntervals P direction (pairPorts rail) paired) i:Word w) := by
  let x : Fin (r*2) := ⟨i,hi⟩
  let e := sides.symm x
  have eqn : sides (e.1,e.2)=x := sides.apply_symm_apply x
  have h := address_at P rail direction paired e.1 e.2
  rw [eqn] at h
  simp only [endpointWord,dite_eq_left hi]
  exact (congrArg (fun a : ℕ=>(a:Word w)) h).symm

def image (literal ends low count : ℕ) (src : ℕ→Word w) (m : Memory w) :=
  let copied := writeRows (dest P code literal low) src m count
  writeRows (fun i=>ends+i) (endpointWord P rail) copied (r*2)

/-- These are precisely the two hypotheses required by the ordered scatter
backend. They follow from original source bits and the full physical writes. -/
theorem readbacks (literal ends low count : ℕ) (src : ℕ→Word w) (m : Memory w)
    (fit : low+count≤S) (sep : ends+r*2≤literal)
    (init : ∀ t i,m (literal+(code (t,i)).val)=((headerOnly P t i).toNat:Word w))
    (on : ∀ (i : ℕ) (hi : i<count),src i=((P.advice ⟨low+i,by omega⟩).toNat:Word w))
    (off : ∀ j : Fin S,(j.val<low ∨ low+count≤j.val)→P.advice j=false) :
    let A := PinAssignment.ofFactorIntervals P direction (pairPorts rail) paired
    let out := image P rail literal ends low count src m
    (∀ i<r*2,out (ends+i)=(GridOrderedPinOrigins.slot A i:Word w)) ∧
      ∀ ci : Cell k n×Fin (q*d),out (literal+(dataCode ci).val)=((A.literal ci).toNat:Word w) := by
  intro A out
  constructor
  · intro i hi
    change writeRows _ _ _ _ (ends+i)=_
    rw [hit _ _ _ _ i hi (fun _ _ h=>Nat.add_left_cancel h)]
    exact endpoints_correct P rail direction paired hi
  · rintro ⟨c,z⟩
    obtain ⟨⟨t,i⟩,rfl⟩ := finProdFinEquiv.surjective z
    change writeRows _ _ _ _ (literal+(dataCode (c,finProdFinEquiv (t,i))).val)=_
    rw [untouched _ _ _ _ _ (fun _ _=>by omega)]
    rw [literal_at]
    have addr : code ((c,t),i)=dataCode (c,finProdFinEquiv (t,i)) := rfl
    simpa only [Equiv.symm_apply_apply,addr] using equals_literal P code literal low count fit src m init on off (c,t) i

end
end Hierarchy.GridPinPublishedBanks

end OAI
