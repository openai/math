import OAI.Hierarchy.GridPinPublisher

namespace OAI
/-! # Composing the two final native writes with the original immutable reads -/

namespace Hierarchy.GridPinPublisher
open Computability.VPVNP.BurstRAM PrivateRAM
open FactorPinIntervals GridThrough GridThrough.Ordered
open GridPinNativeLoops GridPinLiteralImage GridPinPublishedBanks GridPinAddressImage
open scoped Fin.CommRing
noncomputable section

variable {r k n q d S N W : ℕ} (P : Plan) (Q : Layout (Cell k n×Fin q) S N d)
    (rail : Fin r↪Fin (S/2)) (direction : Fin r→Fin k)
    (paired : ∀ e,Q.origin (pairPorts rail (e,true))=Q.origin (pairPorts rail (e,false)))

private def slotOfNat (j : ℕ) :=
  if hj : j<S then (code (Q.address ⟨j,hj⟩)).val else 0

def railOfNat (e : ℕ) := if h : e<r then (rail ⟨e,h⟩).val else 0

private theorem sideVal (e : Fin r) (b : Bool) : (sides (e,b)).val=e.val*2+b.toNat := by
  rw [GridThrough.Ordered.exterior_number]
  omega

private theorem endpoint_image (i : ℕ) (hi : i<r*2) :
    (slotOfNat Q (railOfNat rail (i/2)*2+i%2):Word W)=endpointWord Q rail i := by
  let x : Fin (r*2) := ⟨i,hi⟩
  let u := sides.symm x
  have address := congrArg Fin.val (sides.apply_symm_apply x)
  change (sides (u.1,u.2)).val=i at address
  rw [sideVal] at address
  have small : u.2.toNat<2 := by cases u.2 <;> decide
  have e : i/2=u.1.val := by omega
  have b : i%2=u.2.toNat := by omega
  have matchBit : (railOfNat rail (i/2))*2+i%2=(pairPorts rail u).val := by
    change railOfNat rail (i/2)*2+i%2=2*(rail u.1).val+u.2.toNat
    simp [railOfNat,e,b,u.1.isLt,Nat.mul_comm]
  simp [endpointWord,hi,matchBit,slotOfNat,(pairPorts rail u).isLt,u,x]

/-- Only pre-scatter readbacks appear here: the header image, stable original
bits, numbered rails, and block offsets. All available head/offset reads are
the outputs of the two native prefix scans (see `traced_offset`). -/
theorem published_banks (m : Memory W) (ends : P.endpoints=r*2)
    (bitFit : P.source.external+P.literals≤S) (srcFit : S≤2^W) (two : 2<2^W)
    (spanFit : P.source.span<2^W) (countFit : P.literals<2^W) (endFit : r*2<2^W)
    (init : ∀ t i, P.initialized m (P.source.literal+(code (t,i)).val)=
      ((headerOnly Q t i).toNat:Word W))
    (copied : ∀ i (hi : i<P.literals),P.initialized m (P.source.originals+(P.source.external+i))=
      ((Q.advice ⟨P.source.external+i,by omega⟩).toNat:Word W))
    (off : ∀ j : Fin S,(j.val<P.source.external ∨ P.source.external+P.literals≤j.val) → Q.advice j=false)
    (ranks : ∀ i<r*2,P.initialized m (P.source.rails+i/2)=(railOfNat rail (i/2):Word W))
    (blocks : ∀ j : Fin S,P.initialized m (P.source.blocks+j.val/P.source.span)+
      ((j.val%P.source.span:ℕ):Word W)=((code (Q.address j)).val:Word W))
    (tableFit : ∀ j : Fin S,P.source.blocks+j.val/P.source.span<2^W)
    (origFit : P.source.originals+S≤2^W)
    (literalFit : P.source.literal+(n+1)^k*(q*d)≤2^W)
    (railFit : P.source.rails+r≤2^W) (destFit : P.source.dest+r*2≤2^W)
    (regions : P.source.dest+r*2≤P.source.literal)
    (protect : ∀ i<(n+1)^k*(q*d),
      (∀ j : Fin S,P.source.literal+i≠P.source.blocks+j.val/P.source.span) ∧
      (∀ j : Fin S,P.source.literal+i≠P.source.originals+j.val) ∧
      ∀ e : Fin r,P.source.literal+i≠P.source.rails+e.val)
    (destProtect : ∀ i<r*2,
      (∀j : Fin S,P.source.dest+i≠P.source.blocks+j.val/P.source.span) ∧
      ∀ e : Fin r,P.source.dest+i≠P.source.rails+e.val) :
    let A := PinAssignment.ofFactorIntervals Q direction (pairPorts rail) paired
    Published A P (P.output m) ∧ ∀a,
      (a<P.source.dest ∨ P.source.dest+r*2≤a) →
      (a<P.source.literal ∨ P.source.literal+(n+1)^k*(q*d)≤a) →
      P.output m a=P.initialized m a := by
  intro A
  let low := P.source.external
  let fetch := fun i=>P.initialized m (P.source.originals+(low+i))
  let src := fun i=> slotOfNat Q (low+i)
  have sourceAt (i : ℕ) (hi : i<P.literals) : src i=(code (Q.address ⟨low+i,by dsimp [low];omega⟩)).val :=
    dite_eq_left (by dsimp [low];omega)
  have stored :
      P.scattered m=writeRows (dest Q code P.source.literal low) fetch (P.initialized m) P.literals := by
    unfold scattered
    rw [literals_image P.source P.literals _ src spanFit countFit]
    · apply writeRows_congr <;> intro i hi
      · simp [dest,sourceAt i hi,show low+i<S from by dsimp [low];omega]
      · rfl
    · intro i hi
      let j : Fin S := ⟨low+i,by dsimp [low];omega⟩
      exact ⟨j.isLt.trans_le srcFit,tableFit j,by have := j.isLt; change _+j.val<_;omega,
        by rw [sourceAt i hi];have := (code (Q.address j)).isLt;omega⟩
    · intro i hi
      let j : Fin S := ⟨low+i,by dsimp [low]; omega⟩
      rw [sourceAt i hi]
      exact blocks j
    · intro i hi k hk
      have hk' := (code (Q.address ⟨low+k,by dsimp [low];omega⟩)).isLt
      rw [sourceAt k (by omega)]
      let j : Fin S := ⟨low+i,by dsimp [low]; omega⟩
      exact ⟨(protect _ hk').1 j,(protect _ hk').2.1 j⟩
  have orig (i : ℕ) (hi : i<r*2) : railOfNat rail (i/2)*2+i%2<S := by
    have h : i/2<r := by omega
    have v := (rail ⟨i/2,h⟩).isLt
    simp only [railOfNat,dite_eq_left h]
    omega
  have saved (a : ℕ) (keep : ∀ i<(n+1)^k*(q*d),P.source.literal+i≠a) :
      P.scattered m a=P.initialized m a := by
    rw [stored]
    apply untouched
    intro i hi
    simp only [dest,dite_eq_left (show low+i<S from by dsimp [low];omega)]
    exact keep _ (Fin.isLt _)
  have final : P.output m=image Q rail P.source.literal P.source.dest low P.literals fetch (P.initialized m) := by
    unfold output
    rw [ends,endpoints_image P.source (r*2) _ (railOfNat rail) spanFit two endFit]
    · unfold image
      rw [←stored]
      apply writeRows_congr
      · exact fun _ _=>rfl
      · intro i hi
        let j : Fin S := ⟨_,orig i hi⟩
        have lookup := saved _ (fun x hx=>(protect x hx).1 j)
        change P.scattered m (P.source.blocks+j.val/P.source.span)+((j.val%P.source.span:ℕ):Word W) = endpointWord Q rail i
        rw [lookup,blocks j]
        simpa only [slotOfNat,dite_eq_left (orig i hi)] using endpoint_image (W:=W) Q rail i hi
    · intro i hi
      have e : i/2<r := by omega
      exact (saved _ (fun j h=>(protect j h).2.2 ⟨_,e⟩)).trans (ranks i hi)
    · intro i hi
      let j : Fin S := ⟨_,orig i hi⟩
      exact ⟨by omega,j.isLt.trans_le srcFit,tableFit j,by omega⟩
    · intro i hi k hk
      have e : i/2<r := by omega
      exact ⟨(destProtect k (by omega)).2 ⟨_,e⟩,(destProtect k (by omega)).1 ⟨_,orig i hi⟩⟩
  rw [final]
  constructor
  · exact readbacks Q rail direction paired _ _ _ _ fetch _ bitFit regions init copied off
  · intro a endsApart pinsApart
    unfold image
    rw [untouched _ _ _ _ _ (fun i hi=>by omega)]
    apply untouched
    intro i hi
    let j : Fin S := ⟨low+i,by dsimp [low];omega⟩
    have dh : dest Q code P.source.literal low i=P.source.literal+(code (Q.address j)).val := dite_eq_left j.isLt
    rw [dh]
    have bound := (code (Q.address j)).isLt
    omega

end
end Hierarchy.GridPinPublisher

end OAI
