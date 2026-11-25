import OAI.Hierarchy.TaggedWireTurnData
import OAI.Hierarchy.ProtocolRAMTurnRead

namespace OAI
/-! # Exact prefix and end-of-word reads at each side of an emitted physical turn -/
noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph AdaptiveProbe
open ProtocolRAMTurnItinerary
open scoped Classical

variable {S n m h : ℕ} (old : Fin n→Chord S) (edge : Fin m→Chord S)
    (route : Fin n→List (Fin m)) (bits : Fin n→ℕ)
    (ord : Fin h≃Σi,Fin (route i).length)

/-- The received prefix is zero on an original source/destination socket.
An internal prefix is the sum of the widths of exactly the preceding hops
using the same resulting paid edge. Both sides refer to the same runtime
occurrence addresses as the turn role program. -/
theorem start_sides (i : Fin n) (sp : Spine (rowGraph edge) (old i).1.1 (route i) (old i).1.2)
    (j : Fin ((route i).length+1)) (t : Turn) (v : Values)
    (len : t.length=(route i).length) (pos : t.position=j.val)
    (address : Fin (route i).length→ℕ)
    (previous : ∀q : Fin (route i).length,q.succ=j→t.occurrence false=address q)
    (next : ∀q : Fin (route i).length,q.castSucc=j→t.occurrence true=address q)
    (read : ∀q : Fin (route i).length,v.starts (address q)=NativeSlot.start route bits ord i q) :
    let z:=sp.sides (.inl false) (.inl true) 0 j
    t.start v false=refStart route bits ord i z.1 ∧ t.start v true=refStart route bits ord i z.2 := by
  dsimp only
  constructor
  · by_cases first:j.val=0
    · have eq:j=0:=Fin.ext first
      have yes:t.boundary false:=by simpa [Turn.boundary,pos] using first
      simp [Turn.start,yes,eq,refStart]
    · let q : Fin (route i).length:=⟨j.val-1,by have:=j.isLt;omega⟩
      have eq:q.succ=j:=Fin.ext (by change j.val-1+1=j.val;omega)
      have no:¬t.boundary false:=by simpa [Turn.boundary,pos] using first
      obtain ⟨b,_,back,_,_⟩:=Spine.adjacent sp (.inl false) (.inl true) 0 q
      rw [eq] at back
      simpa only [Turn.start,ite_eq_right no,previous q eq,back,Nat.zero_add,refStart,dite_eq_left q.isLt] using read q
  · by_cases last:j.val=(route i).length
    · have eq:j=Fin.last (route i).length:=Fin.ext last
      have yes:t.boundary true:=by simpa [Turn.boundary,pos,len] using last
      simp [Turn.start,yes,eq,refStart]
    · let q : Fin (route i).length:=⟨j.val,by have:=j.isLt;omega⟩
      have eq:q.castSucc=j:=Fin.ext rfl
      have no:¬t.boundary true:=by simpa [Turn.boundary,pos,len] using last
      obtain ⟨b,fwd,_,_,_⟩:=Spine.adjacent sp (.inl false) (.inl true) 0 q
      rw [eq] at fwd
      simpa only [Turn.start,ite_eq_right no,next q eq,fwd,Nat.zero_add,refStart,dite_eq_left q.isLt] using read q

/-- One uniform shelf width covers an old word and the exact live prefix of
any new half-port. In particular a repeated physical edge never overflows
the aperture at its last occurrence. -/
theorem ref_extent (i : Fin n) (s : Fin S) (t : TurnRef) (valid : ValidRef old edge route i s t)
    (positive : 0<bits i) (cap : ℕ) (oldFit : bits i≤cap) (newFit : ∀e,routeLoad route bits e≤cap) :
    refStart route bits ord i t+bits i≤cap := by
  rcases t with b|⟨j,b⟩
  · simpa [refStart] using oldFit
  · obtain ⟨bound,_⟩:=valid
    simpa only [refStart,dite_eq_left bound] using
      (NativeSlot.start_room route bits ord i ⟨j,bound⟩ positive).trans (newFit _)

end Hierarchy.WireTelescope

end
end OAI
