import OAI.Hierarchy.TaggedWireSideSites
import OAI.Hierarchy.TaggedWireTurnOffsets

namespace OAI
/-! # Private scalar read at the actual signed source or occurrence of a turn -/
noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph AdaptiveProbe
open scoped Classical
variable {S n m h : ℕ} (old : Fin n→Chord S) (edge : Fin m→Chord S)
    (route : Fin n→List (Fin m)) (bits : Fin n→ℕ)
    (ord : Fin h≃Σi,Fin (route i).length)

def ValidRef (i : Fin n) (s : Fin S) : TurnRef→Prop
  | .inl b=>(rowGraph old).vertex i b=s
  | .inr (j,b)=>∃ ht:j<(route i).length,(rowGraph edge).vertex ((route i).get ⟨j,ht⟩) b=s

/-- Both entries of an indexed boundary really belong to the very same site.
This is what allows physically local old and new role reads. -/
theorem valid_pair (i : Fin n) (sp : Spine (rowGraph edge) (old i).1.1 (route i) (old i).1.2)
    (u : Fin ((route i).length+1)) :
    let pair:=sp.sides (.inl false) (.inl true) 0 u
    ValidRef old edge route i (sp.visit u) pair.1 ∧ ValidRef old edge route i (sp.visit u) pair.2 := by
  dsimp only
  constructor
  · induction u using Fin.cases with
    | zero=>rw [Spine.sides_first,Spine.visit_zero];rfl
    | succ j=>
      obtain ⟨side,_,endp,_,loc⟩:=Spine.adjacent sp (.inl false) (.inl true) 0 j
      rw [endp]
      simpa only [Nat.zero_add] using (show ValidRef old edge route i (sp.visit j.succ) (.inr (j.val,!side)) from
        ⟨j.isLt,loc.symm⟩)
  · induction u using Fin.lastCases with
    | last=>rw [Spine.sides_last,Spine.visit_last];rfl
    | cast j=>
      obtain ⟨side,startp,_,loc,_⟩:=Spine.adjacent sp (.inl false) (.inl true) 0 j
      rw [startp]
      simpa only [Nat.zero_add] using (show ValidRef old edge route i (sp.visit j.castSucc) (.inr (j.val,side)) from
        ⟨j.isLt,loc.symm⟩)

/-- Address origin in the paid output. Both old ends start at zero; each
new occurrence starts at its accumulated earlier positive width. -/
def refStart (i : Fin n) : TurnRef→ℕ
  | .inl _=>0
  | .inr (j,_)=>if ht:j<(route i).length then NativeSlot.start route bits ord i ⟨j,ht⟩ else 0

def refRole (before : Fin n→Bool→ℕ) (after : Fin m→Bool→ℕ) (i : Fin n) : TurnRef→ℕ
  | .inl b=>before i b
  | .inr (j,b)=>if ht:j<(route i).length then after ((route i).get ⟨j,ht⟩) b else 0

theorem read_private (i : Fin n) (j : Fin (bits i)) (s : Fin S) (side : TurnRef)
    (ok : ValidRef old edge route i s side)
    (x : BitState (bitGraph (rowGraph old) bits) s) (y : ∀d,Fin (2^routeLoad route bits d))
    (before : Fin n→Bool→ℕ) (after : Fin m→Bool→ℕ) (plane : ℕ→ℕ→Bool)
    (prior : ∀b (site:(rowGraph old).vertex i b=s),plane (before i b) j.val=
      x ⟨(⟨i,j⟩,b),by cases b <;>exact site⟩)
    (paid : ∀u : Fin (route i).length,∀b,(rowGraph edge).vertex ((route i).get u) b=s→
      plane (after ((route i).get u) b) (NativeSlot.start route bits ord i u+j.val)=
        (y ((route i).get u)).val.testBit (NativeSlot.start route bits ord i u+j.val)) :
    plane (refRole route before after i side) (refStart route bits ord i side+j.val)=
      readTurn (rowGraph edge) (rowGraph old) route bits (NativeSlot.allocation route bits ord) ⟨i,j⟩ s
        (x,(bitGraph (rowGraph edge) (routeLoad route bits)).atVertex (wordBitsEquiv _ y) s) side := by
  rcases side with b|⟨u,b⟩
  · rw [turn_start_bit old edge route bits ord i j b s ok,refRole,refStart,Nat.zero_add]
    exact prior b ok
  · obtain ⟨bound,atSite⟩:=ok
    let pos : Fin (route i).length:=⟨u,bound⟩
    rw [turn_paid_bit old edge route bits ord i pos j b s atSite x y]
    simpa only [refRole,refStart,dite_eq_left bound] using paid pos b atSite

end Hierarchy.WireTelescope

end
end OAI
