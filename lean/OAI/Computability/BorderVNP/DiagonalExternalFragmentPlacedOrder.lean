import OAI.Computability.BorderVNP.DiagonalExternalFragmentLiveOrder
import OAI.Computability.BorderVNP.DiagonalExternalFragmentCandidates

/-! # Live-fragment order after placement at the actual final cells -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.Fragments

open Crossing Packing Packing.CellAddresses Packing.Directory
open scoped Classical
open private end_le_start from OAI.Computability.BorderVNP.PackedCellSlabs
open private quotient from OAI.Computability.BorderVNP.PackedDirectoryInverse

variable {D C m R r w link V g entries desc : ℕ}
    (N : Network D (FreeBlock R V) (fun _ => g)) (cell : N.Site → Fin C) (edgeID : N.Edge ↪ Fin m)
    (lp : ℕ → ℕ × ℕ) (placement : LivePlacement N cell edgeID finProdFinEquiv.toEmbedding lp)

local notation "dir" => freeDirectory R r w link V g entries desc
local notation "ord" => finProdFinEquiv.toEmbedding

/-- The dense base of an actual free word when viewed inside its receiving cell. -/
noncomputable def portStart (c : Fin C) (a : FreeBlock R V) (atCell : cell (N.attach a) = c) :=
  CellSlabs.start (suppliedRow N cell c edgeID ord) (suppliedWidth N cell c) (.inr ⟨a,atCell⟩)

include placement in
theorem placed_at (c : Fin C) (a : FreeBlock R V) (atCell : cell (N.attach a) = c) :
    lp (a.1.val*V+a.2.val) = (c.val,portStart N cell edgeID c a atCell) := by
  subst c
  exact placement a

/-- Two distinct surviving free words in the same cell have disjoint
ordered intervals in the actual external slab. -/
theorem port_before {c : Fin C} {a b : FreeBlock R V} (ha : cell (N.attach a) = c)
    (hb : cell (N.attach b) = c) (order : (finProdFinEquiv a).val < (finProdFinEquiv b).val) :
    portStart N cell edgeID c a ha+g ≤ portStart N cell edgeID c b hb := by
  let left : Supplied N cell c := .inr ⟨a,ha⟩
  let right : Supplied N cell c := .inr ⟨b,hb⟩
  have ids : suppliedRow N cell c edgeID ord left < suppliedRow N cell c edgeID ord right := by
    change (m+m)+(finProdFinEquiv a).val < (m+m)+(finProdFinEquiv b).val
    omega
  exact end_le_start (suppliedRow N cell c edgeID ord) (suppliedWidth N cell c) ids

include placement in
/-- Relate the actual directory record to the original team's physical tile,
including both the clipped extent and the dense supplied start in its final cell. -/
theorem located_live (hg : 0 < g) (room : r*(2*w+R*link) ≤ V*g)
    (supplied base : ℕ → ℕ) (u : Fin (R+1)) (p : Fin r) (f : Fin 2) (k : Fin (w/g+2))
    {q : Quad} (h : live supplied base ((dir).liveRow lp u p f k) = some q) :
    let a := fieldStart r w R link p f
    let sl := slice a w g k
    ∃ site : Fin V, site.val = sl.1/g ∧ q.cell = (cell (N.attach (u,site))).val ∧
      q.start = portStart N cell edgeID _ (u,site) rfl + sl.1%g ∧ q.width = sl.2 ∧
      0 < sl.2 ∧ sl.1%g+sl.2 ≤ g := by
  let a := fieldStart r w R link p f
  let sl := slice a w g k
  let j := a/g+k.val
  have code : (dir).liveRow lp u p f k =
      ⟨u,p,f,sl.1-a,(lp (u.val*V+j)).1,(lp (u.val*V+j)).2+(sl.1-j*g),sl.2⟩ := by
    simp [Layout.liveRow,Layout.stride,freeDirectory,fieldStart,sl,j,a]
  rw [code] at h
  unfold live at h
  split at h
  next yes =>
    have pos : 0 < sl.2 := yes.2
    have hh := slice_bounds (a := a) (k := k.val) pos
    have left : j*g ≤ sl.1 := hh.2.2.1
    have right : sl.1+sl.2 ≤ j*g+g := by simpa [j,Nat.succ_mul] using hh.2.2.2
    have block : sl.1/g = j := quotient hg left (by omega)
    have index : j < V := by
      have e := (slice_bounds (a := a) (k := k.val) pos).2.1.trans (field_end p f)
      have cap := (Nat.mul_le_mul_right (2*w+R*link) p.isLt).trans room
      have last : sl.1+sl.2 ≤ V*g := e.trans cap
      have : j*g < V*g := by omega
      exact Nat.lt_of_mul_lt_mul_right this
    let site : Fin V := ⟨j,index⟩
    have address := placement (u,site)
    have x : sl.1-j*g = sl.1%g := by
      have hx := Nat.mod_add_div sl.1 g
      rw [block,Nat.mul_comm g j] at hx
      omega
    have spanRoom : sl.1%g+sl.2 ≤ g := by
      have hx := Nat.mod_add_div sl.1 g
      rw [block,Nat.mul_comm g j] at hx
      omega
    obtain rfl := Option.some.inj h
    exact ⟨site,block.symm,congrArg Prod.fst address,by rw [congrArg Prod.snd address,x]; rfl,
      rfl,pos,spanRoom⟩
  next no => simp at h

end Diagonal.ExternalSew.Fragments

end BorderVNP
end Computability
end OAI
