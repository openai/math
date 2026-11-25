import OAI.Computability.BorderVNP.DiagonalExternalFragmentPlacedOrder
import OAI.Computability.BorderVNP.DiagonalExternalFragmentCover

/-! # The stable live-delivery subsequence in each final supplied slab -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.Fragments

open Crossing Packing Packing.CellAddresses Packing.Directory
open scoped Classical

variable {D C m R r w link V g entries desc : ℕ}
    (N : Network D (FreeBlock R V) (fun _ => g)) (cell : N.Site → Fin C) (edgeID : N.Edge ↪ Fin m)
    (pp lp : ℕ → ℕ × ℕ) (placement : LivePlacement N cell edgeID finProdFinEquiv.toEmbedding lp)
    (supplied base : ℕ → ℕ) (privateAfter : ∀ j : Fin entries, supplied (pp j.val).1 ≤ (pp j.val).2)
    (hg : 0 < g) (room : r*(2*w+R*link) ≤ V*g)
local notation "dir" => freeDirectory R r w link V g entries desc

private theorem start_transport {a : FreeBlock R V} {c c' : Fin C} (h : c=c')
    (h₁ : cell (N.attach a) = c) (h₂ : cell (N.attach a) = c') :
    portStart N cell edgeID c a h₁ = portStart N cell edgeID c' a h₂ := by subst c'; rfl

private theorem separate_ports {a b : FreeBlock R V} (hc : cell (N.attach a) = cell (N.attach b))
    (ho : (finProdFinEquiv a).val < (finProdFinEquiv b).val) :
    portStart N cell edgeID _ a rfl+g ≤ portStart N cell edgeID _ b rfl :=
  (start_transport N cell edgeID hc rfl hc ▸ port_before N cell edgeID hc rfl ho)

private theorem tile_ordinal_before {a a' : Fin (R+1)} {i i' : Fin V} (h : a < a' ∨ a = a' ∧ i < i') :
    (finProdFinEquiv (a,i)).val < (finProdFinEquiv (a',i')).val := by
  change i.val+V*a.val < i'.val+V*a'.val
  rcases h with h | ⟨rfl,hi⟩
  · have hb := Nat.mul_le_mul_left V (show a.val+1 ≤ a'.val from h)
    rw [Nat.mul_succ] at hb
    have := i.isLt
    omega
  · exact Nat.add_lt_add_right hi _

include placement privateAfter hg room in
/-- A positive later live candidate in the same cell begins only after
the entire preceding interval, in the physical ordering of the directory. -/
theorem candidate_ordered {i j : Fin (dir).candidates} {x y : Quad}
    (lt : i < j) (hx : live supplied base ((dir).row pp lp i) = some x)
    (hy : live supplied base ((dir).row pp lp j) = some y) (same : x.cell = y.cell) :
    x.start+x.width ≤ y.start := by
  obtain ⟨a,p,f,k,xi,xr⟩ := retained_live_candidate (dir) pp lp supplied base privateAfter i hx
  obtain ⟨a',p',f',k',yi,yr⟩ := retained_live_candidate (dir) pp lp supplied base privateAfter j hy
  rw [xr] at hx
  rw [yr] at hy
  obtain ⟨t,tx,cx,sx,wx,px,cap⟩ := located_live N cell edgeID lp placement hg room supplied base a p f k hx
  obtain ⟨u,ty,cy,sy,_,py,_⟩ := located_live N cell edgeID lp placement hg room supplied base a' p' f' k' hy
  let l := slice (fieldStart r w R link p f) w g k
  let l' := slice (fieldStart r w R link p' f') w g k'
  change t.val = l.1/g at tx
  change u.val = l'.1/g at ty
  change x.start = portStart N cell edgeID _ (a,t) rfl + l.1%g at sx
  change y.start = portStart N cell edgeID _ (a',u) rfl + l'.1%g at sy
  change x.width = l.2 at wx
  change l.1%g+l.2 ≤ g at cap
  have hc : cell (N.attach (a,t)) = cell (N.attach (a',u)) := Fin.ext (cx.symm.trans (same.trans cy))
  have idx := (show (dir).liveIndex a p f k < (dir).liveIndex a' p' f' k' from xi ▸ yi ▸ lt)
  have before := live_slice_order idx px py
  change a < a' ∨ a = a' ∧ l.1+l.2 ≤ l'.1 at before
  rw [sx,wx,sy]
  have apart (h : a < a' ∨ a = a' ∧ t < u) :
      portStart N cell edgeID _ (a,t) rfl+l.1%g+l.2 ≤ portStart N cell edgeID _ (a',u) rfl+l'.1%g := by
    have ord := separate_ports N cell edgeID hc (tile_ordinal_before h)
    omega
  rcases before with h | ⟨rfl,h⟩
  · exact apart (.inl h)
  · have du : t.val ≤ u.val := tx.trans_le ((Nat.div_le_div_right (show l.1 ≤ l'.1 by omega)).trans_eq ty.symm)
    rcases lt_or_eq_of_le du with du | du
    · exact apart (.inr ⟨rfl,du⟩)
    · obtain rfl := Fin.ext du
      have d₁ := Nat.mod_add_div l.1 g
      have d₂ := Nat.mod_add_div l'.1 g
      rw [← tx] at d₁
      rw [← ty] at d₂
      omega

include placement privateAfter hg room in
/-- The actual compact seven-word table retains this order after the private
slots and empty rows have been discarded. -/
theorem livePass_ordered (c : ℕ) : (liveQuads (dir) pp lp supplied base).Pairwise
    (fun x y => x.cell = c → y.cell = c → x.start+x.width ≤ y.start) := by
  unfold liveQuads
  rw [Layout.directory_eq_populated,List.filterMap_map]
  apply List.pairwise_filterMap.mpr
  have increasing : ((dir).populated pp lp).Pairwise (· < ·) := List.pairwise_lt_range.filter _
  apply List.Pairwise.imp_of_mem _ increasing
  intro i j hi hj hlt x hx y hy cx cy
  have bi := List.mem_range.mp (List.mem_filter.mp hi).1
  have bj := List.mem_range.mp (List.mem_filter.mp hj).1
  exact candidate_ordered N cell edgeID pp lp placement supplied base privateAfter hg room
    (i := ⟨i,bi⟩) (j := ⟨j,bj⟩) hlt hx hy (cx.trans cy.symm)

end Diagonal.ExternalSew.Fragments

end BorderVNP
end Computability
end OAI
