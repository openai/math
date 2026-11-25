import OAI.Hierarchy.DescentTerminalGrainProfiles
import OAI.Hierarchy.DescentTerminalExteriorHeaders
import OAI.Hierarchy.DescentTerminalSparseHeader

namespace OAI
/-! # Cable and public width tapes from counts of the actual terminal grains -/

namespace Hierarchy.DescentTerminalGrainProfiles
open Computability.BorderVNP.Crossing DescentTerminalGraphPositions DescentTerminalPorts DescentTerminalCableOrder
open DescentTerminalDenseHeader DescentTerminalDenseWindow DescentTerminalHeaderGroups
open ThreeFlat.Routing
open scoped Classical BigOperators
noncomputable section

variable {D S p : ℕ} {P : Type} [Fintype P] {bits : P→ℕ} (N : Network D P bits)
    (home : N.Site→Fin S) (native : N.Edge ↪ Fin (Fintype.card N.Edge)) (external : P ↪ ℕ)
    (nodes : N.Site ↪ ℕ) (ops : ∀v,DescentKernelHistory.Boundary N v ↪ ℕ)
    (hp : 0<p) (internal : ∀e,p∣N.width e) («public» : ∀z,p∣bits z)
local notation "L" => order N home native p external nodes ops

include hp internal «public»

theorem group_full (i : Fin S) (g : Order.Group L i) (u : Fin (Fintype.card (Order.At L i g))) :
    groupLengths N L i g u=p := by
  unfold groupLengths
  generalize ((Order.inGroup L i g).symm u).val=z
  rcases z with ⟨e,k⟩|⟨z,k⟩
  · exact piece_full hp (internal e) k
  · exact piece_full hp («public» z) k

/-- A pair count measures true distinct p-sized pieces, including a cable whose ends share a host. -/
theorem cable_card (i j : Fin S) (g : Order.Group L i) (near:g.val=some j) :
    Fintype.card (Order.At L i g)=pairMass N home (pair i j)/p := by
  have full:=group_full N home native external nodes ops hp internal «public» i g
  have total:=group_total N home native external nodes ops hp i j g near
  rw [pref_full _ full (le_refl _)] at total
  rw [←total,Nat.mul_div_cancel _ hp]

theorem cable_rows (q : ℕ) (t : ℕ) : blockRows N home native external nodes ops q hp t=
    rows q p (pairMass N home t/p) := by
  unfold blockRows
  split
  next live=>
    let g:=selected N home native external nodes ops hp t live
    have tag:g.tag=t:=selected_tag N home native external nodes ops hp t live
    change chunkRows g.lengths g.small q=_
    have sized : Fintype.card (Order.At L g.site g.group) = pairMass N home t / p := by
      calc
        _ = pairMass N home g.tag / p :=
          cable_card N home native external nodes ops hp internal «public» g.site g.other g.group g.near
        _ = pairMass N home t / p := by rw [tag]
    exact (chunk_rows (q := q) g.lengths g.small
      (group_full N home native external nodes ops hp internal «public» g.site g.group)).trans
      (congrArg (rows q p) sized)
  next zero=>simp [Nat.eq_zero_of_not_pos zero]

/-- Catalogue entries of zero mass consume no row or native header. -/
theorem cable_stream (q limit : ℕ) (keys : List ℕ)
    (sorted : keys.filter (fun t=>decide (0<pairMass N home t))=
      (DescentTerminalSparseHeader.occupied N home limit).sort) :
    keys.flatMap (fun t=>rows q p (pairMass N home t/p))=
      stream N home native external nodes ops q hp limit := by
  let f:=fun t=>rows q p (pairMass N home t/p)
  have skip (l : List ℕ) : (l.filter (fun t=>decide (0<pairMass N home t))).flatMap f=l.flatMap f := by
    induction l with
    | nil=>rfl
    | cons a l ih=>
      by_cases ha:0<pairMass N home a
      · simp [ha,ih]
      · simp [ih,f,Nat.eq_zero_of_not_pos ha]
  change keys.flatMap f=_
  rw [←skip keys,sorted,DescentTerminalSparseHeader.occupied_sort,skip,stream]
  apply List.flatMap_congr
  intro t ht
  exact (cable_rows N home native external nodes ops hp internal «public» q t).symm

theorem public_rows (q : ℕ) (hq:0<q) (i : Fin S) :
    DescentTerminalExteriorHeaders.siteRows (q:=q) N home native external nodes ops i=
      rows q p (DescentTerminalExteriorHeaders.siteMass N home i/p) := by
  unfold DescentTerminalExteriorHeaders.siteRows
  split
  next live=>
    let g : Order.Group L i:=⟨none,live⟩
    have full:=group_full N home native external nodes ops hp internal «public» i g
    have total:=DescentTerminalExteriorHeaders.total N home native external nodes ops hp i g rfl
    rw [pref_full _ full (le_refl _)] at total
    unfold DescentTerminalExteriorHeaders.block
    rw [chunk_rows _ _ full,←total,Nat.mul_div_cancel _ hp]
  next off=>
    have zero:=DescentTerminalExteriorHeaders.site_mass N home native external nodes ops hq hp i
    simp [DescentTerminalExteriorHeaders.siteRows,off,listMass] at zero
    simp [←zero]

theorem public_stream (q : ℕ) (hq:0<q) (k : ℕ) :
    (List.range k).flatMap (fun n=>if h:n<S then
      rows q p (DescentTerminalExteriorHeaders.siteMass N home ⟨n,h⟩/p) else [])=
      DescentTerminalExteriorHeaders.stream (q:=q) N home native external nodes ops k := by
  induction k with
  | zero=>rfl
  | succ k ih=>
    rw [List.range_succ,List.flatMap_append,DescentTerminalExteriorHeaders.stream,ih]
    by_cases hk:k<S
    · simp [hk,public_rows N home native external nodes ops hp internal «public» q hq]
    · simp [hk]

end
end Hierarchy.DescentTerminalGrainProfiles

end OAI
