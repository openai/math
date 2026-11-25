import OAI.Computability.BorderVNP.DiagonalExternalFragmentPadding
import OAI.Computability.BorderVNP.CubeHostScatterReadback

/-! # Host-cable scattering preserves the grouped literal and pin memory

The owned endpoint writes only its true crossing-word interval. A grouped
argument lies after that interval in the same cell, or in another disjoint
fixed-stride cell bank.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.Fragments

open Crossing Packing Packing.CellAddresses BorderVNP.Cube
open scoped Classical

variable {D R V g C m n : ℕ} (N : Network D (FreeBlock R V) (fun _ => g))
    (cell : N.Site → Fin C) (edgeID : N.Edge ↪ Fin m) (portID : FreeBlock R V ↪ Fin n)
    {lp : ℕ → ℕ × ℕ} (place : LivePlacement N cell edgeID portID lp)
    {l : HostScatter.Layout} {mem : ℕ → ℕ} (rows : CableRows N cell edgeID portID l mem)

include place rows in
/-- The original physical cell word of any grouped port lane survives every
owned endpoint store in any prefix of the cable scatter. -/
theorem host_prefix_free_lane (origin stride : ℕ)
    (bases : ∀ c : Fin C, mem (l.cells+2*c.val+1) = origin+c.val*stride)
    (room : ∀ c : Fin C, suppliedSize N cell c ≤ stride) (seen : ℕ) (bound : seen ≤ l.count)
    (a : Σ _ : FreeBlock R V, Fin g) :
    let pos := laneAddress lp a
    let addr := origin+pos.1*stride+pos.2
    l.prefix mem seen addr = mem addr := by
  intro pos addr
  let u := cell (N.attach a.1)
  have atCell : pos.1 = u.val := congrArg Prod.fst (place a.1)
  let capacities := fun i : ℕ => if h : i < C then suppliedSize N cell ⟨i,h⟩ else 0
  have counts (c : Fin C) : capacities c.val = suppliedSize N cell c := by simp [capacities,c.isLt]
  have cap := live_base_fits N cell edgeID portID place capacities counts a.1
  change (lp (a.1.1.val*V+a.1.2.val)).2+g ≤ capacities pos.1 at cap
  rw [atCell,counts] at cap
  have within : pos.2 < stride := (Nat.add_lt_add_left a.2.isLt _).trans_le (cap.trans (room u))
  apply l.prefix_outside
  intro i hi side owned
  let q : Quad := ⟨l.cell mem i side,mem (l.relative+2*i+side.toNat),l.dest mem i side,l.width mem i⟩
  have read : cable l mem side i = some q := ite_eq_right (not_or.mpr ⟨owned.2.1,owned.1⟩)
  obtain ⟨e,_,_,he⟩ := (cable_some_iff rows (hi.trans_le bound) side q).mp read
  let c := endpointCell N cell side e
  let start := endpointRow N cell edgeID portID side e
  have hd := congrArg Quad.source he
  have hw := congrArg Quad.width he
  change l.dest mem i side = mem (l.cells+2*c.val+1)+start at hd
  change l.width mem i = N.width e.val at hw
  rw [bases c] at hd
  change origin+pos.1*stride+pos.2 < l.dest mem i side ∨
    l.dest mem i side+l.width mem i ≤ origin+pos.1*stride+pos.2
  rw [hd,hw,atCell]
  rcases lt_trichotomy c u with less | same | greater
  · have endFits : start + N.width e.val ≤ stride := (endpointRow_fits N cell edgeID portID side e).trans (room c)
    have advance := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt (show c.val < u.val from less))
    rw [Nat.succ_mul] at advance
    exact Or.inr (by omega)
  · have before := endpoint_before_free N cell edgeID portID place side e a.1 same
    change start+N.width e.val ≤ (lp (a.1.1.val*V+a.1.2.val)).2 at before
    have up : (lp (a.1.1.val*V+a.1.2.val)).2 ≤ pos.2 := Nat.le_add_right ..
    rw [same]
    exact Or.inr (by omega)
  · have advance := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt (show u.val < c.val from greater))
    rw [Nat.succ_mul] at advance
    exact Or.inl (by omega)

end Diagonal.ExternalSew.Fragments

end BorderVNP
end Computability
end OAI
