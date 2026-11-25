import OAI.Computability.BorderVNP.PackedDirectoryIncoming
import OAI.Computability.BorderVNP.CubePhysicalPaddingPublic

/-! # Incidence at the physical cells of the routed batch

Both inputs to the public label selector count individual lanes. Their sparse directory
pointers and widths come from the same packed network and prefix pass. The incidence
bound follows from the local expanded record count of that network.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs

open Crossing Shortening CellAddresses CellAddressCircuit CellAddressPhysical RoutingISA Finset
open Cube.Physical Cube.Balancing
open scoped Classical
open private sum_lanes embedded_sum_le from OAI.Computability.BorderVNP.PackedDirectoryIncoming

variable {D C : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}

/-- The live cable incidence count used by the balancing scan is bounded by the
expanded weights at the same physical cell. -/
theorem cable_incidence_le_records (N : Network D P bits) (cell : N.Site → Fin C)
    (prior payload : N.Site → ℕ) (c : Fin C) :
    (univ.filter (fun b : LiveBit N cell =>
      c ∈ ({crossSrc N cell b.1, crossDst N cell b.1} : Finset (Fin C)))).card ≤
      localRecords N true prior payload (fun v => cell v = c) := by
  let hit (e : N.Edge) := c ∈ ({cell (N.src e), cell (N.dst e)} : Finset (Fin C))
  rw [card_filter, sum_lanes (crossWidth N cell) (fun e => hit e.val),testedWidth]
  let inc (e : N.Edge) :=
    (if cell (N.src e) = c then recordCost true (N.width e) else 0) +
      if cell (N.dst e) = c then recordCost true (N.width e) else 0
  have first : (∑ e : N.CrossingEdge cell, if hit e.val then N.width e.val else 0) ≤
      ∑ e : N.CrossingEdge cell, inc e.val := by
    apply sum_le_sum
    intro e _
    by_cases hs : c = cell (N.src e.val) <;> by_cases hd : c = cell (N.dst e.val) <;>
      simp [hit,inc,hs,hd,eq_comm,recordCost] <;> omega
  have second := embedded_sum_le (Function.Embedding.subtype (fun e : N.Edge => cell (N.src e) ≠ cell (N.dst e))) inc
  have ends : (∑ e, inc e) =
      testedWidth (fun e => recordCost true (N.width e)) (fun e => cell (N.src e) = c) +
      testedWidth (fun e => recordCost true (N.width e)) (fun e => cell (N.dst e) = c) := by
    unfold inc testedWidth
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro e _
    by_cases hs : cell (N.src e) = c <;> by_cases hd : cell (N.dst e) = c <;> simp [hs,hd]
  have f := first.trans (second.trans_eq ends)
  have hb : testedWidth (fun e => recordCost true (N.width e)) (fun e => cell (N.src e) = c) +
      testedWidth (fun e => recordCost true (N.width e)) (fun e => cell (N.dst e) = c) ≤
      localRecords N true prior payload (fun v => cell v = c) := by
    unfold localRecords
    dsimp only
    omega
  refine le_trans ?_ (f.trans hb)
  apply le_of_eq
  apply sum_congr rfl
  intro e _
  by_cases he : hit e.val <;> simp [he,crossWidth]

/-- The positive seven-word delivery rows in the actual private-prefix image give the
per-cell incoming-bit incidence used by the balancing scan, including any pinned field. -/
theorem Image.private_incoming {s m n d k w W : ℕ} {σ : Type*} [Fintype σ]
    (N : Network D P bits) (cell : N.Site → Fin C) (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s)
    (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n) (F : Fields s m n C d k w σ) {x : σ → Bool}
    (net : Represents N cell aux siteID edgeID portID F x) (code : ∀ c, (F.cells c).val = c.val)
    (fit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^w)
    (dir : Directory.Layout) (old : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
    (width : ∀ p, bits (live p) = dir.block) (bound : dir.DestinationBounds)
    (head origin gap : ℕ) (before after : ℕ → ℕ)
    (img : Image F (siteID ∘ old) (portID ∘ live ∘ finProdFinEquiv.symm) x origin before)
    (run : (privateLayout head origin m C dir.entries dir.description gap).Image before dir.entries after)
    (room : (privateLayout head origin m C dir.entries dir.description gap).Fits W before)
    (prior payload : N.Site → ℕ) (desc : ∀ j, dir.description ≤ payload (old j)) :
    let pp := Directory.ISA.placement after (bases origin m C dir.entries).privatePairs
    let lp := Directory.ISA.placement after (bases origin m C dir.entries).livePairs
    let rows := dir.directory pp lp
    ∀ (recv : Fin rows.length → Fin C), (∀ i, (recv i).val = rows[i.val].cell) → ∀ c,
      (univ.filter (fun b : Bits (fun i : Fin rows.length => rows[i.val].width) => c = recv b.1)).card ≤
        localRecords N true prior payload (fun v => cell v = c) := by
  intro pp lp rows recv atCell c
  let p := img.networkPlacement N cell aux siteID edgeID portID F net code fit dir old live width
    head origin gap before after run room
  have oldCell (j : Fin dir.entries) : (pp j.val).1 = (cell (old j)).val :=
    congrArg Prod.fst (p.entry (.inl j))
  have liveCell (a : Fin dir.teams × Fin dir.sites) :
      (lp (a.1.val*dir.sites+a.2.val)).1 = (cell (N.attach (live a))).val :=
    congrArg Prod.fst (p.entry (.inr a))
  have h := dir.incoming_le_records N cell pp lp bound old live prior payload desc width oldCell liveCell c
  rw [card_filter, sum_lanes (fun i : Fin rows.length => rows[i.val].width) (fun i => c = recv i)]
  convert h using 2
  funext i
  exact propext (Fin.ext_iff.trans ((eq_comm).trans (by rw [atCell])))

end Packing.RoutingOutputs

end BorderVNP
end Computability
end OAI
