import OAI.Computability.BorderVNP.PackedRoutingPlaced
import OAI.Computability.BorderVNP.PackedRoutingIncidence
import OAI.Computability.BorderVNP.PackedRoutingTeamAgreement

/-! # Native delivery rows determined by the sewn history before any team runs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs.NativeDemands

open Crossing CellAddresses CellAddressCircuit CellAddressPhysical RoutingISA Directory Directory.PrivateBank
open scoped Classical

variable {D C ne np : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → Fin C) (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)
    (dir : Directory.Layout) (old : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P) (gap : ℕ)

/-- The private descriptor prefix follows genuine supplied slots and the report gap.
Live destinations use the original supplied-port row ordinal. -/
noncomputable def destination (k : dir.DestinationKey) : Fin C × ℕ :=
  let sc := Sum.elim (fun x : SuppliedWord N cell => x.1) (id : Fin C → Fin C)
  let sw := Sum.elim (supplyWidth N cell) (fun _ : Fin C => gap)
  let si := PrivateBank.reserveID (C:=C) (suppliedID N cell edgeID portID)
  let owner := Sum.elim sc (cell ∘ old)
  let widths := Sum.elim sw (fun _ : Fin dir.entries => dir.description)
  let key := Sum.elim Sum.inr (fun u => Sum.inl (Sum.inl (suppliedPort N cell (live u)))) k
  (owner key,DataSlabs.base owner (PrivateBank.numbered si) widths key)

private def pair {I : Type} (f : I → Fin C × ℕ) (i : I) := ((f i).1.val,(f i).2)

local notation "coords" => destination N cell edgeID portID dir old live gap
/-- Fully defined address table, with zero in inaccessible private slots. -/
noncomputable def privatePair (j : ℕ) : ℕ × ℕ := if h : j < dir.entries then pair coords (.inl ⟨j,h⟩) else (0,0)
/-- Fully defined team-major address table for live grouped words. -/
noncomputable def livePair (j : ℕ) : ℕ × ℕ :=
  if h : j < dir.teams*dir.sites then pair coords (.inr (finProdFinEquiv.symm ⟨j,h⟩)) else (0,0)

local notation "pp" => privatePair N cell edgeID portID dir old live gap
local notation "lp" => livePair N cell edgeID portID dir old live gap

theorem keyPair (k : dir.DestinationKey) : dir.keyPlacement pp lp k = pair coords k := by
  cases k with
  | inl j => exact dite_eq_left j.isLt
  | inr p =>
    have val : (finProdFinEquiv p).val = p.1.val*dir.sites+p.2.val := by
      simp only [finProdFinEquiv_apply_val]; ring
    change lp (p.1.val*dir.sites+p.2.val) = _
    rw [←val]
    simp only [livePair,dite_eq_left (finProdFinEquiv p).isLt,Fin.eta,Equiv.symm_apply_apply]

/-- The complete positive-length seven-word directory determined by the sewn network. -/
noncomputable def rows := dir.directory pp lp

/-- Any real invocation that returns on this history emits this very directory,
including the source offsets and the absolute destination slots. -/
theorem rows_eq_native {s d k w word : ℕ} {σ : Type} [Fintype σ] (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s)
    (F : Fields s ne np C d k w σ) (x : σ → Bool) (head origin : ℕ) (before after : ℕ → ℕ)
    (net : Represents N cell aux siteID edgeID portID F x) (code : ∀ c, (F.cells c).val = c.val)
    (fit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^w)
    (bounds : dir.DestinationBounds) (width : ∀ p, bits (live p) = dir.block)
    (img : Image F (siteID ∘ old) (portID ∘ live ∘ finProdFinEquiv.symm) x origin before)
    (run : (privateLayout head origin ne C dir.entries dir.description gap).Image before dir.entries after)
    (room : (privateLayout head origin ne C dir.entries dir.description gap).Fits word before) :
    rows N cell edgeID portID dir old live gap = dir.directory
      (ISA.placement after (bases origin ne C dir.entries).privatePairs)
      (ISA.placement after (bases origin ne C dir.entries).livePairs) := by
  let image := img.networkPlacement N cell aux siteID edgeID portID F net code fit dir old live width
    head origin gap before after run room
  apply dir.directory_congr_keys _ _ _ _ bounds
  intro k
  refine (keyPair N cell edgeID portID dir old live gap k).trans ?_
  cases k with
  | inl j => exact (image.entry (.inl j)).symm
  | inr p => exact (image.entry (.inr p)).symm

local notation "rows₀" => rows N cell edgeID portID dir old live gap

private theorem positive_width (i : Fin (rows₀).length) : 0 < rows₀[i.val].width := by
  have h : rows₀[i.val] ∈ rows₀ := List.getElem_mem i.isLt
  exact of_decide_eq_true (List.mem_filter.mp h).2

/-- The native cell ordinal for each occupied delivery. -/
noncomputable def receiver (bounds : dir.DestinationBounds) (i : Fin (rows₀).length) : Fin C :=
  let lane : dir.PopulatedBit pp lp := ⟨i,0,positive_width N cell edgeID portID dir old live gap i⟩
  (coords (dir.destinationKey pp lp bounds (dir.rawBit pp lp lane)).1).1

/-- Every typed receiver is precisely the cell on the published seven-word row. -/
theorem receiver_val (bounds : dir.DestinationBounds) (i : Fin (rows₀).length) :
    (receiver N cell edgeID portID dir old live gap bounds i).val = rows₀[i.val].cell := by
  let lane : dir.PopulatedBit pp lp := ⟨i,0,positive_width N cell edgeID portID dir old live gap i⟩
  let raw := dir.rawBit pp lp lane
  let dest := dir.destinationKey pp lp bounds raw
  have h := (dir.destinationKey_placement pp lp bounds raw).1
  exact (h.trans (congrArg Prod.fst (keyPair N cell edgeID portID dir old live gap dest.1))).symm.trans
    (congrArg Directory.Row.cell (dir.populatedRow pp lp i)).symm

end Packing.RoutingOutputs.NativeDemands

end BorderVNP
end Computability
end OAI
