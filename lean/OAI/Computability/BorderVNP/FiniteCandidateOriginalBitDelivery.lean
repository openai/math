import OAI.Computability.BorderVNP.CellPacketGeometryOriginalDelivery
import OAI.Computability.BorderVNP.CellTeamBitDelivery
import OAI.Computability.BorderVNP.CellPacketGeometryNativePlaces
import OAI.Computability.BorderVNP.CellPacketGeometryHistoryTables
import OAI.Computability.BorderVNP.PackedNativeDemandRows

/-! # Charging each finite private box bit to its occupied physical delivery row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs.NativeDemands

open Crossing Packing

/-- The candidate's actual received operand numbers and widths locate every
positive-length published source row, in the order used by its finite field plan. -/
noncomputable def rowLocations {D C e p : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → Fin C) (edgeID : N.Edge ↪ Fin e) (portID : P ↪ Fin p)
    (dir : Directory.Layout) (original : Fin dir.entries ↪ N.Site)
    (live : (Fin dir.teams × Fin dir.sites) ↪ P) (gap : ℕ) (bounds : dir.DestinationBounds) :
    let list := rows N cell edgeID portID dir original live gap
    Directory.RowLocations list Fin.val (receiver N cell edgeID portID dir original live gap bounds)
      (fun i : Fin list.length => list[i.val].width) :=
  ⟨Function.Embedding.refl _,receiver_val N cell edgeID portID dir original live gap bounds,fun _ => rfl⟩

end Packing.RoutingOutputs.NativeDemands

namespace CellPacketGeometry.History.Native.Terminal

open Crossing Packing Packing.Inherited Packing.Inherited.FrozenTape Packing.RoutingOutputs
open CellSparse CellSparse.Packet CellSparse.Packet.Source CellPacketGeometry.History
open _root_.OAI.Computability.BorderVNP.Cube.TeamRowClock RoutingISA.CellPacket
open VPVNP.BurstRAM RoutingISA
open scoped Classical

variable {a C D n e depth k w cap d t : ℕ} {P σ R B U V E : Type} [Fintype P] [Fintype σ]
    {bits : P → ℕ} (N : Network D P bits) (cell : N.Site → Fin C)
    (siteID : N.Site ↪ Fin a) (edgeID : N.Edge ↪ Fin e) (portID : P ↪ Fin n) (state : N.Site → Site)
    (F : CellAddressCircuit.Fields a e n C depth k w σ) (z : σ → Bool) (cp : 0<C)
    (physical : CellAddressPhysical.Represents N cell (fun v => (state v).size) siteID edgeID portID F z)
    (dir : Packing.Directory.Layout) (original : Fin dir.entries ↪ N.Site)
    (live : (Fin dir.teams × Fin dir.sites) ↪ P) (gap : ℕ)
    (S : FrozenTape.Schema R B) (L : FrozenTape.Schema U V)
    (boxes : Fin a → List (Source.Box (Fin dir.entries))) (known : Fin a → List (List Factor))
    (roster : boxes = originalBoxes (original.trans siteID) known)
    (sh : ∀ r, (S.tags r).length ≤ cap) (lh : ∀ r, (L.tags r).length ≤ cap)
    (priv : Fin (C+1) → E) (rep : Fin (C+1) → List (List E)) (arg : E → ℕ)
    (x : FrozenTape.Pins R B d → Bool) (y : FrozenTape.Pins U V t → Bool) (off box : Fin a → ℕ)

local notation3 (prettyPrint := false) "cells" => TerminalTable.cell F cp z
local notation3 (prettyPrint := false) "G₀" => directory S L boxes sh lh priv rep arg x y cells off box
local notation3 (prettyPrint := false) "sent" => NativeDemands.rows N cell edgeID portID dir original live gap

set_option maxRecDepth 5500 in
set_option maxHeartbeats 1600000 in
include physical roster in
/-- On the measured finite terminal, every bit of every original private
box in a real cell injects into a bit of the emitted seven-word demand
directory at that same cell. Known public factors and unused sites do not
enter this charge. The split includes boxes spanning two processor tails. -/
noncomputable def originalBitDelivery {A G : Type} (recv : A → Fin C) (incoming : A → ℕ)
    (installed : Packing.Directory.RowLocations sent Fin.val recv incoming)
    (tail : 0 < dir.literal/2) (short : dir.description ≤ dir.literal/2)
    {p h dest head : ℕ} (ptr : Fin dir.entries → G)
    (hf : (C+1)+(G₀).words.length+(C+1) ≤ 2^p)
    (hs : (C+1)+(Schema.coords ((G₀).referenceRows ptr).length).length+(C+1) ≤ 2^h)
    (mem : ℕ → ℕ) (slot : Fin dir.entries → ℕ) (fs : Fin dir.entries → List Factor)
    (ext scratch burst : Fin (C+1) → ℕ) (external : Fin (C+1) → List Bool) :
    let places := atRanges (dest := dest) (H := head) G₀ ptr hf hs mem slot fs ext scratch burst external
    BitDelivery (fun j : (c : Fin C) × Fin ((places ⟨min c.val C,Nat.lt_succ_of_le (min_le_right ..)⟩).boxes.filterMap Sum.getRight?).length => j.1)
      (fun _ => dir.description) recv incoming := by
  subst boxes
  intro places
  let entry := original.trans siteID
  let row := originalDelivery S L entry known sh lh priv rep arg x y cells off box
  let realDir := directory S L (originalBoxes entry known) sh lh priv rep arg x y cells off box
  let pos (c : Fin C) : (places ⟨min c.val C,Nat.lt_succ_of_le (min_le_right ..)⟩).boxes =
      realDir.cellBoxes c.castSucc := by
    have idx : (⟨min c.val C,Nat.lt_succ_of_le (min_le_right ..)⟩ : Fin (C+1))=c.castSucc :=
      Fin.ext (min_eq_left c.isLt.le)
    rw [idx]
    rfl
  let castRows (c : Fin C) :=
    finCongr (congrArg (fun l : List (Source.Box (Fin dir.entries)) => (l.filterMap Sum.getRight?).length) (pos c))
  let localIndex := (Equiv.sigmaCongrRight castRows).toEmbedding
  let pp := NativeDemands.privatePair N cell edgeID portID dir original live gap
  let lp := NativeDemands.livePair N cell edgeID portID dir original live gap
  apply dir.privateBitDelivery pp lp _ (localIndex.trans row) Fin.valEmbedding recv incoming installed _ tail short
  intro j
  let i := row (localIndex j)
  have received : cells (entry i) = j.1 :=
    originalDelivery_receiver S L entry known sh lh priv rep arg x y cells off box (localIndex j)
  have actual : cells (entry i)=cell (original i) :=
    TerminalTable.cell_live F N cell siteID edgeID portID state cp physical (original i)
  change (pp i.val).1 = j.1.val
  change (if h : i.val < dir.entries then _ else (0,0)).1 = _
  rw [dite_eq_left i.isLt]
  exact congrArg Fin.val (actual.symm.trans received)

end CellPacketGeometry.History.Native.Terminal

end BorderVNP
end Computability
end OAI
