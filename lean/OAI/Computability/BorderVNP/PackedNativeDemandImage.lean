import OAI.Computability.BorderVNP.PackedNativeDemandPacket
import OAI.Computability.BorderVNP.CubeLabelNetworkRun
import OAI.Computability.BorderVNP.PackedRoutingTraffic

/-! # The geometry invocation installs the fixed signed packet's balancing inputs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs.NativeDemands

open Crossing Shortening CellAddresses CellAddressCircuit CellAddressPhysical RoutingISA VPVNP.BurstRAM
open BorderVNP.Cube Cube.Physical Cube.MeanChoice Cube.LabelIndex
open scoped Classical

variable {D s n d k w : ℕ} {P σ : Type} [Fintype P] [Fintype σ] {bits : P → ℕ}

/-- The actual placement and publication leave the chooser reading the
fixed history's exact incoming rows, physical cell numbers and sparse cable IDs. -/
theorem published_placement {W : ℕ} (l : LabelIndex.Layout) (N : Network D P bits)
    (cell : N.Site → Fin l.cells) (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s)
    (edgeID : N.Edge ↪ Fin l.cableCount) (portID : P ↪ Fin n)
    (F : Fields s l.cableCount n l.cells d k w σ) (x : σ → Bool)
    (net : Represents N cell aux siteID edgeID portID F x) (code : ∀ c, (F.cells c).val = c.val)
    (fit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^w)
    (hk : k ≤ w) (wFit : w ≤ W) (cells : 0 < l.cells)
    (dir : Directory.Layout) (old : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
    (width : ∀ p, bits (live p) = dir.block) (bounds : dir.DestinationBounds)
    (head gap : ℕ) (before : ℕ → ℕ) (mid : Memory W) :
    let q := privateLayout head l.cables l.cableCount l.cells dir.entries dir.description gap
    let list := rows N cell edgeID portID dir old live gap
    let recv := receiver N cell edgeID portID dir old live gap bounds
    let mem := readings (Directory.ISA.publish mid head l.deliveries list)
    Image F (siteID ∘ old) (portID ∘ live ∘ finProdFinEquiv.symm) x l.cables before →
    q.Image before dir.entries (readings mid) → q.Fits W before →
    list.length = l.deliveryCount → head+9 < l.cables → head+9 < l.deliveries →
    (l.cables+l.cableCount*3 ≤ l.deliveries ∨ l.deliveries+7*l.deliveryCount ≤ l.cables) →
    (∀ i : Fin list.length, ∀ b ∈ list[i.val].words, b < 2^W) →
    ∃ (ep : Endpoints l mem) (dataOrd : Fin list.length ≃ Fin l.deliveryCount),
      RowPlacement (networkRows N cell recv (fun i => list[i.val].width)) (fromTables l mem ep)
        (Equiv.refl _) ((CableTriples.wireOrd N cell edgeID).sumMap dataOrd.toEmbedding) := by
  intro q list recv mem img run room count first second clear rawFit
  let ptr := bases l.cables l.cableCount l.cells dir.entries
  let published := dir.directory (Directory.ISA.placement (readings mid) ptr.privatePairs)
    (Directory.ISA.placement (readings mid) ptr.livePairs)
  have eq : list = published := rows_eq_native N cell edgeID portID dir old live gap aux siteID F x head l.cables
    before (readings mid) net code fit bounds width img run room
  let wordsFit (rs : List Directory.Row) := ∀ i : Fin rs.length, ∀ b ∈ rs[i.val].words, b < 2^W
  let image (rs : List Directory.Row) := ∃ r : Fin rs.length → Fin l.cells, (∀ i, (r i).val = rs[i.val].cell) ∧
    ∃ (ep : Endpoints l (readings (Directory.ISA.publish mid head l.deliveries rs)))
      (dataOrd : Fin rs.length ≃ Fin l.deliveryCount), RowPlacement (networkRows N cell r (fun i => rs[i.val].width))
        (fromTables l _ ep) (Equiv.refl _) ((CableTriples.wireOrd N cell edgeID).sumMap dataOrd.toEmbedding)
  have result : image published := after_private_placement l N cell aux siteID edgeID portID F x net code fit hk wFit cells
    dir old live width bounds head gap before mid img run room ((congrArg List.length eq).symm.trans count)
    first second clear ((congrArg wordsFit eq).mp rawFit)
  obtain ⟨r,atRow,ep,ord,models⟩ := (congrArg image eq).mpr result
  have same : r = recv := funext fun i => Fin.ext ((atRow i).trans (receiver_val N cell edgeID portID dir old live gap bounds i).symm)
  exact ⟨ep,ord,same ▸ models⟩


section Chooser

open Diagonal Diagonal.CellEntries

variable {ne np r : ℕ} {K Team : Type} [Field K]
    (l : LabelIndex.Layout) (N : Network D P bits) (cell : N.Site → Fin l.cells)
    (edge : N.Edge ↪ Fin l.cableCount) (port : P ↪ Fin np)
    (dir : Directory.Layout) (old : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
    (gap : ℕ) (bounds : dir.DestinationBounds) (cube : FixedCube K) (team : Fin (r+1) ≃ Team)
    {d : ℕ} (hd : 0 < d) {volume : ℝ} {cap : ℕ}
local notation "list" => rows N cell edge port dir old live gap
local notation3 (prettyPrint := false) "widths" => fun i : Fin (list).length => (list)[i.val].width
local notation "recv" => receiver N cell edge port dir old live gap bounds

/-- Any chooser pass on the true published row image writes exactly the label
of the fixed signed packet at each physical cell address. -/
theorem packet_label_stored (budget : PackedLabelBudget N cell recv widths volume cap (d^(cube.pred+1)))
    {before : ℕ → ℕ} (ep : Endpoints l before) {dataOrd : Fin (list).length ≃ Fin l.deliveryCount}
    (placed : RowPlacement (networkRows N cell recv widths) (fromTables l before ep) (Equiv.refl _)
      ((CableTriples.wireOrd N cell edge).sumMap dataOrd.toEmbedding))
    {w : ℕ} (mem : Memory w) (lab : ℕ)
    (written : ∀ c : Fin l.cells, (mem (lab+c.val)).val = (tableCodes l before ep (d^(cube.pred+1)-1) c).val)
    (c : Fin l.cells) :
    memoryLabel mem lab (Equiv.refl _) cube.pred d hd c =
      (packet N cell edge port dir old live gap bounds cube team hd budget).label c := by
  have read := decoded_tableCodes N cell recv widths l before ep (Equiv.refl _) placed cube.pred d hd c
  have code : Fin.ofNat (d^(cube.pred+1)-1+1) (mem (lab+c.val)).val =
      tableCodes l before ep (d^(cube.pred+1)-1) c := by
    apply Fin.ext
    rw [Fin.val_ofNat,written,Nat.mod_eq_of_lt (Fin.isLt _)]
  change decodeProduct cube.pred d hd _ = meanPackedLabel N cell recv widths (List.finRange l.cells) cube.pred d hd c
  rw [show Fin.ofNat (d^(cube.pred+1)-1+1) (mem (lab+((Equiv.refl (Fin l.cells)) c).val)).val =
    tableCodes l before ep (d^(cube.pred+1)-1) c from code]
  simpa using read

end Chooser
end Packing.RoutingOutputs.NativeDemands

end BorderVNP
end Computability
end OAI
