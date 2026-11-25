import OAI.Hierarchy.TaggedWireStripDebitWire
import OAI.Hierarchy.ProbeFixedStripQuotes
import OAI.Hierarchy.TaggedWireStripTender

namespace OAI
/-! # One selected strip consumes precisely its own original padded debit words -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard Strip WireTelescope CatalystArchive StockCommit RepairHistogram
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor Probe ChosenPackets RowRouting
open ThreeFlat.Diagonal.MotifOuterTerms
open scoped BigOperators Classical Fin.CommRing

variable {k n K w : ℕ} {A B Ball F : Type}
  [Field F] [Fintype A] [Fintype B] [Fintype Ball]
local notation "C" => TreeColumn n
local notation "R" => ColumnWires.Role C (Fin n) (A⊕B) k
variable {extra : A⊕B→DistinctPair (TreeSite n k)} {place : Ball×TreeSite n k↪Fin K} {u : Ball}
local notation "roles" => ColumnWires.ends (horizontal n) extra
variable (labels : TreeSite n k≃Fin (Fintype.card (TreeSite n k))) (rt : Fin (Fintype.card (TreeSite n k)))
  {N z rawD D : ℕ} [Nonempty (Fin (Fintype.card (TreeSite n k)))] [Nonempty (Fin k)]
  [Nonempty (ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k)]
  {M ε tree : ℝ} {len : Fin n→ℝ} {cap : A→ℝ}
local notation "req" => ColumnWires.demand (I:=C) (H:=Fin n) (k:=k) (Sum.inl (α:=A) (β:=B))
variable {menu : Probe.FixedMenu F
    (fun e : ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k =>
      @DistinctPair.chord _ _ ⟨labels⟩ (ColumnWires.ends (horizontal n) extra e))
    (ColumnWires.demand (I:=TreeColumn n) (H:=Fin n) (k:=k) (Sum.inl (α:=A) (β:=B)))
    ((fun y:A→ℝ => ColumnWires.quote (I:=TreeColumn n) (k:=k) M len (LocalCommodity.extraPrice (B:=B) y)) ''
      Set.Icc 0 cap) ε tree N}
  (i : menu.index) {q : ℕ} (x : StripInput menu w z rawD q D)
  (j : Fin x.raw.market.rows) (live : j∈liveRows x.ballot x.mem x.raw.market.rows)
  (arity : (x.ballot.termCount.read x.mem (x.ballot.packet.eval x.mem (j.val:Word w))).val=(menu.packet i).terms)
  (selected : (x.ballot.packet.eval x.mem (j.val:Word w)).val=(Fintype.equivFin menu.index i).val+1)
    (pad : Chord K) (bound : (menu.packet i).terms≤q)

local notation "needs" => (fun z : PositiveDemand req i.val.val=>req z.val)
local notation "Q" => stripPacket labels roles needs place u rt (menu.packet i)
local notation "wire" => stripDebitWire (D:=D) pad (reportedRole place roles u)

include live arity selected bound in
omit [Fintype Ball] [Nonempty (Fin k)] in
theorem chosen_strip_source : (Q).wants x.ballot.copies=
    optionWidths wire (fun v=>consumedBits (fresh x.form.pricedArea x.form.stockSource).columns x.mem (x.plan.enum ⟨j,v⟩)) := by
  obtain ⟨spare,eq⟩:=Nat.exists_eq_add_of_le bound
  subst q
  let row:=StripInput.packetAt i spare x j live arity selected
  let embedding:=labels.symm.toEmbedding.trans (ballEmbedding place u)
  apply row.padded_source embedding rt (treeGraph labels) (tree_connected labels) wire
  intro e
  change PortPadding.extend _ pad (PortPadding.inject x.ports (Fintype.equivFin R e))=_
  rw [PortPadding.extend_real,Equiv.symm_apply_apply]
  exact (physicalChord_role labels (ballEmbedding place u) (roles e)).symm

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
