import OAI.Hierarchy.DescentTerminalSliceDated
import OAI.Hierarchy.DescentTerminalEmittedArity

namespace OAI
/-! # Reached per-node readback of the five retained span and metadata observables -/
namespace Hierarchy.DescentTerminalSliceRuns
open DescentTerminalSliceShelf DescentTerminalPointerDigits DescentSIMDLookup DescentPackedColony
open DescentCompiler DescentSixParty DescentDatedAddressBook ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentBundleHistory DescentKernelHistory
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable (v:ResetOutput) (base:ℕ)
local notation "A" => v.argumentSlots
local notation "B" => v.receiver.blocks
local notation "H" => v.receiver.hosts
local notation "N" => v.nodes
local notation "G" => v.receiver.groups
local notation "tokenBits" => v.primitive.chart.bits
local notation "bits" => v.nodeBits
variable (tok:v.receiver.blocks=v.primitive.chart.blocks) (argc:v.receiver.blocks=v.metadata.chart.blocks)
local notation "chart" => datedChart v base tok argc
local notation "field_" f:arg j:arg b:arg => v.terminalField base (⟨4+(f:Fin 3).val,by omega⟩:Fin 7) j b

variable {w d:ℕ} (m:Memory w) (b:Fin v.receiver.blocks) (h:Fin v.receiver.hosts) (g:Fin v.receiver.groups) (u:Fin v.nodes)
local notation "raw" => extract (datedWidths v) (seen (d:=d) chart m b h) g u
variable (T:Fin v.receiver.hosts→Fin v.receiver.groups→Cell (v.primitive.chart.bits*v.nodes))
    (Q:Fin v.receiver.hosts→Fin v.receiver.groups→Cell (v.nodeBits*v.nodes))
    (S:Fin 3→Fin v.argumentSlots→Fin v.receiver.hosts→Fin v.receiver.groups→Cell (v.nodeBits*v.nodes))
    (role:Reads (v.terminalRole base (b.cast tok)) T v.receiver.groups m)
    (flatArity:Reads (v.terminalArity base (b.cast argc)) Q v.receiver.groups m)
    (ranges:∀(f:Fin 3) j,Reads (v.terminalField base (⟨4+f.val, by omega⟩:Fin 7) j b) (S f j) v.receiver.groups m)
    (wide:physicalWidth v.receiver.groups v.nodes v.primitive.chart.bits v.nodeBits≤w)
    (cover:physicalWidth v.receiver.groups v.nodes v.primitive.chart.bits v.nodeBits≤d)
local notation "val_" a:arg x:arg => ((encode a N).symm (x h g) u).val

private theorem field_le (k:ℕ) (eq_:k≤ max tokenBits bits) :
    (k*N)*G≤physicalWidth G N tokenBits bits:=by
  have le_:=Nat.mul_le_mul_right (N*G) eq_
  simpa only [physicalWidth,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using le_

structure Decoded (r:Raw A) : Prop where
  token : r.token=val_ tokenBits T
  count : r.live=val_ bits Q
  start : ∀j,(r.header j).start=val_ bits (S 0 j)
  stride : ∀j,(r.header j).stride=val_ bits (S 1 j)
  words : ∀j,(r.header j).count=val_ bits (S 2 j)

include role flatArity ranges wide cover in
theorem extract_source : Decoded v h g u T Q S raw := by
  have lo:=field_le v tokenBits (Nat.le_max_left ..)
  have hi:=field_le v bits (Nat.le_max_right ..)
  refine ⟨?_,?_,?_,?_,?_⟩
  · change laneField tokenBits g u (seen (d:=d) chart m b h (leading 0))=_
    simp only [seen,token_bank,Gather.Address.atHost]
    exact stored_lane _ _ m role (lo.trans wide) (lo.trans cover) h g u
  · change laneField bits g u (seen (d:=d) chart m b h (leading 1))=_
    simp only [seen,count_bank,Gather.Address.atHost]
    exact stored_lane _ _ m flatArity (hi.trans wide) (hi.trans cover) h g u
  all_goals
    intro j
    change laneField bits g u (seen (d:=d) chart m b h (triple _ j))=_
    simp only [seen,span_bank,Gather.Address.atHost]
    exact stored_lane _ _ m (ranges _ j) (hi.trans wide) (hi.trans cover) h g u

end
end Hierarchy.DescentTerminalSliceRuns

end OAI
