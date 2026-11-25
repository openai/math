import OAI.Hierarchy.DescentTerminalArchivedChartRead
import OAI.Hierarchy.DescentTerminalSliceDated
import OAI.Hierarchy.DescentResetRegisteredOperandRows
import OAI.Hierarchy.DescentResetArchiveMetadata

namespace OAI
/-! Identification of the original registered slice chart with the scheduled reset's actual banks. -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentCompiler DescentDatedPriorOperand DescentOperandStateBanks
open DescentSIMDLookup DescentTerminalSliceRuns DescentTerminalSliceShelf DescentTerminalPointerDigits
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

private theorem node_bank_cast {s t : DescentDatedNodeMetadata.Chart} (eqn : s=t) (base : ℕ)
    (f : Fin 2) (x : Fin s.blocks) :
    s.bank base f x=t.bank base f (x.cast (congrArg DescentDatedNodeMetadata.Chart.blocks eqn)):=by
  cases eqn
  rfl

private theorem argument_bank_cast {s t : DescentDatedPriorOperand.Layout} (eqn : s=t) (base : ℕ) (f : Fin 7)
    (j : Fin s.operands) (x : Fin s.blocks) :
    previousBank s base x (DescentOperandStateBanks.page f j)=
      previousBank t base (x.cast (congrArg DescentDatedPriorOperand.Layout.blocks eqn))
        (DescentOperandStateBanks.page f (j.cast (congrArg DescentDatedPriorOperand.Layout.operands eqn))) :=by
  cases eqn
  rfl

variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "ports" => reset a floor u
local notation "v" => a.successor
local notation "at_" => a.rebased floor
variable (layout : (reset a floor u).rangeLayout=a.successor.rangeLayout) (nodes : (reset a floor u).metadataChart=a.successor.metadata.chart)
  (tok : a.successor.receiver.blocks=a.successor.primitive.chart.blocks) (argc : a.successor.receiver.blocks=a.successor.metadata.chart.blocks)
local notation "b_" x:arg => (x).cast (congrArg DescentDatedPriorOperand.Layout.blocks layout)

include nodes in
/-- Every leading or affine source address is the one from the issued last reset. -/
theorem reset_slice_chart (c : Fin (Columns (v).argumentSlots)) (x : Fin (2^(ports).venue.k)) :
    archiveSliceChart ports c x=datedChart v at_ tok argc c (b_ x) :=by
  obtain ⟨z,rfl⟩:=finSumFinEquiv.surjective c
  cases z with
  | inl t =>
    fin_cases t
    · exact (archive_leading_token ports x).trans (token_bank v at_ tok argc (b_ x)).symm
    · refine (archive_leading_count ports x).trans (Eq.trans ?_ (count_bank v at_ tok argc (b_ x)).symm)
      exact congrArg Gather.Address.hosts (node_bank_cast nodes _ 1 x)
  | inr t =>
    obtain ⟨⟨f,j⟩,rfl⟩:=finProdFinEquiv.surjective t
    refine (archive_triple ports f j x).trans (Eq.trans ?_ (span_bank v at_ tok argc f j (b_ x)).symm)
    exact congrArg Gather.Address.hosts ((argument_bank_cast layout _ _ j x).trans
      ((v).operand_bank at_ (b_ x) j (DescentRetainedRangeDigits.page f)))

open DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentRetainedRangeDigits
open DescentPrimitivePalette DescentPackedColony
variable {F P : Type} [Field F] {D : ℕ} {size : P→ℕ} {W : MarkedWorld F D P size}
    {G : PoweredGadget F} {q ε : ℝ} {sched : AtomSchedule} {k age z degree wire hist d limit : ℕ}
    (r : Reached W G q ε sched k age z degree wire hist) (B : BitDescription W)
    (order : Local B) (places : RangeRoom (reset a floor u) r B) {p R s Z : ℕ} (shape : WorldShape p R B) (op : RotorSpec)
    (label : NodeOrder.All B→Label G s Z op) (ptr : NodeOrder.All B→ℕ→Pointer)
    (flags : Fin (2^(reset a floor u).venue.k)→Fin (reset a floor u).nodes→Fin (reset a floor u).operandHosts→Fin (reset a floor u).venue.groups→ℕ)
    (before after : Memory w) (stored : ArchiveRead (reset a floor u) r B order places shape op label ptr flags before)
local notation "chart" => datedChart v at_ tok argc
local notation "bitsT" => printedBits G s Z op
local notation "rect" => physicalWidth (ports).venue.groups (v).nodes bitsT (v).nodeBits
variable (roleWidth : (printedBits G s Z op)=a.successor.primitive.chart.bits)
    (pitch : (reset a floor u).operandLanes=(reset a floor u).venue.groups) (roles : (reset a floor u).roleLanes=(reset a floor u).venue.groups)
    (wide : physicalWidth (reset a floor u).venue.groups a.successor.nodes (printedBits G s Z op) a.successor.nodeBits≤w) (cover : physicalWidth (reset a floor u).venue.groups a.successor.nodes (printedBits G s Z op) a.successor.nodeBits≤d) (x : Fin (2^(reset a floor u).venue.k)) (h : Fin (reset a floor u).operandHosts)
    (g : Fin (reset a floor u).venue.groups) (n : Fin a.successor.nodes) (y : NodeOrder.All B)
    (hit : slotAt (reset a floor u) r B order places x n h g=some y)
local notation "raw" => extract (datedWidths v) (seen (d:=d) chart after (b_ x) h) g n
local notation "args" => occurrences (shape.sites y.1) y.2

include layout nodes tok argc stored roleWidth pitch roles wide cover hit in
/-- At the first slice pass, the visible operands at this resident come from the earlier
registered reset. The intervening reel can write its own area above all these pages. -/
theorem ArchiveRead.reset_slice_at
    (earlier : ∀c,(chart c (b_ x)).Fits limit (ports).operandHosts w)
    (frame : ∀a<limit,after a=before a) :
    (raw).token=(token G s Z op (label y)).val ∧ (raw).live=((args).length : Cell (v).nodeBits).val ∧
    ∀(j : Fin (v).argumentSlots) (f : Fin 3),j.val<(args).length ∨ f=2 →
      value ((raw).header j) f=atSlot (shape.sites y.1) y.2 j.val f :=by
  exact ArchiveRead.slice_at_chart (d:=d) ports r B order places shape op label ptr flags before after
    stored pitch roles wide cover chart (datedWidths v) rfl rfl rfl
    (by simp only [datedWidths, ←roleWidth]; rfl) x (b_ x) h g n y hit
    (fun c => reset_slice_chart u layout nodes tok argc c x) earlier frame

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
