import OAI.Hierarchy.DescentEncodedBookTags
import OAI.Hierarchy.DescentPackedReadUnique
import OAI.Hierarchy.DescentArchiveCellRead

namespace OAI
/-! # The dated kind and the live pointer on the same physical archive -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentRetainedRangeDigits
open DescentDatedAddressBook DescentDatedPriorOperand DescentOperandStateBanks DescentPackedColony
open DescentPrimitivePalette DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM
open scoped Classical Fin.CommRing
noncomputable section

open DescentOrdinaryAtomFieldRAM DescentPriorOperandColumns

def ArchiveTags (ports : DatePorts) {w : ℕ} (m : Memory w) : Prop :=
  ∃bks : Books ports.rangeLayout, BookTags bks ∧ ∀x pg,
    Reads (previousBank ports.rangeLayout ports.archive.arguments x pg)
      (bks x pg) ports.rangeLayout.lanes m

/-- The physical tag pages determine the kind for any family measuring them. -/
theorem ArchiveTags.at_read {ports : DatePorts} {w : ℕ} {m : Memory w} (held : ArchiveTags ports m)
    (bks : Books ports.rangeLayout) (live : 0<ports.rangeLayout.lanes)
    (room : ((ports.rangeLayout.size+2)*ports.rangeLayout.nodes)*ports.rangeLayout.lanes ≤ w)
    (same : ∀x j,Reads (previousBank ports.rangeLayout ports.archive.arguments x (pageOf j 0))
      (bks x (pageOf j 0)) ports.rangeLayout.lanes m) : BookTags bks :=by
  obtain ⟨original,valid,stored⟩:=held
  exact BookTags.of_same_register valid live room (fun x j=>stored x (pageOf j 0)) same

private theorem same_read_digit {w H G M K a b : ℕ} (bits : a=b) (bank : Bank) (m : Memory w)
    {t : Fin H→Fin G→Cell (a*K)} {s : Fin H→Fin G→Cell (b*K)}
    (lt : Reads bank t M m) (rt : Reads bank s M m) (positive : 0 < M) (space : (a*K)*M ≤ w)
    (h : Fin H) (g : Fin G) (n : Fin K) :
    (ScalarOperand.take n (t h g)).val=(ScalarOperand.take n (s h g)).val := by
  subst b
  rw [Reads.determined lt rt positive space]

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k age grain degree wire hist w : ℕ}
    (ports : DatePorts) (r : Reached W G q ε S k age grain degree wire hist) (B : BitDescription W)
    (number : Local B) (room : RangeRoom ports r B)

variable {p R s Z : ℕ} (shape : WorldShape p R B) (op : RotorSpec)
    (label : NodeOrder.All B→Label G s Z op) (pointer : NodeOrder.All B→ℕ→Pointer)
    (flags : Fin (2^ports.venue.k)→Fin ports.nodes→Fin ports.operandHosts→Fin ports.venue.groups→ℕ)

/-- The registered scalar decoder returns the earlier semantic pointer for every
admitted argument, using four projections at the very same measured location. -/
theorem ArchiveRead.decoded_at {m : Memory w}
    (held : ArchiveRead ports r B number room shape op label pointer flags m)
    (bks : Books ports.rangeLayout) (bits : 2 ≤ ports.operandBits) (positive : 0 < ports.operandLanes)
    (space : ((ports.rangeLayout.size+2)*ports.nodes)*ports.operandLanes ≤ w)
    (reads : ∀x pg,Reads (previousBank ports.rangeLayout ports.archive.arguments x pg) (bks x pg) ports.operandLanes m)
    (x : Fin (2^ports.venue.k)) (n : Fin ports.nodes) (j : Fin ports.argumentsPerNode)
    (h : Fin ports.operandHosts) (g : Fin ports.venue.groups) (y : NodeOrder.All B)
    (location : slotAt ports r B number room x n h g=some y)
    (active : j.val<(occurrences (shape.sites y.1) y.2).length) :
    decodeHeader (booksHeader bks (ports.rangeLayout.index (x,n,j)) h g)=pointer y j.val :=by
  apply decode_of_pointer
  intro f
  obtain ⟨cells,readAt,semantic⟩:=held.headers x j f
  have width : ports.rangeLayout.size+2=ports.operandBits := Nat.sub_add_cancel bits
  have digit:=same_read_digit width _ m (reads x (pageOf j f)) readAt positive space h g n
  simpa only [booksHeader,Equiv.symm_apply_apply,ScalarOperand.take] using
    digit.trans (semantic h g n y location active)

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
