import OAI.Hierarchy.DescentArchiveCellRead
import OAI.Hierarchy.DescentRoleMountSpan
import OAI.Hierarchy.DescentLowCountBook

namespace OAI
/-! Earlier count and late role writes preserve every original register of the selected archive. -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler DescentDatedAddressBook DescentKernelHistory DescentLocalArchiveOrder
open DescentBundleHistory DescentPrimitivePalette DescentSIMDLookup DescentPackedColony DescentDatedPriorOperand
open DescentOperandStateBanks ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k age grain degree wire hist w : ℕ}
    (ports : DatePorts) (r : Reached W G q ε S k age grain degree wire hist) (B : BitDescription W)
    (number : Local B) (room : RangeRoom ports r B)
variable {p R s Z : ℕ} (shape : WorldShape p R B) (op : RotorSpec)
    (label : NodeOrder.All B→Label G s Z op) (pointer : NodeOrder.All B→ℕ→Pointer)
    (flags : Fin (2^ports.venue.k)→Fin ports.nodes→Fin ports.operandHosts→Fin ports.venue.groups→ℕ)

private theorem read_interval {bits h g lanes : ℕ} {bank:Bank} {low high : ℕ}
    {m out:Memory w} {words : Fin h→Fin g→Cell bits}
    (read : Reads bank words lanes m) (inPage : low≤bank.base ∧ bank.base+h*chunks g lanes≤high)
    (frame : ∀a,low≤a→a<high→ out a=m a) : Reads bank words lanes out:=by
  intro z
  exact (frame (bank.base+(row h g lanes z).val) (inPage.1.trans (Nat.le_add_right ..))
    ((Nat.add_lt_add_left (row h g lanes z).isLt _).trans_le inPage.2)).trans (read z)

private abbrev bankInWindow (low high : ℕ) (bank : Bank) (len : ℕ) : Prop :=
  low≤bank.base ∧ bank.base+len≤high

/-- Low and high writes may be interleaved with the earlier archive. Only its actually
addressed rows need to lie in the protected interval. -/
theorem ArchiveRead.between {low high : ℕ} {m out : Memory w}
    (read : ArchiveRead ports r B number room shape op label pointer flags m)
    (fields : ∀x j (f:Fin 7),bankInWindow low high (previousBank ports.rangeLayout ports.archive.arguments x (DescentOperandStateBanks.page f j)) (ports.operandHosts*chunks ports.venue.groups ports.operandLanes))
    («meta» : ∀x (f:Fin 2),bankInWindow low high (metadataPage ports f x) (ports.operandHosts*chunks ports.venue.groups ports.operandLanes))
    (role : ∀x : Fin (2^ports.venue.k),bankInWindow low high (ports.archive.roles.bank x.val) (ports.operandHosts*chunks ports.venue.groups ports.roleLanes))
    (frame : ∀a,low≤a→a<high→ out a=m a) :
    ArchiveRead ports r B number room shape op label pointer flags out :=by
  rcases read with ⟨headers, spans, flagsRead, arityRead, roleRead⟩
  refine ArchiveRead.mk (ports:=ports) (r:=r) (B:=B) (number:=number) (room:=room)
    (shape:=shape) (op:=op) (label:=label) (pointer:=pointer) (flags:=flags) (m:=out) ?_ ?_ ?_ ?_ ?_
  · intro x j f
    obtain ⟨words,held,ok⟩:=headers x j f
    exact ⟨words,read_interval held (fields x j (f.castLE (by decide))) frame,ok⟩
  · intro x j f
    obtain ⟨words,held,ok⟩:=spans x j f
    exact ⟨words,read_interval held (fields x j (DescentRetainedRangeDigits.page f)) frame,ok⟩
  · exact fun x=>read_interval (flagsRead x) («meta» x 0) frame
  · exact fun x=>read_interval (arityRead x) («meta» x 1) frame
  · exact fun x=>read_interval (roleRead x) (role x) frame

/-- Actual count capture below the reset and the original role ROM above its end. -/
theorem ArchiveRead.after_role_mount {low high roleBase roof : ℕ} {m : Memory w}
    (read : ArchiveRead ports r B number room shape op label pointer flags m)
    (fields : ∀x j (f:Fin 7),bankInWindow low high (previousBank ports.rangeLayout ports.archive.arguments x (DescentOperandStateBanks.page f j)) (ports.operandHosts*chunks ports.venue.groups ports.operandLanes))
    («meta» : ∀x (f:Fin 2),bankInWindow low high (metadataPage ports f x) (ports.operandHosts*chunks ports.venue.groups ports.operandLanes))
    (role : ∀x : Fin (2^ports.venue.k),bankInWindow low high (ports.archive.roles.bank x.val) (ports.operandHosts*chunks ports.venue.groups ports.roleLanes))
    (capture count : ℕ) (source : ℕ→ℕ) (mount : RoleMount w roleBase roof)
    (before : capture+count≤low) (later : high≤roleBase) :
    ArchiveRead ports r B number room shape op label pointer flags
      (mount.phase.image (DescentLowCountBook.output capture source m count)) :=
  ArchiveRead.between ports r B number room shape op label pointer flags read fields «meta» role (fun a ha below=>
    (mount.frame _ a (.inl (below.trans_le later))).trans
      (DescentLowCountBook.frame capture source m count a (.inr (before.trans ha))))

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
