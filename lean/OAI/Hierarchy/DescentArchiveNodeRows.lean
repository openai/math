import OAI.Hierarchy.DescentArchiveRegisterFlag

namespace OAI
/-! # The two reached node fields at their dated register -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentRetainedRangeDigits
open DescentDatedAddressBook DescentPackedColony DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM
open scoped Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i grain degree wire hist w p R : ℕ}
    (r : Reached W G q ε S k i grain degree wire hist) (B : BitDescription W)
    (number : Local B) (shape : WorldShape p R B)
def NodeRows (ports : DatePorts) (room : RangeRoom ports r B) (m : Memory w) : Prop :=
  (∀x,Reads (metadataPage ports 0 x) (fun h g=>encode ports.operandBits ports.nodes
    (fun j=>(RegisterTimeline.archiveFlag r B number ports room x j h g:Cell ports.operandBits))) ports.operandLanes m) ∧
  ∀x,Reads (metadataPage ports 1 x) (fun h g=>encode ports.operandBits ports.nodes
    (fun j=>((slotAt ports r B number room x j h g).elim 0
      (fun y=>(occurrences (shape.sites y.1) y.2).length):Cell ports.operandBits))) ports.operandLanes m

theorem ArchiveRead.nodeRows {ports : DatePorts} {room : RangeRoom ports r B} {m : Memory w}
    {s Z : ℕ} {op : RotorSpec} {label : NodeOrder.All B → DescentPrimitivePalette.Label G s Z op}
    {pointer : NodeOrder.All B → ℕ → DescentOperandStateBanks.Pointer}
    (stored : ports.ArchiveRead r B number room shape op label pointer
      (RegisterTimeline.archiveFlag r B number ports room) m) :
    NodeRows r B number shape ports room m :=
  ⟨stored.nodeFlags,stored.arity⟩

theorem node_rows_at_cursor {p₀ p₁ : DatePorts} {m₀ m₁ : Memory w} (ports : p₁=p₀) (memory : m₁=m₀)
    (where₀ : RangeRoom p₀ r B) (where₁ : RangeRoom p₁ r B) (rows : NodeRows r B number shape p₀ where₀ m₀) :
    NodeRows r B number shape p₁ where₁ m₁ :=by
  subst p₁
  subst m₁
  exact rows

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
