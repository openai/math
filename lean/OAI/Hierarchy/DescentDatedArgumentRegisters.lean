import OAI.Hierarchy.DescentOrdinaryDatedEntry
import OAI.Hierarchy.DescentPreviousOperandLimit
import OAI.Hierarchy.DescentPriorArchiveLimits
import OAI.Hierarchy.DescentResetTerminalRegisterLayout

namespace OAI
/-! The end of the actual seven-field rectangle carried by each predecessor date. -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentOrdinaryFinal DescentInitialHost DescentDatedSeedStartup
open DescentDatedPriorOperand DescentOperandStateBanks DescentSIMDLookup ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section

def argumentLimit (p : DatePorts) (blocks : ℕ) :=
  (p.argumentLayout blocks).previousLimit p.archive.arguments

theorem prior_fits (prior : DatePorts) (blocks cut w : ℕ) (done : prior.argumentLimit blocks≤cut)
    (room : cut<2^w) (x : Fin blocks) (p : Pages prior.argumentsPerNode) :
    (previousBank (prior.argumentLayout blocks) prior.archive.arguments x p).Fits w cut :=
  (prior.argumentLayout blocks).previous_fit _ _ _ done room x p

theorem seed_argument_limit {F : Type} [Field F] {c p : ℕ} (G : PoweredGadget F) (op : RotorSpec)
    (X : Catalyst.Approximation F c p) (copies : ℕ) (l : DescentDatedSeedStartup.Layout) (k H groups h Z : ℕ) :
    (initial G op X copies l k H groups h Z).argumentLimit (2^k)=
      DescentDatedSeedStartup.directoryBase X l H groups k :=rfl

theorem ordinary_argument_limit {F P : Type} [Field F] (v : PhysicalOrdinary F P) (base : ℕ)
    (groups : v.venue.groups=v.resolver.groups) (chart : v.operandBook=v.finalChart) :
    (ordinary v base).argumentLimit v.resolver.blocks=v.operandEnd base :=by
  change v.finalChart.out (v.metaEnd base)+(7*v.resolver.operands)*
    (v.resolver.blocks*(v.resolver.hosts*chunks v.venue.groups v.resolver.lanes))+
      2^Nat.clog 2 (v.resolver.hosts*chunks v.venue.groups v.resolver.lanes+1)=
    v.operandBook.endAddress (v.metaEnd base)
  rw [groups,chart]
  simp only [DescentOrdinaryFinal.Chart.endAddress,DescentOrdinaryFinal.Chart.passes,
    DescentOrdinaryFinal.Chart.outputs,DescentOrdinaryFinal.Chart.rows,PhysicalOrdinary.finalChart,
    DescentDatedPriorOperand.Layout.rows,Nat.mul_assoc]

theorem reset_argument_limit {w} (a : PhysicalReset) (base : ℕ) (u : a.DateInputs base w)
    (hosts : a.successor.sheets.hosts=a.successor.receiver.hosts)
    (groups : a.successor.venue.next.groups=a.successor.receiver.groups) :
    (reset a base u).argumentLimit a.successor.receiver.blocks=a.successor.finalEnd (a.rebased base) :=by
  let v := a.successor
  change v.sheets.hosts=v.receiver.hosts at hosts
  change v.venue.next.groups=v.receiver.groups at groups
  have layout : (reset a base u).argumentLayout v.receiver.blocks = v.rangeLayout := by
    change (⟨v.receiver.blocks,v.nodes,v.argumentSlots,v.sheets.hosts,v.venue.next.groups,
      v.receiver.lanes,v.nodeBits-2⟩ : DescentDatedPriorOperand.Layout) = v.rangeLayout
    rw [hosts, groups]
    rfl
  change ((reset a base u).argumentLayout v.receiver.blocks).previousLimit
    (PriorResetArchive.reset v (a.rebased base)).arguments = v.finalEnd (a.rebased base)
  rw [layout]
  exact v.terminal_previous_limit (a.rebased base)

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
