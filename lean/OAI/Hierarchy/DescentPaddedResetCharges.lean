import OAI.Hierarchy.DescentRegisteredResetCharges
import OAI.Hierarchy.DescentResetHostPadPrice

namespace OAI
/-! The complete registered reset includes the physical padding of the previous
date's metadata, argument and role archives before entering the fourteen stages. -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentCompiler DescentPacking.PackedMatch.Local.Stage
open DescentStaticWordColumn Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree h : ℕ)
    (ordinary : ℕ→Dated.Ordinary) (op : RotorSpec) (s Z : ℕ) (prev : DatePorts) (floor w : ℕ)
local notation "post" => prev.afterPad k floor
local notation "start" => prev.priorStart k floor
local notation "nextM" => NativePitch.incoming S k tail p f h ordinary (age+1)
local notation "outer" => scheduledAtPorts G S board k tail age p f g drift degree h ordinary op s Z prev floor
local notation "padded" => priorArchivePhase G S board k tail age p f g drift degree h ordinary op s Z prev floor w
variable (capacity : prev.venue.cap = ((capCalendar G.b S.rounds g S.height).take age).prod*256)
    (space : ScheduledCodeRoom G S board k tail age p f g drift degree h ordinary op s Z
      prev.operandLanes prev.roleLanes prev.venue prev.io (prev.priorStart k floor) w
      (prev.afterPad k floor).archive)

def archiveCharge :=((padded).ticks+7*names (padded).program)*w

theorem reset_padded_charge (old : 0 < prev.venue.lanes) (roles : 0 < prev.roleLanes) (next : 0 < nextM)
    (roof : (outer).fullEnd < 2^w) :
    (resetDate G S board k tail age p f g drift degree h ordinary op s Z prev floor w capacity space).tariff ≤
      archiveCharge G S board k tail age p f g drift degree h ordinary op s Z prev floor w+
      (resetCharges G S board k tail age p f g drift degree h ordinary op s Z post start w space).total :=by
  rw [show (resetDate G S board k tail age p f g drift degree h ordinary op s Z prev floor w capacity space).tariff = _ from
    scheduled_padded_price G S board k tail age p f g drift degree h ordinary op s Z prev floor w capacity space]
  exact Nat.add_le_add_left (reset_charge_at G S board k tail age p f g drift degree h ordinary op s Z
    post start w capacity space old roles next roof) _

/-- The actual outer opcode uses one high-word allowance after summing its own
fifteen cost components, each of which can choose a distinct fixed rate. -/
theorem reset_date_invoice (old : 0 < prev.venue.lanes) (roles : 0 < prev.roleLanes) (next : 0 < nextM)
    (roof : (outer).fullEnd < 2^w) (J saving : ℕ) (leads rates shares : Fin 15 → ℕ)
    (bought : ∀j : Fin 15,
      ((resetCharges G S board k tail age p f g drift degree h ordinary op s Z post start w space).paddedAmount
        (archiveCharge G S board k tail age p f g drift degree h ordinary op s Z prev floor w)) j ≤
        S.hostSize age*h*(leads j*TerminalScale.scale J (rates j))+
        S.hostSize age*(S.groupCount age*S.radix)*(leads j*TerminalScale.scale J (rates j))+
        shares j*(S.initialSites/(2^J)^(saving+1)))
    (shared : (∑j,shares j) ≤ 2^J) :
    (resetDate G S board k tail age p f g drift degree h ordinary op s Z prev floor w capacity space).tariff ≤
      S.hostSize age*h*((∑j,leads j)*TerminalScale.scale J (∑j,rates j))+
      S.hostSize age*(S.groupCount age*S.radix)*((∑j,leads j)*TerminalScale.scale J (∑j,rates j))+
      S.initialSites/(2^J)^saving :=by
  have actual:=reset_padded_charge G S board k tail age p f g drift degree h ordinary op s Z prev floor w
    capacity space old roles next roof
  rw [←EnteredCharges.sum_padded] at actual
  exact actual.trans (EnteredCharges.finite_paid _ J _ _ _ saving leads rates shares bought shared)

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
