import OAI.Hierarchy.DescentScheduledResetChart
import OAI.Hierarchy.DescentIncomingCalendarFactors

namespace OAI
/-! # The last physical normalized venue has the full final cap calendar and the frozen group count -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentCompiler DescentSixParty DescentPacking.PackedMatch.Local.Stage ProtocolRAM
noncomputable section
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f gain drift degree h : ℕ)
    (ordinary : ℕ→Dated.Ordinary) (op : RotorSpec)
    (s Z operandLanes primitiveLanes : ℕ) (old : StageVenueTail.Date)
    (addr : ℕ→ℕ→Bank) (roster : Bank)

local notation "a" => scheduled G S board k tail age p f gain drift degree h ordinary op s Z operandLanes primitiveLanes old addr roster

theorem scheduled_venue_shape (floor:ℕ):
    let v:=(a floor).successor.venue.next
    v.k=old.k ∧ v.hosts=S.hostSize (age+1) ∧ v.groups=S.groupCount (age+1) ∧
      v.cap=2^gain*((capCalendar G.b S.rounds gain S.height).take age).prod*256 ∧
      v.lanes=NativePitch.incoming S k tail p f h ordinary (age+1):=by
  exact ⟨rfl,rfl,rfl,by change 2^gain*(_*256)=2^gain*_*256;rw [Nat.mul_assoc],rfl⟩

theorem last_capacity (last:age+1=S.length):
    2^gain*((capCalendar G.b S.rounds gain S.height).take age).prod=(capCalendar G.b S.rounds gain S.height).prod:=
  NativePitch.terminal_factor G.b S.rounds gain S.height age last

theorem scheduled_terminal_shape (floor:ℕ)(last:age+1=S.length)(blocks:old.k=k):
    let v:=(a floor).successor.venue.next
    v.k=k ∧ v.hosts=S.hostSize S.length ∧ v.groups=S.groupCount S.length ∧
      v.cap=(capCalendar G.b S.rounds gain S.height).prod*256 ∧ v.lanes=S.groupCount S.length:=by
  obtain ⟨radix,hosts,groups,cap,pitch⟩:=scheduled_venue_shape G S board k tail age p f gain drift degree h ordinary op
    s Z operandLanes primitiveLanes old addr roster floor
  exact ⟨radix.trans blocks,hosts.trans (congrArg S.hostSize last),groups.trans (congrArg S.groupCount last),
    cap.trans (congrArg (·*256) (last_capacity G S age gain last)),by rw [pitch,last,NativePitch.terminal]⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
