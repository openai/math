import OAI.Hierarchy.DescentRegisteredResetBounds
import OAI.Hierarchy.DescentScheduledResetAtPorts
import OAI.Hierarchy.DescentDateArgumentSlots
import OAI.Hierarchy.DescentResetHostPadPrice
import OAI.Hierarchy.DescentPriorNodePresenceRate

namespace OAI
/-! # Complete reset address bounds from the physical endpoint of its preceding date -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty DescentPackedWalsh
open DescentPacking.PackedMatch.Local.Stage ProtocolRAM Filter
noncomputable section
set_option quotPrecheck false

variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
  (op : RotorSpec) (t f g reset τ maximum drift B : ℕ) {ι : ℕ→Type*}
  (sites age p degree floor : ∀h,ι h→ℕ)
  (ordinary : ∀h,ι h→ℕ→Dated.Ordinary) (ports : ∀h,ι h→Chronology.DatePorts)
local notation "J_" h:arg => Nat.log 2 h/(2*B)
local notation "tb_" h:arg => tail τ (J_ h)
local notation "S_" h:arg i:arg =>stageNumbers G t (J_ h) f g reset (sites h i) (tb_ h)
local notation "k_" h:arg =>groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "cap_" h:arg i:arg => ((capCalendar G.b t g (J_ h)).take (age h i)).prod*256
local notation "seed_" h:arg i:arg =>(S_ h i).firstWidth G.b (p h i)
local notation "grain_" h:arg i:arg =>(S_ h i).grainAt G.b (p h i) 0
local notation "token_" h:arg i:arg =>DescentPrimitivePalette.printedBits G (seed_ h i) (grain_ h i) op
local notation "oldCut_" h:arg i:arg => NativePitch.resetCut (S_ h i) (k_ h) (tb_ h) (p h i) f h (age h i)
local notation "nextM_" h:arg i:arg => NativePitch.incoming (S_ h i) (k_ h) (tb_ h) (p h i) f h (ordinary h i) (age h i+1)
local notation "pad_" h:arg i:arg =>(ports h i).resetPad (k_ h)
local notation "presence_" h:arg i:arg =>(ports h i).presence (k_ h)
local notation "inside_" h:arg i:arg =>(ports h i).priorStart (k_ h) (floor h i)
local notation "a_" h:arg i:arg =>scheduledAtPorts G (S_ h i) board (k_ h) (tb_ h) (age h i) (p h i) f g drift (degree h i) h
  (ordinary h i) op (seed_ h i) (grain_ h i) (ports h i) (floor h i)

theorem registered_pad (seed : Bounded sites) (before : ∀h i,age h i<(S_ h i).length)
    (oldHost : ∀h i,((ports h i).venue).hosts=(S_ h i).hostSize (age h i))
    (oldGroup : ∀h i,((ports h i).venue).groups=(S_ h i).groupCount (age h i))
    («arguments» : ∀ᶠ h:ℕ in atTop,∀i,Chronology.DatePorts.ArgumentSlots G (S_ h i) (ports h i) drift)
    (archives : ∀ᶠ h:ℕ in atTop,∀i,Chronology.DatePorts.ArchiveWidths G (S_ h i) op (ports h i)
      (k_ h) (tb_ h) (p h i) drift (degree h i) h (age h i)) :
    DescentResetPriorHostPad.Shape.ScalarRoom (fun h i=>pad_ h i) :=by
  let e:=operandExponent G (stageNumbers G t 0 f g reset 0 0)
  let κ:=1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
  have axes:=schedule_space G t f g reset τ B sites age seed (fun h i=>(before h i).le)
  have level : ∀ᶠ h:ℕ in atTop,J_ h≤h:=Eventually.of_forall fun h=>(Nat.div_le_self ..).trans (Nat.log_le_self 2 h)
  have args : SmallAt (fun h=>J_ h) (fun h (_:ι h)=>(2^(J_ h))^e) :=by
    refine ⟨e,Eventually.of_forall fun h i=>?_⟩
    change (2 ^ (J_ h)) ^ e ≤ 2 ^ (e * ((J_ h) + 1))
    rw [← Nat.pow_mul,Nat.mul_comm (J_ h) e]
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left e (Nat.le_succ _))
  have blocks : SmallAt (fun h=>J_ h) (fun h (_:ι h)=>2^(k_ h)) :=
    ⟨κ,Eventually.of_forall fun h i=>Nat.pow_le_pow_right (by decide) (groupBits_linear ..)⟩
  have previous : Bounded (fun h i=>(ports h i).argumentsPerNode) :=
    ((Bounded.const (drift+1)).mul (args.bounded level)).of_eventually_le «arguments»
  have heightRoom : Bounded (fun h (_:ι h)=>h) :=
    ⟨1,Eventually.of_forall fun h i=>by simpa only [one_mul] using (Nat.lt_two_pow_self (n:=h)).le⟩
  have pitches : ∀ᶠ h:ℕ in atTop,∀i,(ports h i).operandLanes≤h ∧ (ports h i).roleLanes≤h:=by
    filter_upwards [archives] with h prev
    intro i
    have saved:=prev i
    have positiveNodes : 0<(ports h i).nodes:=by
      rw [saved.nodes]
      split
      · decide
      · exact pow_pos (Nat.two_pow_pos _) _
    have bits : 0<(ports h i).operandBits:=by
      rw [saved.digits]
      exact (Nat.succ_pos _).trans_le (Nat.le_max_right ..)
    have printed : 0<token_ h i:=by
      apply Nat.clog_pos (by decide : 1<2)
      unfold DescentPrimitivePalette.colors
      omega
    exact ⟨(Nat.le_mul_of_pos_left _ (Nat.mul_pos bits positiveNodes)).trans (saved.operands.trans (Nat.div_le_self ..)),
      (Nat.le_mul_of_pos_left _ (Nat.mul_pos printed positiveNodes)).trans (saved.roles.trans (Nat.div_le_self ..))⟩
  exact ⟨axes.oldHost.of_le (fun h i=>(oldHost h i).le),axes.oldGroup.of_le (fun h i=>(oldGroup h i).le),
    previous,blocks.bounded level,heightRoom.of_eventually_le (pitches.mono fun _ q i=>(q i).1),
    heightRoom.of_eventually_le (pitches.mono fun _ q i=>(q i).2)⟩

/-- The positive token of every original node also pays for its one-bit
presence at either of the two archived pitches. -/
theorem registered_presence
    (r : DescentResetPriorHostPad.Shape.ScalarRoom (fun h i=>pad_ h i))
    (archives : ∀ᶠ h:ℕ in atTop,∀i,Chronology.DatePorts.ArchiveWidths G (S_ h i) op (ports h i)
      (k_ h) (tb_ h) (p h i) drift (degree h i) h (age h i)) :
    DescentPriorNodePresence.Chart.ScalarRoom (fun h i=>presence_ h i) :=by
  have computed : ∀ᶠ h:ℕ in atTop,∀i,
        (ports h i).tokenBits*(ports h i).nodes*(ports h i).roleLanes≤h ∧
        (ports h i).nodes*(ports h i).roleLanes≤h ∧
        (ports h i).nodes*(ports h i).operandLanes≤h :=by
    filter_upwards [archives] with h saved
    intro i
    have a:=saved i
    have tokens : 0<(ports h i).tokenBits:=by
      rw [a.token]
      apply Nat.clog_pos (by decide : 1<2)
      unfold DescentPrimitivePalette.colors
      omega
    have bits : 0<(ports h i).operandBits:=by
      rw [a.digits]
      exact (Nat.succ_pos _).trans_le (Nat.le_max_right ..)
    have old : (ports h i).tokenBits*(ports h i).nodes*(ports h i).roleLanes≤h:=by
      rw [a.token]
      exact a.roles.trans (Nat.div_le_self ..)
    exact ⟨old,(Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ tokens)).trans old,
      (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ bits)).trans (a.operands.trans (Nat.div_le_self ..))⟩
  refine ⟨r.hosts,r.groups,r.blocks,r.rolePitch,r.dataPitch,⟨1,?_⟩,⟨1,?_⟩,⟨1,?_⟩⟩
  · simpa only [Nat.one_mul,Chronology.DatePorts.presence] using computed.mono fun h hq i=>(hq i).1
  · simpa only [Nat.one_mul,Chronology.DatePorts.presence] using computed.mono fun h hq i=>(hq i).2.1
  · simpa only [Nat.one_mul,Chronology.DatePorts.presence] using computed.mono fun h hq i=>(hq i).2.2

theorem registered_padded_increments (den : 0<B) (branch : G.b≤2^(capRate G t g))
    (cutoff : 2*(1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g)≤B)
    (receiver : 2*degreeRate G board op t f g reset maximum≤B) (tailBought : τ≤B)
    (stagePayload : ∀h i j,(ordinary h i j).payload=h)
    (bound : ℕ) (small : ∀h i,p h i≤h) (degrees : ∀h i,degree h i≤bound)
    (seed : Bounded sites) (before : ∀h i,age h i<(S_ h i).length)
    (oldDegree : ∀h i,((ports h i).venue).degree≤ maximum) (oldCap : ∀h i,((ports h i).venue).cap=cap_ h i)
    (oldPaid : ∀h i,((ports h i).venue).paidBits=(S_ h i).censusBits (p h i))
    (oldHost : ∀h i,((ports h i).venue).hosts=(S_ h i).hostSize (age h i))
    (oldGroup : ∀h i,((ports h i).venue).groups=(S_ h i).groupCount (age h i))
    (oldK : ∀h i,((ports h i).venue).k=k_ h) (oldM : ∀h i,((ports h i).venue).lanes=2^(oldCut_ h i))
    (degreeQuota : maximum≤quota t)
    (archives : ∀ᶠ h:ℕ in atTop,∀i, Chronology.DatePorts.ArchiveWidths G (S_ h i) op (ports h i)
      (k_ h) (tb_ h) (p h i) drift (degree h i) h (age h i))
    («arguments» : ∀ᶠ h:ℕ in atTop,∀i,Chronology.DatePorts.ArgumentSlots G (S_ h i) (ports h i) drift) :
    Bounded (fun h i=>(a_ h i).fullEnd-floor h i) :=by
  have r:=registered_pad G op t f g reset τ drift B sites age p degree ports seed before oldHost oldGroup «arguments» archives
  have pad:=DescentResetPriorHostPad.Shape.extent_rate _ r
  have occupied:=registered_presence G op t f g reset τ drift B sites age p degree ports r archives
  have prefix_:=DescentPriorNodePresence.Chart.rate (fun h i=>presence_ h i) occupied
    (fun h i=>(pad_ h i).endAddress 0) pad
  have inner:=registered_increments G board op t f g reset τ maximum drift B sites age p degree
    (fun h i=>inside_ h i) ordinary ports den branch cutoff receiver tailBought stagePayload bound small degrees
    seed before oldDegree oldCap oldPaid oldHost oldGroup oldK oldM degreeQuota archives
  apply (prefix_.add inner).of_le
  intro h i
  have put : inside_ h i=floor h i+(presence_ h i).endAddress ((pad_ h i).endAddress 0):=by
    change (presence_ h i).endAddress ((pad_ h i).endAddress (floor h i))=_
    rw [(presence_ h i).translated ((pad_ h i).endAddress (floor h i)),
      (presence_ h i).translated ((pad_ h i).endAddress 0),(pad_ h i).translated (floor h i)]
    omega
  have last : inside_ h i≤(a_ h i).inner.fullEnd (inside_ h i):=(a_ h i).stages.2
  change (a_ h i).inner.fullEnd (inside_ h i)-floor h i≤
    (presence_ h i).endAddress ((pad_ h i).endAddress 0)+((a_ h i).inner.fullEnd (inside_ h i)-inside_ h i)
  omega

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
