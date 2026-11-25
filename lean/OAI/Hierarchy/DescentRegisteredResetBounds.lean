import OAI.Hierarchy.DescentDatedArchiveWidths
import OAI.Hierarchy.DescentScheduledAllResetBounds

namespace OAI
/-! # Uniform complete reset amount on the chronological archive actually returned to the machine -/
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
local notation "a_" h:arg i:arg =>scheduled G (S_ h i) board (k_ h) (tb_ h) (age h i) (p h i) f g drift (degree h i) h
  (ordinary h i) op (seed_ h i) (grain_ h i) ((ports h i).operandLanes) ((ports h i).roleLanes) ((ports h i).venue)
  ((ports h i).io.wire) ((ports h i).io.roster) (floor h i)
theorem registered_increments (den : 0<B) (branch : G.b≤2^(capRate G t g))
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
      (k_ h) (tb_ h) (p h i) drift (degree h i) h (age h i)) :
    Bounded (fun h i=>(a_ h i).fullEnd (floor h i)-floor h i) :=by
  apply all_scheduled_increments G board op t f g reset τ maximum drift B sites age p degree
    (fun h i=>(ports h i).operandLanes) (fun h i=>(ports h i).roleLanes) floor ordinary
    (fun h i=>(ports h i).venue) (fun h i=>(ports h i).io.wire) (fun h i=>(ports h i).io.roster)
    den branch cutoff receiver tailBought stagePayload bound small degrees seed before oldDegree oldCap oldPaid
    oldHost oldGroup oldK oldM degreeQuota
  filter_upwards [archives] with h loaded
  intro i
  exact (loaded i).previous G (S_ h i) op

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
