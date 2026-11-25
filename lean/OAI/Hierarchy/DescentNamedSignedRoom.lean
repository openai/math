import OAI.Hierarchy.DescentNamedSignedDate
import OAI.Hierarchy.DescentSignedFormatRoom
import OAI.Hierarchy.DescentDatedScheduleSpace
import OAI.Hierarchy.DescentDatedOrdinarySignedExtent

namespace OAI
/-! # The complete signed memory region in the original ordinary calendar -/
namespace Hierarchy.DescentDatedAddressBook.SignedStage
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) {ι : ℕ → Type*}
variable (t f g reset τ B : ℕ) (sites age : ∀h,ι h → ℕ)
local notation "J_" h:arg => Nat.log 2 h/(2*B)
local notation "S_" h:arg i:arg => stageNumbers G t (J_ h) f g reset (sites h i) (tail τ (J_ h))
local notation "k_" h:arg => groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "q_" h:arg i:arg => atDate G (S_ h i) g (k_ h) (age h i) (NativePitch.incomingHosts (S_ h i) (age h i+1))
local notation "s_" h:arg i:arg => signedAt G (S_ h i) g (k_ h) (age h i) h

theorem signedAt_scalar_room (source : Bounded sites) (before : ∀h i,age h i ≤ (S_ h i).length)
    (room : ∀h i,2*(q_ h i).unit ≤ h) : SignedExtent.ScalarRoom (fun h i=>s_ h i) := by
  have space:=schedule_space G t f g reset τ B sites age source before
  have high : Bounded (fun h i=>(q_ h i).newHosts) := by
    apply (space.oldHost.padded.max' space.newHost.padded).of_le
    intro h i
    let S:=S_ h i
    let a:=age h i
    have within : a≤S.length := before h i
    change NativePitch.incomingHosts S (a+1) ≤ max (hostRows (S.hostSize a)) (hostRows (S.hostSize (a+1)))
    by_cases inside : a+1≤S.length
    · exact (NativePitch.hosts_bounds S _ inside).2.trans (le_max_right ..)
    · have last : a=S.length:=by omega
      rw [last]
      simp only [NativePitch.incomingHosts, Nat.not_lt_of_ge (Nat.le_succ _),ite_false]
      exact (hostPad _).trans (le_max_left ..)
  exact format_scalar_room (fun h i=>q_ h i) space.oldHost.padded high space.newGroup room

/-- The issued lane is paid at all sufficiently large heights.  Restricting the auxiliary index to
that range allows the physical format itself (including the zero-lane initial heights) to remain
exactly the one used by the original calendar. -/
theorem signedAt_roof_bounded (source : Bounded sites) (before : ∀h i,age h i ≤ (S_ h i).length)
    (room : ∀ᶠ h : ℕ in atTop,∀i,2*(q_ h i).unit ≤ h) : Bounded (fun h i=>(s_ h i).roof 0) := by
  let ix := fun h => {i : ι h // 2*(q_ h i).unit ≤ h}
  let smallSites : ∀h,ix h → ℕ := fun h i=>sites h i.val
  let smallAge : ∀h,ix h → ℕ := fun h i=>age h i.val
  obtain ⟨C,base⟩:=source
  have paid : Bounded smallSites:=⟨C,base.mono (fun _ reads i=>reads i.val)⟩
  have field:=signedAt_scalar_room G t f g reset τ B smallSites smallAge paid
    (fun h i=>before h i.val) (fun _ i=>i.property)
  obtain ⟨K,tariff⟩:=SignedExtent.rate _ field
  refine ⟨K,?_⟩
  filter_upwards [room,tariff] with h ok fits
  exact fun i=>fits (⟨i,ok i⟩ : ix h)

end
end Hierarchy.DescentDatedAddressBook.SignedStage

end OAI
