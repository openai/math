import OAI.Hierarchy.DescentUniformResetVenue
import OAI.Hierarchy.DescentOriginalPeerRegions
import OAI.Hierarchy.DescentDatedResetVenue
import OAI.Hierarchy.DescentNextStagePitch
import OAI.Hierarchy.DescentIncomingHosts

namespace OAI
/-! # Original selected root and receiver pitches pay every lookup in the reached reset venue -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty Filter
noncomputable section
variable {F : Type} [Field F] (G:PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
variable (op : RotorSpec) (t f g reset τ D drift B : ℕ) {ι : ℕ→Type*}
variable (sites age size degree root previous nextM base : ∀h,ι h→ℕ) (old : ∀h,ι h→Prior)
local notation "J_" h:arg => Nat.log 2 h/(2*B)
local notation "S_" h:arg i:arg => stageNumbers G t (J_ h) f g reset (sites h i) (tail τ (J_ h))
local notation "k_" h:arg => groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "a_" h:arg i:arg => originalSample G op t f g reset τ D drift (J_ h) (sites h i) (age h i)
  (size h i) (degree h i) h (root h i) (previous h i) (2^(root h i)) (nextM h i) (base h i) (old h i)
set_option quotPrecheck false in
local notation "out_" => fun h i=>(a_ h i).output G board D f g op.C op.w

theorem original_venue_room (positive:0<B)(branch:G.b≤2^(capRate G t g))(bound:ℕ)
    (short:∀h i,size h i≤h)(degrees:∀h i,degree h i≤bound)
    (seed:Bounded sites)(earlier:∀h i,age h i≤(S_ h i).length)
    (oldHosts:∀h i,(old h i).venue.hosts=(S_ h i).hostSize (age h i))
    (oldK:∀h i,(old h i).venue.k=k_ h)
    (next:∀h i,root h i≤(S_ h i).groupWidth (k_ h) (tail τ (J_ h)) (age h i+1))
    (priced:Installed (out_))
    (mask:∃C:ℕ,∀ᶠ h:ℕ in atTop,∀i,nextM h i≤C*h):
    ResetVenue.ScalarRoom (fun h i=>(out_ h i).venue):=by
  have r:=original_inputs G board op t f g reset τ D drift B sites age size degree root previous nextM base old
    positive branch bound short degrees
  have axes:=schedule_space G t f g reset τ B sites age seed earlier
  have level:∀ᶠ h:ℕ in atTop,J_ h≤h:=Eventually.of_forall fun h=>(Nat.div_le_self ..).trans (Nat.log_le_self 2 h)
  have M:Bounded (fun h i=>2^(root h i)):=axes.newGroup.of_le fun h i=>
    (Nat.pow_le_pow_right (by decide) (next h i)).trans (((S_ h i).group_power (k:=k_ h) rfl rfl _).le)
  have oldG:Bounded (fun h i=>2^((S_ h i).groupWidth (k_ h) (tail τ (J_ h)) (age h i))):=
    axes.oldGroup.of_le fun h i=>((S_ h i).group_power (k:=k_ h) rfl rfl _).le
  exact uniform_venue_room G board op t f g reset D drift (fun h=>J_ h)
    (fun _ _=>τ) (fun h _=>J_ h) sites age size degree root previous nextM base old
    r level axes.oldHost axes.newHost oldG axes.newGroup M oldHosts oldK priced mask

/-- The original public incoming width fits at ordinary, reset and final dates, including an empty epoch. -/
theorem normalized_mask_rate (payloadCode:∀h,ι h→ℕ→DescentPacking.PackedMatch.Local.Stage.Dated.Ordinary)
    (ordinary:∀h i j,(payloadCode h i j).payload=h)
    (positive:0<B)(term:τ≤B):
    ∀ᶠ h:ℕ in atTop,∀i,nextM h i=NativePitch.incoming (S_ h i) (k_ h) (tail τ (J_ h))
      (size h i) f h (payloadCode h i) (age h i+1)→nextM h i≤1*h:=by
  filter_upwards [eventually_ge_atTop (2^(2*B))] with h large
  have hp:0<h:=(Nat.two_pow_pos _).trans_le large
  have logRoom:2*B≤Nat.log 2 h:=Nat.le_log_of_pow_le (by decide) large
  have divPos:0<J_ h:=Nat.div_pos logRoom (by omega)
  have cpp:(J_ h)*(2*B)≤Nat.log 2 h:=Nat.div_mul_le_self ..
  have tailRoom:tail τ (J_ h)≤Nat.log 2 h:=by
    unfold tail
    calc
      τ*((J_ h)+1)≤B*((J_ h)+1):=Nat.mul_le_mul_right _ term
      _≤B*((J_ h)+(J_ h)):=Nat.mul_le_mul_left _ (by omega)
      _=(J_ h)*(2*B):=by ring
      _≤_:=cpp
  intro i chosen
  rw [chosen,Nat.one_mul]
  unfold NativePitch.incoming
  split
  · split
    · unfold NativePitch.resetCut DescentPackedWalsh.laneBits
      apply le_trans _ (Nat.pow_log_le_self 2 hp.ne')
      apply Nat.pow_le_pow_right (by decide : 0<2)
      exact (Nat.sub_le ..).trans ((Nat.min_le_right ..).trans (Nat.log_mono_right (Nat.div_le_self ..)))
    · change (payloadCode h i _).payload/(2*(payloadCode h i _).unit)≤h
      rw [ordinary];exact Nat.div_le_self ..
  · simp only [AtomSchedule.groupCount,Nat.sub_self,pow_zero,Nat.mul_one]
    exact (Nat.pow_le_pow_right (by decide) tailRoom).trans (Nat.pow_log_le_self 2 hp.ne')

theorem scheduled_venue_room
    (programs:∀h,ι h→ℕ→DescentPacking.PackedMatch.Local.Stage.Dated.Ordinary)
    (issued:∀h i j,(programs h i j).payload=h)
    (positive:0<B)(tailRoom:τ≤B)(branch:G.b≤2^(capRate G t g))(bound:ℕ)
    (short:∀h i,size h i≤h)(degrees:∀h i,degree h i≤bound)
    (seed:Bounded sites)(earlier:∀h i,age h i<(S_ h i).length)
    (resetSlot:∀h i,age h i%((S_ h i).rounds+1)=(S_ h i).rounds)
    (oldHomes:∀h i,(old h i).venue.hosts=NativePitch.incomingHosts (S_ h i) (age h i))
    (oldRadix:∀h i,(old h i).venue.k=k_ h)
    (choice:∀h i,nextM h i=NativePitch.incoming (S_ h i) (k_ h) (tail τ (J_ h)) (size h i) f h (programs h i) (age h i+1))
    (rootFits:∀h i,root h i≤(S_ h i).groupWidth (k_ h) (tail τ (J_ h)) (age h i+1))
    (fixed:Installed (out_)):ResetVenue.ScalarRoom (fun h i=>(out_ h i).venue):=by
  have masks:=normalized_mask_rate G t f g reset τ B sites age size nextM programs issued positive tailRoom
  have prior:∀h i,(old h i).venue.hosts=(S_ h i).hostSize (age h i):=by
    intro h i
    rw [oldHomes,NativePitch.incomingHosts,ite_eq_left (earlier h i),ite_eq_left (resetSlot h i)]
  exact original_venue_room G board op t f g reset τ D drift B sites age size degree root previous nextM base old
    positive branch bound short degrees seed (fun h i=>(earlier h i).le) prior oldRadix rootFits fixed
    ⟨1,masks.mono fun h used i=>used i (choice h i)⟩

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
