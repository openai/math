import OAI.Hierarchy.DescentOriginalPeerRegions
import OAI.Hierarchy.DescentDatedRetainedPitches
import OAI.Hierarchy.DescentRetainedCalendarAperture
import OAI.Hierarchy.DescentInitialArgumentCapacity

import OAI.Hierarchy.DescentUniformRetainedSpace

namespace OAI
/-! # The two actual predecessor archives on the public reset schedule -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty Filter
noncomputable section
variable {F : Type} [Field F] (G:PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
variable (op : RotorSpec) (t f g reset τ D drift B : ℕ) {ι : ℕ→Type*}
variable (sites age size degree root previous nextM base : ∀h,ι h→ℕ) (old : ∀h,ι h→Prior)
set_option quotPrecheck false
local notation "J_" h:arg => Nat.log 2 h/(2*B)
local notation "S_" h:arg i:arg => stageNumbers G t (J_ h) f g reset (sites h i) (tail τ (J_ h))
local notation "k_" h:arg => groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "a_" h:arg i:arg => originalSample G op t f g reset τ D drift (J_ h) (sites h i) (age h i)
  (size h i) (degree h i) h (root h i) (previous h i) (2^(root h i)) (nextM h i) (base h i) (old h i)
local notation "out_" => fun h i=>(a_ h i).output G board D f g op.C op.w

local notation "c_" h:arg i:arg => (S_ h i).groupWidth (k_ h) (tail τ (J_ h)) (age h i)
local notation "A_" h:arg i:arg => (out_ h i).setup.retained
local notation "T_" h:arg i:arg => (out_ h i).roleTransfer.transfer

/-- The two true earlier word lengths come from the preceding archive's issued
seven fields and its positive primitive labels. Both traversals have their own
physically selected matrix tile. -/
theorem original_retained (positive : 0<B) (branch : G.b≤2^(capRate G t g)) (bound : ℕ)
    (short : ∀h i,size h i≤h) (degrees : ∀h i,degree h i≤bound)
    (seed : Bounded sites) (before : ∀h i,age h i<(S_ h i).length)
    (caps : ∀ᶠ h:ℕ in atTop,∀i,(old h i).nodes≤(S_ h i).retainedNodes ∧
      (old h i).arguments≤(S_ h i).retainedArgumentsAt G drift)
    (priorLanes : Bounded (fun h i=>(old h i).operandLanes))
    (roleLanes : Bounded (fun h i=>(old h i).primitiveLanes))
    (archive : ∀ᶠ h:ℕ in atTop,∀i,
      (A_ h i).wholeWord*(old h i).operandLanes≤h/2 ∧ (T_ h i).wholeWord*(old h i).primitiveLanes≤h/2)
    (selected : ∀ᶠ h:ℕ in atTop,∀i,8*(out_ h i).groupWidth≤h) :
    DescentResetRetainedSetup.Layout.ScalarRoom (fun h i=>A_ h i) ∧
    DescentResetRetainedSetup.Layout.ScalarRoom (fun h i=>T_ h i) :=by
  have cal:=original_inputs G board op t f g reset τ D drift B sites age size degree root previous nextM base old
    positive branch bound short degrees
  have axes:=schedule_space G t f g reset τ B sites age seed (fun h i=>(before h i).le)
  have level : ∀ᶠ h:ℕ in atTop,J_ h≤h:=Eventually.of_forall fun h=>
    (Nat.div_le_self ..).trans (Nat.log_le_self ..)
  have oldG : Bounded (fun h (i:ι h)=>2^((S_ h i).groupWidth (k_ h) (tail τ (J_ h)) (age h i))):=
    axes.oldGroup.of_le fun h i=>((S_ h i).group_power (k:=k_ h) rfl rfl _).le
  exact uniform_retained G board op t f g reset D drift (fun h=>J_ h) (fun _ _=>τ) (fun h _=>J_ h)
    sites age size degree root previous nextM base old cal level
    axes.oldHost oldG axes.matrices before caps priorLanes roleLanes archive selected

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
