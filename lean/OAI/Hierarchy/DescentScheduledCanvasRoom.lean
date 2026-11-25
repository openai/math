import OAI.Hierarchy.DescentScheduledResetChart
import OAI.Hierarchy.DescentDatedScheduleSpace
import OAI.Hierarchy.DescentResetRootHeaderScale
import OAI.Hierarchy.DescentMeasuredLaneRoom
import OAI.Hierarchy.DescentDatedResetRate

namespace OAI
/-! Scalar and original lookup bounds for the public Canvas at the actual
post-ingress base of a selected chronological reset. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentCompiler TerminalScale DescentSixParty DescentSixParty.PackedFlow.Canvas DescentPackedWalsh
open DescentPackedFlowPublication DescentWalshPrecision ProtocolRAM Filter
open DescentPacking.PackedMatch.Local.Stage
noncomputable section
set_option quotPrecheck false

variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
    (op : RotorSpec) (t f g reset τ B drift : ℕ) {ι : ℕ→Type*}
    (sites age p degree inputBits numberBits oldOperand oldPrimitive floor : ∀h,ι h→ℕ)
    (ordinary : ∀h,ι h→ℕ→Dated.Ordinary) (old : ∀h,ι h→StageVenueTail.Date)
    (wire : ∀h,ι h→ℕ→ℕ→Bank) (roster : ∀h,ι h→Bank)
local notation "J" h:arg => Nat.log 2 h/(2*B)
local notation "tb" h:arg => tail τ (J h)
local notation "S" h:arg i:arg => stageNumbers G t (J h) f g reset (sites h i) (tb h)
local notation "k" h:arg => groupBits t (J h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "a" h:arg i:arg => scheduled G (S h i) board (k h) (tb h) (age h i) (p h i) f g drift (degree h i) h
  (ordinary h i) op (inputBits h i) (numberBits h i) (oldOperand h i) (oldPrimitive h i) (old h i)
  (wire h i) (roster h i) (floor h i)
local notation "c" h:arg i:arg => (S h i).groupWidth (k h) (tb h) (age h i)
local notation "m" h:arg i:arg => c h i+k h
local notation "b" h:arg i:arg => (S h i).localWalshBits (p h i) (m h i) f (quota t)
local notation "l" h:arg i:arg => laneBits (m h i) h (b h i)
local notation "P" h:arg i:arg => (a h i).chart ((a h i).stageStart (floor h i))

theorem scheduled_canvas_room (D : ℕ) (sources : Bounded sites)
    (height : ∀h i,age h i ≤ (S h i).length) (payload : ∀h i,p h i ≤ h)
    (branch : ∀h i,(old h i).degree ≤ D) :
    Placement.ScalarRoom (fun h i=>P h i) (fun h i=>(a h i).payload) (fun h i=>(a h i).gain) ∧
    Bounded (fun h i=>2^(a h i).k) ∧ Bounded (fun h i=>2^((a h i).high+(a h i).low)) ∧
    Bounded (fun h i=>(a h i).groups) ∧ Bounded (fun h i=>2^(a h i).e) := by
  let A:=localCoefficient G t f g reset (quota t) τ
  have stage:=schedule_space G t f g reset τ B sites age sources height
  have dim (h : ℕ) (i : ι h) : (a h i).high+(a h i).low=m h i:=
    Nat.sub_add_cancel (Nat.min_le_left ..)
  have span (h : ℕ) : tb h ≤ τ*(Nat.log 2 h+1)^2:=
    Nat.mul_le_mul_left _ ((Nat.succ_le_succ (Nat.div_le_self ..)).trans (by nlinarith))
  have count (h : ℕ) (i : ι h) : m h i ≤ b h i:=by
    change _ ≤ DescentWalshPrecision.bits _ _ _ _
    unfold DescentWalshPrecision.bits
    omega
  have axm : Bounded (fun h i=>2^(m h i)):=stage.matrices.of_le fun h i=>by
    apply Nat.pow_le_pow_right (by decide)
    exact Nat.le_mul_self _
  have ax : Bounded (fun h i=>2^((a h i).high+(a h i).low)):=by simpa only [dim] using axm
  have radix : Bounded (fun h i=>2^(a h i).k):=axm.of_le fun h i=>
    Nat.pow_le_pow_right (by decide) (Nat.le_add_left ..)
  have heads : Bounded (fun h i=>2^(a h i).high):=ax.of_le fun h i=>
    Nat.pow_le_pow_right (by decide) (Nat.le_add_right ..)
  have pitchFit : Bounded (fun h i=>(P h i).geo.pitch):=
    ((((Bounded.const 2).mul stage.oldHost).add (Bounded.const 1)).mul heads).of_le fun h i=>Book.pitch_upper _ _
  have bounds:=eventually_actual_width G t f g reset B (quota t) τ
  have small : ∀ᶠ h:ℕ in atTop,∀i,8*(b h i) ≤ h/2:=
    bounds.mono fun h hh i=>(hh (sites h i) (tb h) (age h i) (p h i) (payload h i) (span h) (height h i)).1
  have result:Placement.ScalarRoom (fun h i=>P h i) (fun h i=>(a h i).payload) (fun h i=>(a h i).gain) := {
    hosts:=stage.oldHost
    ports:=(Bounded.const D).of_le branch
    pitch:=pitchFit
    payload:=⟨1,Eventually.of_forall fun h i=>by change h ≤ 1*h;simp⟩
    axis:=⟨A,Eventually.of_forall fun h i=>by
      change (a h i).high+(a h i).low ≤ _
      rw [dim]
      exact (count h i).trans (actual_width G t (J h) f g reset (sites h i) (tb h) (age h i) h (p h i)
        (quota t) τ (payload h i) (Nat.div_le_self ..) (span h) (height h i))⟩
    lanes:=Eventually.of_forall fun h i=>by
      change laneBits ((a h i).high+(a h i).low) h (b h i)=l h i
      rw [dim]
    small:=small
    gains:=Eventually.of_forall fun h i=>gain_le _ _ _ _
    routeBits:=small.mono fun h hh i=>by
      have key:=keys_fit («m»:=m h i) (a h i).positive ((hh i).trans (Nat.div_le_self ..))
      unfold bigKey at key
      exact (Nat.le_add_left ..).trans key
    square:=stage.halfMatrix.mono fun h hh i=>by
      change ((a h i).high+(a h i).low)*((a h i).high+(a h i).low) ≤ h/2
      rw [dim]
      exact hh i
  }
  refine ⟨result,radix,ax,?_,?_⟩
  · apply stage.oldGroup.of_le
    intro h i
    exact ((S h i).group_power («k»:=k h) (tail:=tb h) rfl rfl (age h i)).le
  · apply axm.of_le
    intro h i
    apply Nat.pow_le_pow_right (by decide)
    let e:=(a h i).e
    have ex:e ≤ l h i-k h:=by
      change laneBits (min _ (min _ _)) _ _ ≤ _
      exact (Nat.min_le_left ..).trans (Nat.min_le_left ..)
    exact ex.trans ((Nat.sub_le ..).trans (Nat.min_le_left ..))

theorem scheduled_initial_book (D : ℕ) (den : 0 < B)
    (cutoff : 2*(1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g) ≤ B)
    (height : ∀h i,age h i ≤ (S h i).length) (payload : ∀h i,p h i ≤ h)
    (branch : ∀h i,(old h i).degree ≤ D) :
    ∀ᶠ h:ℕ in atTop,∀i, Book.width (a h i).bits (2^(a h i).k) (a h i).short*(a h i).lanes ≤ (a h i).payload := by
  filter_upwards [measured_lane_room G t f g reset τ B (quota t) cutoff,
    eventually_actual_width G t f g reset B (quota t) τ,
    eventually_ge_atTop (2^(Nat.clog 2 (D+1)*(2*B)))] with h rooms words late
  intro i
  let j:=J h
  have ageFit:j ≤ Nat.log 2 h:=Nat.div_le_self ..
  have logFit:Nat.clog 2 (D+1) ≤ j:=(Nat.le_div_iff_mul_le (by omega : 0 < 2*B)).2 (Nat.le_log_of_pow_le (by decide) late)
  have span:tb h ≤ τ*(Nat.log 2 h+1)^2:=Nat.mul_le_mul_left _ ((Nat.succ_le_succ ageFit).trans (by nlinarith))
  have small:8*(b h i) ≤ h/2:=(words (sites h i) (tb h) (age h i) (p h i) (payload h i) span (height h i)).1
  have fit:k h ≤ l h i:=rooms (sites h i) (age h i) (p h i) (height h i) (payload h i)
  have jk:j ≤ k h:=by change j ≤ j+_+8+_;omega
  have bp:0 < b h i:=(a h i).positive
  have sz:Nat.clog 2 ((old h i).degree+1) ≤ (b h i)*2^(k h):=
    ((Nat.clog_mono_right _ (Nat.add_le_add_right (branch h i) 1)).trans (logFit.trans jk)).trans
      ((Nat.lt_two_pow_self (n:=k h)).le.trans (Nat.le_mul_of_pos_left _ bp))
  have key:=keys_fit («m»:=m h i) bp (small.trans (Nat.div_le_self ..))
  have offset:2^(k h)*2^(l h i-k h)=2^(l h i):=by rw [←pow_add,Nat.add_sub_of_le fit]
  change Book.width (b h i) (2^(k h)) (Nat.clog 2 ((old h i).degree+1))*2^(l h i-k h) ≤ h
  rw [Book.width,max_eq_right (Nat.add_le_add_left sz _)]
  calc
    _ = ((b h i)+(b h i))*2^(l h i):=by rw [←offset];ring
    _ ≤ bigKey (l h i) (b h i):=Nat.le_add_left ..
    _ ≤ h:=key.trans (Nat.div_le_self ..)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
