import OAI.Hierarchy.DescentProfiledResetArea
import OAI.Hierarchy.DescentRegisteredPackingWidth

namespace OAI
/-! The original reset Canvas has one address aperture for all calibrated tails. -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline.ResetArea
open DescentCompiler TerminalScale DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset
open DescentSixParty.PackedFlow.Canvas DescentPackedWalsh DescentPackedFlowPublication DescentWalshPrecision Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ}
  (board : NonlinearExpanders.Graph n d) (op : RotorSpec) (t f g reset drift degreeMax : ℕ)
local notation "A" h:arg => ResetArea G board op t f g reset drift degreeMax h
local notation "I" h:arg => {x : A h // x.Verified ∧ x.frozen ≤ Nat.log 2 h}
local notation "v" i:arg => (i).val.stage
local notation "P" i:arg => (v i).chart ((v i).stageStart (i).val.inside)
local notation "dim_" i:arg => (i).val.sched.groupWidth (i).val.k (i).val.frozen (i).val.v.age+(i).val.k

theorem uniform_canvas : ResetOutput.EntranceRoom (fun h (i:I h)=>v i) (fun _ i=>i.val.inside) :=by
  let κ:=1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
  have dim (h) (i:I h) : (v i).high+(v i).low=dim_ i:=Nat.sub_add_cancel (Nat.min_le_left ..)
  have extent (h) (i:I h) : dim_ i ≤ h:=(Nat.le_mul_self _).trans (i.property.1.matrix.trans (Nat.div_le_self ..))
  have old : Bounded (fun h (i:I h)=>(v i).hosts):=⟨3,Eventually.of_forall fun _ i=>i.property.1.oldHost⟩
  have axis : Bounded (fun h (i:I h)=>2^((v i).high+(v i).low)):=by
    refine ⟨1,Eventually.of_forall fun h i=>?_⟩
    change 2^((v i).high+(v i).low) ≤ 2^(1*h)
    rw [dim h i,Nat.one_mul]
    exact Nat.pow_le_pow_right (by decide) (extent h i)
  have radical : Bounded (fun h (i:I h)=>2^(v i).k):=axis.of_le fun h i=>by
    change 2^(v i).k ≤ 2^((v i).high+(v i).low)
    rw [dim h i]
    exact Nat.pow_le_pow_right (by decide) (Nat.le_add_left ..)
  have high : Bounded (fun h (i:I h)=>2^(v i).high):=axis.of_le fun _ _=>Nat.pow_le_pow_right (by decide) (Nat.le_add_right ..)
  have geo : ∀h (i:I h),dim_ i ≤ (1+κ*(t+2))*(Nat.log 2 h+1)^2:=by
    intro h i
    exact registered_matrix_dimension G t i.val.ageHeight f g reset i.val.v.sites i.val.frozen i.val.v.age h
      (Nat.div_le_self ..) i.property.2
  have packed : ∀ᶠ h:ℕ in atTop,∀i:I h,8*(P i).geo.bits ≤ (v i).payload/2:=
    Eventually.of_forall fun _ i=>i.property.1.packed
  have canvas : Placement.ScalarRoom (fun h (i:I h)=>P i) (fun _ i=>(v i).payload) (fun _ i=>(v i).gain):={
    hosts:=old
    ports:=(Bounded.const (atRound t)).of_le fun _ i=>i.val.reached_degree.le
    pitch:=((((Bounded.const 2).mul old).add (Bounded.const 1)).mul high).of_le fun _ _=>Book.pitch_upper _ _
    payload:=⟨1,Eventually.of_forall fun h i=>by change h ≤ 1*h;simp⟩
    axis:=⟨1+κ*(t+2),Eventually.of_forall fun h i=>by change (v i).high+(v i).low ≤ _;rw [dim];exact geo h i⟩
    lanes:=Eventually.of_forall fun h i=>by
      change laneBits ((v i).high+(v i).low) h (v i).bits=(v i).low
      rw [dim];rfl
    small:=packed
    gains:=Eventually.of_forall fun _ _=>gain_le _ _ _ _
    routeBits:=packed.mono fun h hh i=>by
      have key:=keys_fit (m:=dim_ i) (v i).positive ((hh i).trans (Nat.div_le_self ..))
      unfold bigKey at key
      exact (Nat.le_add_left ..).trans key
    square:=Eventually.of_forall fun h i=>by
      change ((v i).high+(v i).low)*((v i).high+(v i).low) ≤ h/2
      rw [dim h i]
      exact i.property.1.matrix
  }
  refine ⟨canvas,radical,axis,Eventually.of_forall (fun _ i=>i.property.1.book),?_,?_,
    Eventually.of_forall fun _ i=>i.property.1.reblock⟩
  · apply axis.of_le
    intro h i
    change (v i).groups ≤ 2^((v i).high+(v i).low)
    rw [dim h i]
    exact Nat.pow_le_pow_right (by decide) (Nat.le_add_right ..)
  · apply axis.of_le
    intro h i
    change 2^(v i).e ≤ 2^((v i).high+(v i).low)
    rw [dim h i]
    have ex : (v i).e ≤ (v i).low-i.val.k:=by
      change laneBits (min _ (min _ _)) _ _ ≤ _
      exact (Nat.min_le_left ..).trans (Nat.min_le_left ..)
    exact Nat.pow_le_pow_right (by decide) (ex.trans ((Nat.sub_le ..).trans (Nat.min_le_left ..)))

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline.ResetArea

end OAI
