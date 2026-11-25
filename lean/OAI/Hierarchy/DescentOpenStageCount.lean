import OAI.Hierarchy.DescentOpenCopyCount
import OAI.Hierarchy.DescentOpenGrainWidth
import OAI.Hierarchy.DescentCalendarNumbers
import OAI.Hierarchy.DescentGrainCalendar
import OAI.Hierarchy.DescentGlobalControlRoom

namespace OAI
/-! # Actual copy multiplicity of the ordinary and reset stage compiler -/

namespace Hierarchy.DescentSixParty
open DescentCompiler
open Filter
variable {F : Type} [Field F] (G : PoweredGadget F)

/-- The constant is fixed by the menu before the stage height, input size,
and physical packing width are chosen. -/
theorem stage_open_copy_count (t f g reset τ : ℕ) :
    let κ := 1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
    ∀ h J initial p : ℕ,
      let S := stageNumbers G t J f g reset initial (τ*(J+1))
      let p₀ := S.firstWidth G.b p
      0<p₀ → p₀≤h → 2^J≤h →
      0<S.copies*p₀ ∧ Real.logb 2 (S.copies*p₀:ℕ) ≤
        ((τ+κ)*(t+2)+1:ℕ)*(Real.logb 2 (2*(h:ℝ)))^2 := by
  intro κ h J initial p S p₀ hp width age
  let k:=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
  exact S.open_copy_count τ κ k h p₀ rfl rfl (groupBits_linear ..) hp width age

/-- One integer grain and copy count, chosen before the replacement or its
queries, give both the original packing inequalities and the real copy cap. -/
theorem stage_open_physical_counts (t f g reset τ a B : ℕ) (pos : 0<B)
    (bought : 2*a+Nat.clog 2 G.b*(t+1)≤B) :
    let κ := 1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀ initial q : ℕ, 0<q → q≤2^(a*(J+1)) →
        let S:=stageNumbers G t J f g reset initial (τ*(J+1))
        let p:=h/(16*(q*(G.b^(t*J)*G.b)))
        let p₀:=S.firstWidth G.b p
        0<p ∧ 16*(q*p₀)≤h ∧ h≤32*(q*p₀) ∧ 0<S.copies*p₀ ∧
          Real.logb 2 (S.copies*p₀:ℕ) ≤ ((τ+κ)*(t+2)+1:ℕ)*(Real.logb 2 (2*(h:ℝ)))^2 := by
  intro κ
  have bpos : 0<G.b := by have := G.paid;omega
  have cap := Nat.le_pow_clog (by decide : 1<2) G.b
  filter_upwards [AtomSchedule.open_grain_width t G.b (Nat.clog 2 G.b) a B bpos cap pos bought,
    eventually_ge_atTop 1] with h choose large
  intro J initial q hq short S p p₀
  obtain ⟨active,nonempty,width,lower,upper⟩:=choose S rfl rfl q hq short
  have scale : 2^J≤h := (Nat.pow_le_pow_right (by decide : 0<2)
    (Nat.div_le_self (Nat.log 2 h) (2*B))).trans (Nat.pow_log_le_self 2 (by omega))
  exact ⟨active,lower,upper,stage_open_copy_count G t f g reset τ h J initial p nonempty width scale⟩

/-- The upper size window of the actual selected sort. Even a fixed polynomial
overhead for each independent copy of the input fits under the threefold
height cap. The bound is uniform in the size of the input and its packing. -/
theorem stage_open_record_capacity (t f g reset τ C power : ℕ) :
    ∀ᶠ h : ℕ in atTop, ∀ J initial M p₀ records : ℕ, J≤Nat.log 2 h →
      M≤(2^h)^2 → p₀≤h →
      let S:=stageNumbers G t J f g reset initial (τ*(J+1))
      records≤C*(h+1)^power*M*(S.copies*p₀) → records≤2^(3*h) := by
  let κ:=1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
  let K:=(τ+κ)*(t+2)
  filter_upwards [global_control_shared C (power+1) K 2 0] with h overhead
  intro J initial M p₀ records age size width S measured
  let k:=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
  have bits : k≤κ*(J+1) := groupBits_linear ..
  have outer : τ*(J+1)+k≤(τ+κ)*(J+1) := by
    rw [Nat.add_mul];exact Nat.add_le_add_left bits _
  have radix : k≤(τ+κ)*(J+1) := (Nat.le_add_left ..).trans outer
  obtain ⟨u,cap,formula⟩:=stack_exponent (t:=t) outer radix
  have same : S.copies=2^u := by
    rw [←formula,pow_add]
    change 2^(τ*(J+1))*(2^k)^((t+1)*J+1)=_
    rw [pow_succ];ring
  have binary := overhead J u (2^h) age cap le_rfl
  simp only [pow_zero,Nat.div_one] at binary
  have paid : C*(h+1)^(power+1)*2^u≤2^h :=
    (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)).trans binary
  calc
    records ≤ C*(h+1)^power*M*(S.copies*p₀) := measured
    _ ≤ C*(h+1)^power*(2^h)^2*(2^u*(h+1)) := by
      rw [same];exact Nat.mul_le_mul (Nat.mul_le_mul_left _ size)
        (Nat.mul_le_mul_left _ (width.trans (Nat.le_succ h)))
    _ = (C*(h+1)^(power+1)*2^u)*(2^h)^2 := by rw [pow_succ (h+1)];ring
    _ ≤ 2^h*(2^h)^2 := Nat.mul_le_mul_right _ paid
    _ = 2^(3*h) := by rw [Nat.mul_comm 3 h,pow_mul];ring

end Hierarchy.DescentSixParty

end OAI
