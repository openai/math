import OAI.Hierarchy.TraceDistributionScale
import OAI.ThreeFlat.Diagonal.NativeTrace
import OAI.ThreeFlat.Diagonal.TraceStaticCost

namespace OAI
/-! # Native 64w-bit verifier and the initial dimensions of paired-input buckets -/

namespace Hierarchy.TraceDistribution
open ThreeFlat Diagonal Computability.VPVNP BurstRAM PrivateRAM
open Filter
open scoped Topology

variable {F : Type} [Field F] [Fintype F] {u s : ℕ → ℕ}

omit [Field F] in
/-- The bounded program text and its external inputs fit on the genuine verifier
grid of depth log₂(U)+1. The machine itself may vary with the word width. -/
theorem native_fits (scale : Scale u s) (pc regs words : ℕ) (hp : 0<pc) :
    ∀ᶠ w : ℕ in atTop,
      Fintype.card F ≤ 2^(64*w) ∧ 2 ≤ u w+1-w/2 ∧ w/2 ≤ u w ∧ u w≤2*w ∧
      ∀ (M : Machine (64*w) pc regs words) (B fuel : ℕ), B≤2^(u w) → fuel≤2^(u w) →
      NativeTrace.Fits M (B+(1+6*pc+words)*(64*w)) B ((u w+1-w/2)+w/2) fuel := by
  have hl := (tendsto_order.mp scale.cap).1 (3/4) (by norm_num)
  have hr := (tendsto_order.mp scale.cap).2 2 (by norm_num)
  filter_upwards [hl,hr,polynomial_room (64*(1+6*pc+words)) 1,
    eventually_ge_atTop (Fintype.card F+pc+regs+words+20)] with w lo hi size large
  have pos : 0 < (w:ℝ) := by exact_mod_cast (show 0<w by omega)
  have lo' := (lt_div_iff₀ pos).mp lo
  have hi' := (div_lt_iff₀ pos).mp hi
  have lower : 3*w ≤ 4*u w := by exact_mod_cast (show (3:ℝ)*w ≤ 4*u w by linarith)
  have upper : u w ≤ 2*w := by exact_mod_cast hi'.le
  have wle : w ≤ 2^(64*w) := (show w≤64*w by omega).trans Nat.lt_two_pow_self.le
  have text : (1+6*pc+words)*(64*w) ≤ 2^(u w) := by
    refine le_trans ?_ (Nat.pow_le_pow_right (n:=2) (by decide) (show w/100≤u w by omega))
    calc
      _ ≤ (64*(1+6*pc+words))*(w+1)^1 := by simp only [pow_one]; nlinarith
      _ ≤ _ := size
  have depth : (u w+1-w/2)+w/2=u w+1 := by omega
  refine ⟨by omega,by omega,by omega,upper,?_⟩
  intro M B fuel hb hf
  have widthU : 2^(u w+1) ≤ 2^(64*w) := Nat.pow_le_pow_right (by decide) (by omega)
  have budget : B+(1+6*pc+words)*(64*w) ≤ 2^(u w+1) := by rw [pow_succ]; omega
  have uwle : 2^(u w) ≤ 2^(64*w+1) := Nat.pow_le_pow_right (by decide) (by omega)
  have prog : 1+6*pc+words ≤ 2^(64*w) := by
    apply (show 1+6*pc+words ≤64*w by omega).trans Nat.lt_two_pow_self.le
  refine ⟨by omega,(show pc≤2^(64*w) by omega).trans (Nat.pow_le_pow_right (by decide) (by omega)),
    hp,budget.trans widthU,hf.trans uwle,?_,⟨by omega,by omega,prog⟩,by omega⟩
  rw [depth,show 1+(u w+1)=(u w+1)+1 by omega,pow_succ,pow_succ]
  omega

/-- The repeated physical table's actual cell count is polynomial in the word
width, uniformly in the instruction data and both the memory and time caps. -/
theorem native_cells {w pc regs words S base d fuel : ℕ} (M : Machine (64*w) pc regs words)
    (fit : NativeTrace.Fits M S base d fuel) (hF : Fintype.card F≤2^(64*w)) (st : Word (64*w))
    (q : Fintype.card F ≤ 64*w) (p : pc ≤ 64*w) (r : regs ≤ 64*w) (k : words ≤ 64*w) (depth : d≤64*w) :
    (TraceStaticRow.gateTable hF fit.width fit.labels base fuel st regs words d).cells ≤
      10^26*(64*w+1)^14 :=
  (TraceStaticRow.gateTable_size hF fit.width fit.labels base fuel st).trans
    (TraceStaticRow.cellsBound_of_le q le_rfl p r k depth)

/-- Multiplying the exact position count by the exact width of each directed
cursor arc charges every row once per offset, slot, argument, and cursor layer. -/
theorem initial_product (u low slots : ℕ) (room : low≤u+1) :
    let k := u+1-low
    let offsets := 1+((u+1)+(u+1))
    (k*2^k)*(2^low*(offsets*slots*3)) = 2^u*(2*k*offsets*slots*3) := by
  dsimp only
  have e : 2^(u+1-low)*2^low=2^u*2 := by rw [←pow_add,Nat.sub_add_cancel room,pow_succ]
  calc
    _ = (2^(u+1-low)*2^low)*((u+1-low)*(1+(u+1+(u+1)))*slots*3) := by ring
    _ = _ := by rw [e]; ring

private def rowWidthConstant := 3*129*10^26*64^14

/-- The fixed polynomial of the row verifier, including its XOR offsets and
three incident arguments, is independent of the chosen saving exponent. -/
theorem seed_arc_width (w d low slots : ℕ) (depth : d≤64*w)
    (cells : slots ≤ 10^26*(64*w+1)^14) :
    2^low*((1+(d+d))*slots*3) ≤ 2^low*(rowWidthConstant*(w+1)^15) := by
  apply Nat.mul_le_mul_left
  have off : 1+(d+d) ≤ 129*(w+1) := by omega
  calc
    _ ≤ (129*(w+1))*(10^26*(64*(w+1))^14)*3 := by
      apply Nat.mul_le_mul_right
      apply Nat.mul_le_mul off
      exact cells.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 14))
    _ = _ := by unfold rowWidthConstant; ring

/-- The product governing both initial work and energy is at most the real
time cap times a fixed polynomial, including the cursor layers. -/
theorem seed_volume (w u low slots : ℕ) (room : low≤u+1) (depth : u+1≤64*w)
    (cells : slots ≤ 10^26*(64*w+1)^14) :
    let k := u+1-low
    let offsets := 1+(u+1+(u+1))
    (k*2^k)*(2^low*(offsets*slots*3)) ≤ 2^u*(128*rowWidthConstant)*(w+1)^16 := by
  dsimp only
  have eqn := initial_product u low slots room
  dsimp only at eqn
  rw [eqn]
  have bound := seed_arc_width w (u+1) 0 slots depth cells
  simp only [pow_zero,one_mul] at bound
  have kbound : u+1-low ≤ 64*(w+1) := by omega
  calc
    _ = 2^u*(2*(u+1-low)*((1+(u+1+(u+1)))*slots*3)) := by ring
    _ ≤ 2^u*(2*(64*(w+1))*(rowWidthConstant*(w+1)^15)) := by gcongr
    _ = _ := by ring

/-- The number of prefix pins in the largest ancestor fiber of one final
factor obeys the same upper bound as its allowed local work. -/
theorem pin_room (scale : Scale u s) (charge : ℕ) :
    ∀ᶠ w : ℕ in atTop, 2^(charge*s w)*(2*2^(w/2)) ≤ 2^(3*w/5) := by
  filter_upwards [factor_room scale 2 0 (2^charge)] with w h
  simp only [pow_zero,mul_one,←pow_mul] at h
  calc
    2^(charge*s w)*(2*2^(w/2)) = 2*2^(charge*s w)*2^(w/2) := by ring
    _ ≤ 2*2^(charge*s w)*2^(max (w/2) (u w-w/2)) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (Nat.le_max_left ..))
    _ ≤ _ := h

/-- The budget for the shared terminal edge string has a fixed polynomial
coefficient independent of the number of blocks and of the cap exponent. -/
theorem terminal_volume (degree slack : ℕ) :
    ∃ C : ℕ, ∀ w u low slots : ℕ, low≤u+1 → u+1≤64*w →
      slots≤10^26*(64*w+1)^14 →
      let k := u+1-low
      let p := k*2^k
      let width := 2^low*((1+(u+1+(u+1)))*slots*3)
      p*degree*width+slack*p ≤ C*2^u*(w+1)^16 := by
  refine ⟨degree*(128*rowWidthConstant)+slack*128,?_⟩
  intro w u low slots room depth cells k p width
  have seed : p*width ≤ 2^u*(128*rowWidthConstant)*(w+1)^16 :=
    seed_volume w u low slots room depth cells
  have pos : p ≤ 128*2^u*(w+1)^16 := by
    have kbound : k ≤64*(w+1) := by dsimp [k]; omega
    have growth : 2^k ≤ 2^(u+1) := Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)
    have poly : w+1≤(w+1)^16 := Nat.le_self_pow (by decide) _
    calc
      p ≤ (64*(w+1))*2^(u+1) := Nat.mul_le_mul kbound growth
      _ = 128*2^u*(w+1) := by rw [pow_succ]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ poly
  calc
    p*degree*width+slack*p = degree*(p*width)+slack*p := by ring
    _ ≤ degree*(2^u*(128*rowWidthConstant)*(w+1)^16)+slack*(128*2^u*(w+1)^16) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ seed) (Nat.mul_le_mul_left _ pos)
    _ = _ := by ring

end Hierarchy.TraceDistribution

end OAI
