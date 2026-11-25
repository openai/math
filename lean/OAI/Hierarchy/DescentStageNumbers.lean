import OAI.Hierarchy.DescentCompilerSlack

namespace OAI
/-! # Uniform common-position and per-site root invoices including the final stage -/

namespace Hierarchy.DescentCompiler
noncomputable section

/-- One additional group remains available at the very last graph. This
lets the same real grouped-placement invariant include the terminal graph. -/
def residual (R r last age : ℕ) := R*r^(last-age)

theorem residual_step {R r last age : ℕ} (inside : age<last) :
    residual R r last (age+1)*r=residual R r last age := by
  simp only [residual,Nat.mul_assoc,←pow_succ]
  congr 2
  omega

theorem residual_count {R r last age : ℕ} (h : age≤last) :
    residual R r last age*r*r^age = R*r^(last+1) := by
  unfold residual
  rw [Nat.mul_assoc,←pow_succ',Nat.mul_assoc,←pow_add]
  congr 2
  omega

/-- The kernel proof uses the already chosen power-of-two stage width. The
same inequality also holds when age is the final terminal or reset age. -/
theorem point_root {t J c g f R M H age a B : ℕ} (ageBound : age≤(t+1)*J)
    (host : H≤M*(2^c*2^groupBits t J c g f)^age) (cut : a≤f)
    (cap : B≤2^(8+g*age)) :
    let last := (t+1)*J
    let r := 2^groupBits t J c g f
    (residual R r last age*H)*(2^a*B)*2^J≤M*(R*r^(last+1)) := by
  let last := (t+1)*J
  let r := 2^groupBits t J c g f
  let groups := residual R r last age
  have resource : (2^c)^age*(2^a*B)*2^J≤r := by
    apply (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ cap))).trans
    change (2^c)^age*(2^a*2^(8+g*age))*2^J≤2^groupBits t J c g f
    rw [←pow_mul,←pow_add,←pow_add,←pow_add]
    apply Nat.pow_le_pow_right (by decide)
    have cg:=Nat.mul_le_mul_left c ageBound
    have gg:=Nat.mul_le_mul_left g ageBound
    unfold groupBits
    rw [Nat.add_mul]
    omega
  have counted := residual_count (R:=R) (r:=r) ageBound
  change groups*H*(2^a*B)*2^J≤M*(R*r^(last+1))
  calc
    _ ≤ groups*(M*(2^c*r)^age)*(2^a*B)*2^J := by gcongr
    _ = (M*(groups*r^age))*((2^c)^age*(2^a*B)*2^J) := by rw [mul_pow];ring
    _ ≤ (M*(groups*r^age))*r := Nat.mul_le_mul_left _ resource
    _ = M*(R*r^(last+1)) := by
      change _=M*(R*r^((t+1)*J+1))
      rw [←counted]
      dsimp only [groups,last]
      ring

/-- Apply the integer position invoice to the actual physical hub scale.
The scalar q measures one retained unit throughout an entire history. -/
theorem point_root_real {t J c g f R M H age a : ℕ} {q B : ℝ} (ageBound : age≤(t+1)*J)
    (host : H≤M*(2^c*2^groupBits t J c g f)^age) (cut : a≤f)
    (cap : q*B≤(2:ℝ)^(8+g*age)) :
    let last := (t+1)*J
    let r := 2^groupBits t J c g f
    ((residual R r last age*H:ℕ):ℝ)*((2:ℝ)^a*(q*B)) ≤ (M:ℝ)*(R*r^(last+1):ℕ)/(2:ℝ)^J := by
  let last := (t+1)*J
  let r := 2^groupBits t J c g f
  have num := point_root (R:=R) ageBound host cut (B:=2^(8+g*age)) le_rfl
  apply (le_div_iff₀ (by positivity : (0:ℝ)<2^J)).mpr
  calc
    _ ≤ ((residual R r last age*H:ℕ):ℝ)*((2:ℝ)^a*2^(8+g*age))*(2:ℝ)^J := by gcongr
    _ ≤ _ := by exact_mod_cast num

end
end Hierarchy.DescentCompiler

end OAI
