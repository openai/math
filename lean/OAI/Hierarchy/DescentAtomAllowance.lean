import OAI.Hierarchy.DescentCompilerSlack

namespace OAI
/-! # Counting retained descriptions only at their creation -/

namespace Hierarchy.DescentCompiler
open scoped BigOperators Classical

/-- The exponent is chosen after the fixed host growth and the per-site
new atom count. It includes room for all stage indices and one factor T. -/
def atomExponent (t c fixed slope : ℕ) := 1+(c+1)*(t+1)+fixed+slope

private theorem atom_power {t J c fixed slope : ℕ} (hJ : 0<J) :
    ((t+1)*J)+c*((t+1)*J)+(fixed+slope*J)+J ≤ J*atomExponent t c fixed slope := by
  have gain := Nat.mul_le_mul_left fixed (show 1≤J from hJ)
  unfold atomExponent
  nlinarith only [gain]

/-- The native lists are indexed by stage and by actual occurrence. The
old references retained through a contraction are counted at their creation
stage, including the initial census atoms at stage zero. -/
theorem atom_lists {Atom : Type*} {t J c fixed slope R r m : ℕ} (hJ : 0<J)
    (H : ℕ→ℕ) (initial : H 0≤m) (growth : ∀i,H (i+1)≤H i*(2^c*r))
    (S : ℕ→Type) [∀i,Fintype (S i)]
    (slots : ∀i≤(t+1)*J,Fintype.card (S i)≤H i*blocks R r ((t+1)*J) i)
    (born : ∀i,S i→List Atom) (limit : ∀i≤(t+1)*J,∀v,(born i v).length≤2^(fixed+slope*J)) :
    (∑i∈Finset.range ((t+1)*J+1),∑v,(born i v).length)*2^J ≤
      (m*(R*r^((t+1)*J)))*(2^J)^atomExponent t c fixed slope := by
  let l := (t+1)*J
  let mass := m*(R*r^l)
  let L := 2^(fixed+slope*J)
  have atStage (i) (hi : i≤l) : (∑v,(born i v).length)≤mass*((2^c)^l)*L := by
    have count := (slots i hi).trans (all_positions H m (2^c) r R initial growth hi)
    have grow : (2^c)^i≤(2^c)^l := Nat.pow_le_pow_right (Nat.two_pow_pos _) hi
    calc
      _ ≤ ∑_v : S i,L := Finset.sum_le_sum fun v _=>limit i hi v
      _ = Fintype.card (S i)*L := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (count.trans (Nat.mul_le_mul_left _ grow))
  have all : (∑i∈Finset.range (l+1),∑v,(born i v).length)≤2^l*(mass*(2^c)^l*L) := by
    calc
      _ ≤ ∑_i∈Finset.range (l+1),mass*(2^c)^l*L :=
        Finset.sum_le_sum fun i hi=>atStage i (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      _ = (l+1)*(mass*(2^c)^l*L) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (show l+1≤2^l from Nat.lt_two_pow_self)
  refine (Nat.mul_le_mul_right (2^J) all).trans ?_
  change 2^l*(mass*(2^c)^l*L)*2^J ≤ mass*(2^J)^atomExponent t c fixed slope
  have powers : 2^l*(2^c)^l*L*2^J≤(2^J)^atomExponent t c fixed slope := by
    dsimp only [L]
    rw [←pow_mul,←pow_add,←pow_add,←pow_add,←pow_mul]
    exact Nat.pow_le_pow_right (by decide) (atom_power hJ)
  simpa only [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using Nat.mul_le_mul_left mass powers

/-- The same atom price fits under the half-cap reserved at one new site. -/
theorem new_site_slack {t J c fixed slope fresh B gain : ℕ} (hJ : 0<J)
    (budget : fresh≤2^(fixed+slope*J)) (reserve : 2≤B*gain) :
    2*fresh ≤ (B*gain)*(2^J)^atomExponent t c fixed slope := by
  have h := atom_power (t:=t) (c:=c) (fixed:=fixed) (slope:=slope) hJ
  have enough : 2^(fixed+slope*J) ≤ (2^J)^atomExponent t c fixed slope := by
    rw [←pow_mul]
    apply Nat.pow_le_pow_right (by decide)
    omega
  exact Nat.mul_le_mul reserve (budget.trans enough)

end Hierarchy.DescentCompiler

end OAI
