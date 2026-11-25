import OAI.Hierarchy.DescentDatedAddressBook
import Mathlib.Order.Filter.AtTopBot.Basic

namespace OAI
/-! # A uniform address exponent for every reached date, including padded banks -/
namespace Hierarchy.DescentDatedAddressBook
open Filter
variable {ι : ℕ→Type*}

def Bounded (x : ∀h,ι h→ℕ) := ∃A : ℕ,∀ᶠ h:ℕ in atTop,∀i,x h i≤2^(A*h)

namespace Bounded
variable {x y : ∀h,ι h→ℕ}

theorem of_le (b : Bounded x) (le : ∀h i,y h i≤x h i) : Bounded y := by
  obtain ⟨A,room⟩:=b
  exact ⟨A,room.mono fun h hh i=>(le h i).trans (hh i)⟩

theorem const (n : ℕ) : Bounded (ι:=ι) (fun _ _=>n) := by
  refine ⟨n,?_⟩
  filter_upwards [eventually_ge_atTop 1] with h one
  intro i
  exact Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right _ one))

theorem add (bx : Bounded x) (by' : Bounded y) : Bounded (fun h i=>x h i+y h i) := by
  obtain ⟨A,ra⟩:=bx
  obtain ⟨B,rb⟩:=by'
  refine ⟨max A B+1,?_⟩
  filter_upwards [ra,rb,eventually_ge_atTop 1] with h ha hb high
  intro i
  have a:= (ha i).trans (Nat.pow_le_pow_right (by decide : 0<2) (Nat.mul_le_mul_right h (le_max_left A B)))
  have b:= (hb i).trans (Nat.pow_le_pow_right (by decide : 0<2) (Nat.mul_le_mul_right h (le_max_right A B)))
  have e : max A B*h+1≤(max A B+1)*h := by rw [Nat.add_mul];omega
  have grow:=Nat.pow_le_pow_right (by decide : 0<2) e
  rw [Nat.pow_succ] at grow
  omega

theorem mul (bx : Bounded x) (by' : Bounded y) : Bounded (fun h i=>x h i*y h i) := by
  obtain ⟨A,ra⟩:=bx
  obtain ⟨B,rb⟩:=by'
  refine ⟨A+B,?_⟩
  filter_upwards [ra,rb] with h ha hb
  intro i
  simpa only [Nat.add_mul,Nat.pow_add] using Nat.mul_le_mul (ha i) (hb i)

theorem pow (bx : Bounded x) (n : ℕ) : Bounded (fun h i=>(x h i)^n) := by
  induction n with
  | zero=>simpa only [Nat.pow_zero] using (const (ι:=ι) 1)
  | succ t ih=>simpa only [Nat.pow_succ] using ih.mul bx

theorem sub (bx : Bounded x) : Bounded (fun h i=>x h i-y h i) :=
  bx.of_le (fun _ _=>Nat.sub_le ..)
theorem div (bx : Bounded x) : Bounded (fun h i=>x h i/y h i) :=
  bx.of_le (fun _ _=>Nat.div_le_self ..)
theorem max' (bx : Bounded x) (by' : Bounded y) : Bounded (fun h i=>max (x h i) (y h i)) :=
  (bx.add by').of_le fun _ _=>max_le (Nat.le_add_right ..) (Nat.le_add_left ..)

theorem padded (bx : Bounded x) : Bounded (fun h i=>2^Nat.clog 2 (x h i)) := by
  apply (mul (const 2) bx |>.add (const 1)).of_le
  intro h i
  let n:=x h i
  change 2^Nat.clog 2 n≤2*n+1
  by_cases lo : n≤1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp lo with z|z <;> rw [z] <;> decide
  · have lower:=Nat.pow_pred_clog_lt_self (by decide : 1<2) (show 1<n by omega)
    have pos:=Nat.clog_pos (by decide : 1<2) (show 1<n by omega)
    cases dep : Nat.clog 2 n with
    | zero=>omega
    | succ k=>rw [dep] at lower;simp only [Nat.pred_succ] at lower;rw [Nat.pow_succ];omega

theorem logPage (bx : Bounded x) : Bounded (fun h i=>2^((x h i).log2+1)) := by
  apply ((bx.add (const 1)).mul (const 2)).of_le
  intro h i
  let n:=x h i
  change 2^(n.log2+1)≤(n+1)*2
  rw [Nat.pow_succ]
  by_cases z : n=0
  · simp [z]
  · exact Nat.mul_le_mul_right _ ((Nat.log2_self_le z).trans (Nat.le_succ _))

theorem pow_of_linear {x : ∀h,ι h→ℕ} {K : ℕ}
    (le : ∀ᶠ h:ℕ in atTop,∀i,x h i≤K*h) : Bounded (fun h i=>2^(x h i)) :=
  ⟨K,le.mono fun _ h i=>Nat.pow_le_pow_right (by decide) (h i)⟩

end Bounded
end Hierarchy.DescentDatedAddressBook

end OAI
