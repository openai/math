import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Find
import Lean.Elab.Tactic.Omega

namespace OAI
/-! # Number of Leighton sorting lifts for a requested key height -/

namespace Hierarchy.DescentSortLiftHeight

/-- One installed lift allows one more quarter of the preceding key height. -/
def height (b : ℕ) : ℕ→ℕ
  | 0 => b
  | n+1 => height b n + height b n / 4

theorem step (b n : ℕ) : height b n≤height b (n+1) := Nat.le_add_right ..

theorem base_le (b : ℕ) (n : ℕ) : b≤height b n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact ih.trans (step b n)

theorem height_add (b m n : ℕ) : height b (m+n)=height (height b m) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change height b (m+n)+height b (m+n)/4=height (height b m) n+height (height b m) n/4
    rw [ih]

theorem threefold {b : ℕ} (low : 4≤b) : 3*b≤height b 7 := by
  by_cases big : 7≤b
  · have growth (j : ℕ) : 5*height b j≤4*height b (j+1)+3 := by
      simp only [height]
      omega
    have a := growth 0
    have c := growth 1
    have d := growth 2
    have e := growth 3
    have f := growth 4
    have g := growth 5
    have h := growth 6
    change 5*b ≤ 4*height b 1+3 at a
    change 5*height b 1≤4*height b 2+3 at c
    change 5*height b 2≤4*height b 3+3 at d
    change 5*height b 3≤4*height b 4+3 at e
    change 5*height b 4≤4*height b 5+3 at f
    change 5*height b 5≤4*height b 6+3 at g
    change 5*height b 6≤4*height b 7+3 at h
    omega
  · have cases : b=4 ∨ b=5 ∨ b=6 := by omega
    rcases cases with rfl|rfl|rfl <;> decide

/-- Once a target is reached, subsequent padding stages stay at the target. -/
def truncated (b t i : ℕ) := min t (height b i)

theorem truncated_start {b t : ℕ} (start : b≤t) : truncated b t 0=b := Nat.min_eq_right start

theorem truncated_step (b t i : ℕ) :
    truncated b t (i+1)=min t (truncated b t i+truncated b t i/4) := by
  unfold truncated
  simp only [height]
  omega

theorem truncated_end {b t : ℕ} (low : 4≤b) (target : t≤3*b) : truncated b t 7=t :=
  Nat.min_eq_left (target.trans (threefold low))

private theorem reach {b t : ℕ} (low : 4≤b) (target : t≤3*b) : ∃i,t≤height b i :=
  ⟨7,target.trans (threefold low)⟩

/-- Ending on the first crossing removes all repeated padding stages. -/
def first {b t : ℕ} (low : 4≤b) (target : t≤3*b) := Nat.find (reach low target)

theorem first_le {b t : ℕ} (low : 4≤b) (target : t≤3*b) : first low target≤7 :=
  Nat.find_min' (reach low target) (target.trans (threefold low))

theorem first_end {b t : ℕ} (low : 4≤b) (target : t≤3*b) :
    truncated b t (first low target)=t := Nat.min_eq_left (Nat.find_spec (reach low target))

theorem before_first {b t i : ℕ} (low : 4≤b) (target : t≤3*b) (before : i<first low target) :
    truncated b t i<truncated b t (i+1) := by
  have early : ¬t≤height b i := Nat.find_min (reach low target) before
  have prev := low.trans (base_le b i)
  unfold truncated
  simp only [height]
  omega

theorem many {b : ℕ} (low : 4≤b) (m : ℕ) : 2^m*b≤height b (8*m) := by
  induction m with
  | zero => simp [height]
  | succ m ih =>
    have ample := threefold (low.trans (base_le b (8*m)))
    have extra : height (height b (8*m)) 7≤height (height b (8*m)) 8 := step _ 7
    rw [Nat.mul_succ,height_add,Nat.pow_succ,Nat.mul_assoc,Nat.mul_comm 2 b,←Nat.mul_assoc]
    omega

/-- The same bound applies if a concrete lift implements a larger height. -/
theorem dominated (b : ℕ) (actual : ℕ→ℕ) (start : b≤actual 0)
    (grow : ∀n,actual n+actual n/4≤actual (n+1)) (n : ℕ) : height b n≤actual n := by
  induction n with
  | zero => exact start
  | succ n ih => exact (Nat.add_le_add ih (Nat.div_le_div_right ih)).trans (grow n)

def batches (b d : ℕ) := Nat.log 2 (1+d/b)+1

theorem covers {b : ℕ} (low : 4≤b) (d : ℕ) : d≤height b (8*batches b d) := by
  have p := Nat.lt_pow_succ_log_self (by decide : 1<2) (1+d/b)
  have hit : d/b<2^batches b d := by dsimp [batches]; omega
  exact (Nat.le_of_lt ((Nat.div_lt_iff_lt_mul (by omega : 0<b)).mp hit)).trans (many low _)

/-- The finite work and depth multipliers after all lifts are polynomial in
the ratio of requested height to the original key height. -/
theorem costs (b d : ℕ) :
    4^(8*batches b d)≤(2*(1+d/b))^16 ∧
    8^(8*batches b d)≤(2*(1+d/b))^24 := by
  let m := batches b d
  have small : 2^m≤2*(1+d/b) := by
    dsimp [m,batches]
    rw [Nat.pow_succ,Nat.mul_comm 2 (1+d/b)]
    have nonzero : 1+d/b≠0 := by
      rw [Nat.add_comm]
      exact Nat.succ_ne_zero _
    exact Nat.mul_le_mul_right 2 (Nat.pow_log_le_self 2 nonzero)
  have powers (a : ℕ) : (2^a)^(8*m)=(2^m)^(8*a) := by
    rw [←Nat.pow_mul,←Nat.pow_mul]
    rw [Nat.mul_comm 8 a,Nat.mul_comm m (a*8),Nat.mul_assoc]
  exact ⟨(powers 2).le.trans (Nat.pow_le_pow_left small _),(powers 3).le.trans (Nat.pow_le_pow_left small _)⟩

/-- Radix, stripe length and half-block for one strictly advancing
truncated lift. The routing square fits inside either physical half-block. -/
theorem oneStepGeometry {b e : ℕ} (hb : 4≤b) (lo : b<e) (hi : e≤b+b/4) :
    ∃ k p B : ℕ,0<k ∧ 0<B ∧ 2^e=k*(k*p) ∧ k*p=2^b ∧
      k*p=B+B ∧ B=2^(b-1) ∧ k*k≤B := by
  let a := e-b
  have ab : a≤b := by dsimp [a]; omega
  have fit : a+a≤b-1 := by dsimp [a]; omega
  have sum : a+(b-a)=b := by omega
  have fields : 2^a*2^(b-a)=2^b := by rw [←Nat.pow_add,sum]
  have halves : 2^b=2^(b-1)+2^(b-1) := by
    conv_lhs => rw [show b=(b-1)+1 by omega,Nat.pow_succ]
    omega
  refine ⟨2^a,2^(b-a),2^(b-1),Nat.two_pow_pos _,Nat.two_pow_pos _,?_,fields,fields.trans halves,rfl,?_⟩
  · rw [fields,←Nat.pow_add]
    congr 1
    dsimp [a]
    omega
  · rw [←Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) fit

/-- Padded item width, never below one whole original block. -/
def pad (b l : ℕ) := max b (Nat.clog 2 l)

theorem pad_volume (b l : ℕ) :
    b≤pad b l ∧ l≤2^(pad b l) ∧
    2^(pad b l)≤2*(l+2^b) ∧ 2^(pad b l-b)≤1+2*((l+2^b-1)/2^b) := by
  have two : 1<2 := by decide
  have Hpos := Nat.two_pow_pos b
  have base : b≤pad b l := le_max_left ..
  have length : l≤2^(pad b l) := (Nat.le_pow_clog two l).trans (Nat.pow_le_pow_right (by decide) (le_max_right ..))
  refine ⟨base,length,?_⟩
  by_cases old : Nat.clog 2 l≤b
  · rw [pad,max_eq_left old,Nat.sub_self,Nat.pow_zero]
    omega
  · have wide : b<Nat.clog 2 l := by omega
    have positive : 0<Nat.clog 2 l := by omega
    let j := (Nat.clog 2 l)-1
    have next : Nat.clog 2 l=j+1 := by dsimp [j]; omega
    have just := (Nat.lt_clog_iff_pow_lt two).1 (show j<Nat.clog 2 l by omega)
    have paid : 2^(pad b l)≤2*l := by
      rw [pad,max_eq_right wide.le,next,Nat.pow_succ]
      omega
    have factor : 2^(pad b l-b)*2^b=2^(pad b l) := by
      rw [←Nat.pow_add,Nat.sub_add_cancel base]
    let m := (l+2^b-1)/2^b
    have carries : l≤m*2^b := by
      have recn := Nat.mod_add_div (l+2^b-1) (2^b)
      have remainder := Nat.mod_lt (l+2^b-1) Hpos
      dsimp [m]
      rw [Nat.mul_comm ((l+2^b-1)/2^b)]
      omega
    have cap : 2^(pad b l-b)≤2*m := by
      apply Nat.le_of_mul_le_mul_right _ Hpos
      rw [factor,Nat.mul_assoc]
      exact paid.trans (Nat.mul_le_mul_left 2 carries)
    exact ⟨by omega,by change 2^(pad b l-b)≤1+2*m; omega⟩

theorem pad_cube_le {b l : ℕ} (fits : l≤(2^b)^3) : pad b l≤3*b := by
  apply max_le (by omega)
  apply (Nat.clog_le_iff_le_pow (by decide : 1<2)).2
  rw [Nat.mul_comm 3 b,Nat.pow_mul]
  exact fits

theorem pad_bounds (b l : ℕ) (fits : l≤(2^b)^2) :
    b≤pad b l ∧ pad b l≤2*b ∧ l≤2^(pad b l) ∧
    2^(pad b l)≤2*(l+2^b) ∧ 2^(pad b l-b)≤1+2*((l+2^b-1)/2^b) := by
  have volume := pad_volume b l
  refine ⟨volume.1,max_le (by omega) ?_,volume.2⟩
  apply (Nat.clog_le_iff_le_pow (by decide : 1<2)).2
  rw [Nat.mul_comm 2 b,Nat.pow_mul]
  exact fits

end Hierarchy.DescentSortLiftHeight

end OAI
