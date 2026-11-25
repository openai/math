import OAI.Computability.IntegerMultiplication.Garden.Air
import OAI.Computability.IntegerMultiplication.Fourier.RestoreTable
import Mathlib.Data.Nat.Choose.Bounds

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Garden
open Brief Staff Strip Code Carry IntegerMultiplication.Fourier Finset
-- exact integer scale implementation. assumptions denominators positive.
noncomputable section
def jewel (D:ℕ) (i:ℤ) : ℕ :=
  if D<(i.natAbs) then 0 else Nat.choose (2*D) (unoff D i)
theorem jewel_le (D i): jewel D i ≤ 2^(2*D) := by unfold jewel; split; exact Nat.zero_le _; exact Nat.choose_le_two_pow ..
theorem jewel_pos (D i) (v:i.natAbs ≤ D):
    0 < jewel D i := by
  unfold jewel
  rw [ite_eq_right (Nat.not_lt.mpr v)]
  apply Nat.choose_pos
  unfold unoff; omega
theorem jewel_coins (D:ℕ) (i:ℤ) :
    Fourier.coef D i=(jewel D i:ℕ)/(4:ℝ)^D := by
  unfold coef jewel
  split
  · next h=>
    have p : i.natAbs≤D := by simp only [mem_rad] at h; omega
    rw [ite_eq_right (Nat.not_lt.mpr p)]
  · next h=>
    have p : D < i.natAbs := by simp only [mem_rad] at h; omega
    simp [p]

variable {s:ℕ} (t D:ℕ) [NeZero s]
abbrev value_ (i:Spot s) := jewel D (delta s t i)
def blocks : ℤ := ∏ i:Spot s, (value_ t D i:ℤ)
def left (i:Spot s) : ℤ := ∏ j:Spot s,if j=i then 1 else (value_ t D j:ℤ)
omit [NeZero s] in
theorem leftr (i:Spot s) :
    value_ t D i * left t D i = blocks (s:=s) t D := by
  let V j:ℤ:=value_ t D (j:Spot s)
  let W j:ℤ:=if j=i then V i else 1
  let L j:ℤ:=if j=i then 1 else V j
  have e (j:Spot s): V j=W j*L j := by unfold W L; split <;> simp_all
  unfold blocks left
  change V i* (∏ j,L j)=∏ j,V j
  calc
    V i*(∏ j,L j)= (∏ j:Spot s,W j)*∏ j,L j := by simp [W]
    _ = ∏ j:Spot s,W j*L j := (Finset.prod_mul_distrib).symm
    _ = _ := by simp only [← e]

def baseline (s:ℕ):ℤ := t*blocks (s:=s) t D
def begins (i j:Spot s):ℤ :=
  if i=j then 4^D*left t D i else 0
def bends_ (i : Spot s) (a:ℤ):ℤ :=
  (t:ℕ)*(left t D i : ℤ)*(jewel D (delta s t i - t*a):ℤ)
def curves (l:ℕ) (i j : Spot s):ℤ :=
  ∑ a∈nhood l, if wrap s (rep i+a)=j then bends_ t D i a else 0

def herb (l:ℕ) (j:Spot s) : Scene s where
  ray i:=begins t D i j*baseline t D s -- check order
  end_:=baseline t D s
  square i k:= -(curves t D l i k)
def first (j:Spot s):Notes s :=
  (fun i=> begins t D i j,1)
def canon (l k:ℕ) (j:Spot s) :=
  (act (herb t D l j))^[k] (first t D j)

theorem curves_apply (l) (i:Spot s) (f:Spot s→ℤ) :
    ∑ j:Spot s, curves t D l i j * f j =
    ∑ a∈nhood l,bends_ t D i a*f (wrap s (rep i+a)) := by
  unfold curves; simp_rw [sum_mul]
  rw [sum_comm]
  simp

variable (v:∀ i:Spot s,(delta s t i).natAbs ≤D)
include v
omit [NeZero s] v in
theorem beginCast (i j:Spot s) :
    ((begins t D i j):ℝ)=(4:ℝ)^D*(left t D i:ℝ)*(if i=j then 1 else 0) := by
  unfold begins; split <;> simp
omit [NeZero s] in
theorem begins_eq (ht:0<t) (i j:Spot s):
    ((begins t D i j):ℝ)=(baseline t D s:ℝ)*start s t D i j := by
  rw [beginCast t D]; unfold start; split
  · unfold factor; rw [jewel_coins]; simp only [mul_one]
    unfold baseline; rw [Int.cast_mul,Int.cast_natCast,← leftr t D i,Int.cast_mul,Int.cast_natCast]
    have w:(t:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ht
    have p : (value_ t D i:ℝ) ≠0 := by exact_mod_cast Nat.ne_of_gt (jewel_pos _ _ (v i))
    change (4:ℝ)^D*(left t D i:ℝ)=(t:ℝ)*((value_ t D i:ℝ)* (left t D i:ℝ))*(1/((t:ℝ)*((value_ t D i:ℝ)/4^D)))
    field
  · simp

omit [NeZero s] in
theorem bendsCast (i:Spot s) (a:ℤ):
    ((bends_ t D i a):ℝ)=(baseline t D s:ℝ)*ratio t D (delta s t i) a := by
  unfold ratio baseline bends_
  rw [jewel_coins,jewel_coins,← leftr t D i]
  push_cast
  have p : (value_ t D i:ℝ) ≠0 := by exact_mod_cast Nat.ne_of_gt (jewel_pos _ _ (v i))
  unfold value_ at *
  field

theorem canon_results (ht:0<t) l k (j:Spot s):
    (canon t D l k j).2=baseline t D s ^ k ∧
    ∀ i:Spot s, ((canon t D l k j).1 i:ℝ) = (baseline t D s :ℝ)^(k+1)*mixTable t D (nhood l) k i j := by
  induction k with
  | zero=> exact ⟨by simp [canon,first],fun i=> by simpa [canon,first,mixTable] using begins_eq t D v ht i j⟩
  | succ k ih=>
    have eq : canon t D l (k+1) j = act (herb t D l j) (canon t D l k j) := by rw [canon,Function.iterate_succ_apply']; rfl
    rw [eq]
    refine ⟨by rw [act,herb,ih.1,pow_succ'],fun i=>?_⟩
    unfold act herb; dsimp only
    simp only [neg_mul,Finset.sum_neg_distrib,curves_apply]
    rw [ih.1,Int.cast_add,Int.cast_mul,Int.cast_mul,begins_eq t D v ht]
    push_cast
    rw [mixTable]
    simp_rw [ih.2,bendsCast t D v,mul_sub]
    let u:= (baseline t D s:ℝ)
    have W: ∀ a:ℤ,u*ratio t D (delta s t i) a*
        (u^(k+1)*mixTable t D (nhood l) k (wrap s (rep i+a)) j)=
        u^(k+1+1)*(ratio t D (delta s t i) a*mixTable t D (nhood l) k (wrap s (rep i+a)) j) := fun a=> by ring
    dsimp [u] at W
    simp_rw [W,← Finset.mul_sum]
    ring

end
end Garden

end IntegerMultiplication
end Computability
end OAI
