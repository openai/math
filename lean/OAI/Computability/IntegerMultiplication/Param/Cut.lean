import OAI.Computability.IntegerMultiplication.Param.Saves

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Param
open Filter

-- K contour
def giant:ℕ := 2^90
theorem giantp : 0<giant := pow_pos (by decide) _
def level n := height n / giant
def chunk n := (2:ℕ)^level n
def batches n := span_ n/chunk n - 1
def border n := chunk n + span_ n%chunk n
def scouts n := lanes n-2
def facing n := scouts n*span_ n
def faces n := facing n/chunk n
def trace_ n := facing n%chunk n

theorem level_le (n) : level n ≤ height n := Nat.div_le_self _ _
theorem chunk_l (n) :
    chunk n ≤ lanes n := Nat.pow_le_pow_right (by decide) (level_le n)
theorem chunk_pos (n) : 0 < chunk n := pow_pos (by decide) _
theorem level_grow : Tendsto level atTop atTop := by
  refine tendsto_atTop.2 fun b=>?_
  filter_upwards [height_grows.eventually (eventually_ge_atTop (b*giant))] with n h
  exact (Nat.le_div_iff_mul_le giantp).2 h

theorem batch :
    Large fun n=> chunk n ≤ span_ n ∧ batches n*chunk n +border n = span_ n := by
  filter_upwards [span_large] with n h
  have t : chunk n ≤span_ n := (chunk_l n).trans
    ((by exact Nat.le_self_pow (by decide) _ : lanes n ≤ lanes n^30).trans h)
  refine ⟨t,?_⟩
  let K := chunk n
  let x := span_ n
  have e : 1*K ≤ x := by simpa [K,x]
  have a : 1≤ x/K := (Nat.le_div_iff_mul_le (chunk_pos n)).2 e
  have b : x/K-1+1=x/K := by omega
  change (x/K-1)*K+(K+x%K)=x
  have v := Nat.div_add_mod x K
  rw [mul_comm K] at v
  calc
    _ = (x/K-1+1)*K+x%K := by ring
    _ = _ := b ▸ v

theorem border_v (n) :
    chunk n ≤ border n ∧ border n ≤ 2*chunk n := by
  have h:= Nat.mod_lt (span_ n) (chunk_pos n)
  unfold border
  omega

theorem facing_pos :
    Large fun n=> ∀ m,chunk n ≤ m → m ≤ facing n → chunk n ≤ facing n := by
  apply Filter.Eventually.of_forall
  intro _ _ a b; omega -- unused
theorem faces_hold :
    Large fun n=> 1≤ faces n ∧ 1≤scouts n := by
  filter_upwards [batch,dim_grows.eventually (eventually_ge_atTop 3)] with n h v
  have s : 1≤scouts n := by unfold scouts; omega
  refine ⟨(Nat.le_div_iff_mul_le (chunk_pos n)).2 (by unfold facing; nlinarith [Nat.mul_le_mul_right (span_ n) s]),s⟩

theorem faces_shape (n) :
    faces n*chunk n + trace_ n = facing n ∧ trace_ n ≤ chunk n := by
  unfold faces trace_
  rw [mul_comm]
  exact ⟨Nat.div_add_mod _ _,(Nat.mod_lt _ (chunk_pos _)).le⟩

theorem face_margin (n) : faces n ≤ facing n ∧ facing n ≤ budget n :=
  ⟨Nat.div_le_self _ _,le_trans (Nat.mul_le_mul_right _ (show scouts n ≤ lanes n from Nat.sub_le _ _)) (wall_small n)⟩

/-- Packed-selector sparsity denominators dwarf any budget polynomial. -/
theorem contour (c k : ℕ) :
    Large fun n=> c*(budget n+1)^k ≤ 2^chunk n := by
  filter_upwards [budget_grows.eventually (eventually_ge_atTop (c*2^k)),
    level_grow.eventually (eventually_ge_atTop (1:ℕ)),
    level_grow.eventually (beats (2*giant*32*(k+1)) 1)] with n h v b
  have w := budget_p n
  have x : c*(budget n+1)^k ≤ budget n^(k+1) := by
    have p := Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega : budget n+1 ≤ 2*budget n) k)
    rw [mul_pow] at p
    rw [pow_succ]
    nlinarith [Nat.mul_le_mul_right (budget n^k) h]
  refine x.trans ?_
  rw [budget_shape,← pow_mul]
  apply Nat.pow_le_pow_right (by decide)
  rw [pow_one] at b
  change _ ≤ chunk n at b
  refine le_trans ?_ b
  have t : height n ≤ 2*giant*level n := by
    let a:= level n
    have f : height n%giant< giant := Nat.mod_lt _ giantp
    have e : height n%giant+giant*a=height n := Nat.mod_add_div _ _
    change _ ≤ _*a
    have s : giant≤giant*a := Nat.le_mul_of_pos_right giant v
    rw [Nat.mul_assoc]
    omega -- omega nonlinear giant treated constant?
  nlinarith [Nat.mul_le_mul_right (32*(k+1)) t]

theorem safe :
    Large fun n=> ∀ a K, a≤budget n → chunk n≤K → K≤2*chunk n →
      (3*(a*K)+1)*(32*(a-1)) ≤ 2^K := by
  filter_upwards [contour 1024 4] with n h a K g v w
  refine le_trans ?_ (h.trans (Nat.pow_le_pow_right (by decide) v))
  let d := budget n+1
  have p : a≤d := by unfold d; omega
  have q : 1≤d := by unfold d; omega
  have s : chunk n ≤ d := le_trans ((chunk_l n).trans (Nat.le_self_pow (by decide) _ :
    lanes n≤budget n)) (Nat.le_succ _)
  have t : 3*(a*K)+1 ≤ 7*d^2 := by
    have z := Nat.mul_le_mul p (by omega : K≤2*d)
    nlinarith
  have T : 32*(a-1) ≤ 32*d := by omega
  change _ ≤ 1024*d^4
  calc
    _ ≤ (7*d^2)*(32*d) := Nat.mul_le_mul t T
    _ = 224*d^3 := by ring
    _ ≤ _ := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_right q (by decide))

noncomputable def tiny:ℝ := 1/(giant:ℕ)
theorem tinyRange : 0<tiny ∧ tiny ≤1/2 := by
  unfold tiny giant; norm_num

theorem chunkCost (n):
    (chunk n:ℝ) ≤ (lanes n:ℝ) ^ tiny := by
  have h : (level n:ℝ)*giant ≤ height n := by
    exact_mod_cast (Nat.div_mul_le_self (height n) giant)
  have r : 0 < (giant:ℝ) := by exact_mod_cast giantp
  unfold lanes chunk tiny
  push_cast
  rw [← Real.rpow_natCast,← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  rw [← div_eq_mul_one_div]
  exact (le_div_iff₀ r).mpr h

end Param

end IntegerMultiplication
end Computability
end OAI
