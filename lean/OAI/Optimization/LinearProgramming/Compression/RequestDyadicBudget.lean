import OAI.Optimization.LinearProgramming.Compression.RequestDyadic
import OAI.Optimization.LinearProgramming.Compression.RequestQueries

/-! A dimension-only bound on every homogeneous grid row physically sent to the
mixed-sign comparator. This includes the powers of two in the RAM midpoint. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open _root_.OAI.Optimization.LinearProgramming.Lattice

private theorem dyadic_source_coordinate {d : ℕ} (z : Fin d → ℤ) (last : Fin d)
    (q K : ℕ) (hK : 0<K) (hz : ∀ i, |z i|≤(K:ℤ)) (W : ℤ) (hW : 0≤W)
    (hm : W≤4*(K:ℤ)*q) (i : Fin (d+1)) :
    let rows := requestDyadicRows z last q (-(K*q:ℤ)) W
    |rows.1 i| + |rows.2 i| ≤ 10*(q:ℤ)*K^2 := by
  have hK1 : (1:ℤ)≤K := by exact_mod_cast hK
  have ht : |2*(-(K*q:ℤ))+W|≤6*(K:ℤ)*q := by
    apply abs_le.mpr
    constructor <;> nlinarith [mul_nonneg (Int.natCast_nonneg K) (Int.natCast_nonneg q)]
  have hlast := mul_le_mul ht (hz last) (abs_nonneg _) (by positivity)
  have hlast' := mul_le_mul hm (hz last) (abs_nonneg _) (by positivity)
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [requestDyadicRows,Fin.snoc_last,abs_mul,abs_neg,abs_abs,abs_of_nonneg hW]
    nlinarith only [hlast,hlast']
  · have hs : |(if 0<z last then (1:ℤ) else -1)|=1 := by split <;> norm_num
    simp only [requestDyadicRows,Fin.snoc_castSucc,abs_mul,hs,mul_one,abs_zero,add_zero]
    simp only [abs_of_nonneg (show (0:ℤ)≤2 by decide),Int.abs_natCast]
    have h1 := mul_le_mul_of_nonneg_left (hz j) (show (0:ℤ)≤2*q by positivity)
    have h2 := mul_nonneg (show (0:ℤ)≤(q:ℤ)*K by positivity) (sub_nonneg.mpr hK1)
    nlinarith only [h1,h2,show 0≤(q:ℤ)*K by positivity]

theorem requestDyadic_query_l1 {d : ℕ} (w : Fin d → ℚ) (z : Fin d → ℤ) (last : Fin d)
    (hshort : ‖requestGraph w z‖ ≤ requestCutoff d) (p : ℕ)
    (oracle : (Fin (d+1) → ℤ) → Bool) :
    let K := requestCutoff d
    let q := 2^p
    let depth := (2*K*q).log2+1
    let width := (2:ℤ)^depth
    let rows := requestDyadicRows z last q (-(K*q:ℤ)) width
    ∀ j < depth, (∑ i : Fin (d+1), |dyadicQuery rows.1 rows.2 j
      (dyadicSearch oracle rows.1 rows.2 j).numerator i|) ≤ (2:ℤ)^(2*p+8*d+30) := by
  intro K q depth width rows j hj
  have hK : 0<K := by dsimp [K,requestCutoff]; positivity
  have hq : 0<q := by dsimp [q]; positivity
  have hwidthN : 2^depth ≤ 4*K*q := by
    have hpow := Nat.log2_self_le (n:=2*K*q) (by positivity)
    dsimp [depth]; rw [pow_succ]
    nlinarith only [hpow]
  have hW : width ≤ 4*(K:ℤ)*q := by
    dsimp only [width]
    exact_mod_cast hwidthN
  have hW0 : 0≤width := by dsimp [width]; positivity
  have hz (i : Fin d) : |z i|≤(K:ℤ) := by exact_mod_cast (requestGraph_coords_le hshort).1 i
  have bound (i : Fin (d+1)) : |dyadicQuery rows.1 rows.2 j
      (dyadicSearch oracle rows.1 rows.2 j).numerator i| ≤ 40*(q:ℤ)^2*K^3 := by
    have h1 := dyadicQuery_coeff_le rows.1 rows.2 j _
      (dyadicSearch_numerator_lt oracle rows.1 rows.2 j).le i
    have h2 := dyadic_source_coordinate z last q K hK hz width hW0 hW i
    have hjW : (2:ℤ)^j≤width := pow_le_pow_right₀ (by decide) hj.le
    calc
      _ ≤ (2:ℤ)^j*(|rows.1 i|+|rows.2 i|) := h1
      _ ≤ (4*(K:ℤ)*q)*(10*(q:ℤ)*K^2) := mul_le_mul (hjW.trans hW) h2
        (add_nonneg (abs_nonneg _) (abs_nonneg _)) (by positivity)
      _ = _ := by ring
  have hdN : d+1≤K := by
    have h := Nat.le_mul_of_pos_left (d+3) (show 0<2^(d+2) by positivity)
    dsimp [K,requestCutoff]; omega
  have hd : ((d+1:ℕ):ℤ) ≤ K := by exact_mod_cast hdN
  have hcap : 4*(q:ℤ)*K^2 ≤ (2:ℤ)^(p+4*d+12) := by exact_mod_cast requestGridArgs_bit_cap d p
  have hpow := pow_le_pow_left₀ (by positivity : (0:ℤ)≤4*(q:ℤ)*K^2) hcap 2
  calc
    _ ≤ ∑ _ : Fin (d+1), 40*(q:ℤ)^2*K^3 := Finset.sum_le_sum (fun i _ => bound i)
    _ = ((d+1:ℕ):ℤ)*(40*(q:ℤ)^2*K^3) := by simp
    _ ≤ (K:ℤ)*(40*(q:ℤ)^2*K^3) := mul_le_mul_of_nonneg_right hd (by positivity)
    _ ≤ 4*(4*(q:ℤ)*K^2)^2 := by nlinarith only [sq_nonneg ((q:ℤ)*K^2)]
    _ ≤ 4*((2:ℤ)^(p+4*d+12))^2 := by gcongr
    _ = (2:ℤ)^(2+(p+4*d+12)*2) := by
      rw [pow_add (2:ℤ) 2 ((p+4*d+12)*2),pow_mul (2:ℤ) (p+4*d+12) 2];norm_num
    _ ≤ (2:ℤ)^(2*p+8*d+30) := pow_le_pow_right₀ (by decide) (by omega)

end Compression
end LinearProgramming
end Optimization
end OAI
