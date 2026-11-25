import OAI.Computability.NearSquareRoot.KernelComputableAddress
import OAI.Computability.NearSquareRoot.InterchangeROMRepairLowerWitness

/-! # Integer sizes of the binary repair tables

The two rounded endpoints of the real interpolation window contribute twice its
radius and one parity bit. This gives the exact source dimensions through
primitive recursive arithmetic, including the size of the coefficient basis.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Sizes

open OAI.LinearAlgebra.FiniteFourier SwapRepair KernelComputableAddress

def sqrtUp (n : ℕ) : ℕ := if n = 0 then 0 else (n-1).sqrt + 1

theorem sqrtUp_eq (n : ℕ) : sqrtUp n = ⌈Real.sqrt (n : ℝ)⌉₊ := by
  cases n with
  | zero => simp [sqrtUp]
  | succ n =>
    simp only [sqrtUp,Nat.succ_ne_zero,ite_false,Nat.add_one_sub_one]
    symm
    apply Nat.ceil_eq_iff (Nat.succ_ne_zero _ ) |>.2
    rw [Nat.add_one_sub_one,Real.lt_sqrt (by positivity),Real.sqrt_le_left (by positivity)]
    constructor
    · exact_mod_cast Nat.sqrt_mul_sqrt_lt_succ' n
    · exact_mod_cast Nat.succ_le_succ_sqrt' n

def windowRadius (m : ℕ) := sqrtUp (2*m*Nat.clog 2 (2*m))
def windowDegree (m : ℕ) := 2*windowRadius m + m%2
def pencilOrder (m : ℕ) := 2 ^ Nat.clog 2 (max 2 (windowDegree m))
def clockDigits (m : ℕ) := (pencilOrder m+1) ^ (m*2)
def rows (m : ℕ) := 2^m * (pencilOrder m)^(clockDigits m)
def checkRows (m : ℕ) := rows m / (2*m^3)
def basisCount (m : ℕ) := 2 ^ (max (Nat.clog 2 (max 2 (windowDegree m))) (Nat.clog 2 (rows m)))

theorem windowRadius_eq (m : ℕ) : windowRadius m = repairWindowRadius 2 m := by
  simp [windowRadius,sqrtUp_eq,repairWindowRadius,repairWindowR]

theorem windowDegree_eq (m : ℕ) : windowDegree m = repairWindowDegree 2 m := by
  rw [windowDegree,windowRadius_eq,repairWindowDegree,repairWindowUpper,repairWindowLower,
    Int.ceil_add_natCast,Int.floor_sub_natCast]
  have mean : repairWindowMean 2 m = (m : ℝ) / 2 := by norm_num [repairWindowMean]
  rw [mean]
  have h₁ : ⌊(m : ℝ) / 2⌋ = ((m/2 : ℕ) : ℤ) := by
    apply Int.floor_eq_iff.mpr
    rw [le_div_iff₀ (by norm_num),div_lt_iff₀ (by norm_num)]
    constructor <;> exact_mod_cast (by omega)
  have h₂ : ⌈(m : ℝ) / 2⌉ = (((m+1)/2 : ℕ) : ℤ) := by
    apply Int.ceil_eq_iff.mpr
    rw [lt_div_iff₀ (by norm_num),div_le_iff₀ (by norm_num)]
    constructor
    · have h : ((m+1)/2 : ℕ)*2 < m+2 := by omega
      rw [Int.cast_natCast]
      have hh : ((((m+1)/2 : ℕ) : ℝ))*2 < (m:ℝ)+2 := by exact_mod_cast h
      linarith
    · exact_mod_cast (by omega)
  rw [h₁,h₂]
  omega

theorem pencilOrder_eq (m : ℕ) : pencilOrder m = order m := by
  simp [pencilOrder,windowDegree_eq,order,countPencilOrder]

theorem clockDigits_eq (m : ℕ) : clockDigits m = clock m := by
  simp [clockDigits,pencilOrder_eq,clock,primeClockDigits]

theorem rows_eq (m : ℕ) : rows m = width m := by
  simp [rows,clockDigits_eq,pencilOrder_eq,width,primePredictorRows,clock]

theorem checkRows_eq (m : ℕ) : checkRows m = checks m := by
  simp [checkRows,rows_eq,checks,countRepairChecks,width,primePredictorRows,clock]

theorem basisCount_eq (m : ℕ) : basisCount m = 2 ^ primeRepairExtensionExponent 2 m := by
  simp [basisCount,primeRepairExtensionExponent,windowDegree_eq,rows_eq,width]

/-- A primitive recursion for the ceiling logarithm increments at powers of two. -/
theorem primrec_clog2 : Primrec (Nat.clog 2) := by
  let step (n k : ℕ) := if 2^k = n then k+1 else k
  have hs : Primrec₂ step := (Primrec.ite
    (Primrec.eq.comp (primrec_pow (Primrec.const 2) Primrec.snd) Primrec.fst)
    (Primrec.nat_add.comp Primrec.snd (Primrec.const 1)) Primrec.snd).to₂
  apply (Primrec.nat_rec₁ 0 hs).of_eq
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [ih,step]
    split_ifs with h
    · have lower := (Nat.clog_lt_clog_succ_iff (by decide : 1 < 2)).2 h
      have upper : Nat.clog 2 (n+1) ≤ Nat.clog 2 n + 1 := by
        apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2
        rw [pow_succ,h]
        have pos : 0 < n := h ▸ Nat.two_pow_pos _
        omega
      omega
    · exact (Nat.clog_eq_clog_succ_iff (by decide : 1 < 2)).2 h

theorem primrec_sqrtUp : Primrec sqrtUp :=
  Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.nat_sqrt.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)))
      (Primrec.const 1))

theorem primrec_windowRadius : Primrec windowRadius :=
  let twice := Primrec.nat_mul.comp (Primrec.const 2) Primrec.id
  primrec_sqrtUp.comp (Primrec.nat_mul.comp twice (primrec_clog2.comp twice))

theorem primrec_windowDegree : Primrec windowDegree :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) primrec_windowRadius)
    (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))

theorem primrec_pencilOrder : Primrec pencilOrder :=
  primrec_pow (Primrec.const 2) (primrec_clog2.comp (Primrec.nat_max.comp (Primrec.const 2) primrec_windowDegree))

theorem primrec_clockDigits : Primrec clockDigits :=
  primrec_pow (Primrec.nat_add.comp primrec_pencilOrder (Primrec.const 1))
    (Primrec.nat_mul.comp Primrec.id (Primrec.const 2))

theorem primrec_rows : Primrec rows :=
  Primrec.nat_mul.comp (primrec_pow (Primrec.const 2) Primrec.id)
    (primrec_pow primrec_pencilOrder primrec_clockDigits)

theorem primrec_checkRows : Primrec checkRows :=
  Primrec.nat_div.comp primrec_rows (Primrec.nat_mul.comp (Primrec.const 2) (primrec_pow Primrec.id (Primrec.const 3)))

theorem primrec_basisCount : Primrec basisCount :=
  primrec_pow (Primrec.const 2) (Primrec.nat_max.comp
    (primrec_clog2.comp (Primrec.nat_max.comp (Primrec.const 2) primrec_windowDegree)) (primrec_clog2.comp primrec_rows))

/-- The packed width scales the check-row charge by exactly the same factor
as the input row count. -/
theorem packed_correction_price (m : ℕ) :
    4 * (checkRows m * basisCount m) * m * m^2 ≤ 2 * (rows m * basisCount m) := by
  rw [checkRows_eq,rows_eq]
  calc 4 * (checks m * basisCount m) * m * m^2 =
        (4 * checks m * m * m^2) * basisCount m := by ring
    _ ≤ (2 * width m) * basisCount m :=
      Nat.mul_le_mul_right _ (correction_swaps_le (m := m))
    _ = 2 * (width m * basisCount m) := by ring

theorem pencil_price {m : ℕ} (hm : 2 ≤ m) :
    4 * (pencilOrder m : ℝ) ≤ 64 * Real.sqrt ((m : ℝ) * Real.log (2*m)) + 16 := by
  rw [pencilOrder_eq]
  exact pencil_stages_le hm

/-- A candidate of computably specified shape exists for every template parameter. -/
theorem exists_accepted {K : Type} [Field K] [DecidableEq K] {m : ℕ} (hm : 2 ≤ m)
    (half : K) (hh : 2 * half = 1) :
    ∃ t : Spec K (Fin (rows m) × Fin (basisCount m)) (Fin (checkRows m) × Fin (basisCount m)) m,
      accepts t (pencilOrder m) half = true := by
  let valid (w s a b : ℕ) := ∃ t : Spec K (Fin w × Fin a) (Fin s × Fin a) m,
    accepts t b half = true
  change valid (rows m) (checkRows m) (basisCount m) (pencilOrder m)
  rw [rows_eq,checkRows_eq,basisCount_eq,pencilOrder_eq]
  exact Lower.exists_accepted hm half hh

end InterchangeROMRepair.Sizes

end NearSquareRoot
end Computability
end OAI
