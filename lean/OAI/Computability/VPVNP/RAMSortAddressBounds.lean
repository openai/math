import OAI.Computability.VPVNP.RAMSortCostLayout

/-!
# Intermediate register widths for sort addresses

The addresses in Lemma 10.1 are computed by a bounded number of word operations.
For that interpretation the intermediate products in the triangular layer number
also have to fit. We bound the largest register value in each address expression,
including its inputs, by a fixed polynomial in the array length and the word width.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMSort

/-- The largest value appearing at any node in the straight-line evaluation. -/
def IndexExpr.peak (e : IndexExpr) : ℕ :=
  match e with
  | .arg x => x
  | .add a b | .sub a b | .mul a b | .div a b | .mod a b | .xor a b | .shl a b | .shr a b =>
    max e.eval (max a.peak b.peak)

theorem IndexExpr.eval_le_peak (e : IndexExpr) : e.eval ≤ e.peak := by
  cases e <;> simp [IndexExpr.peak, IndexExpr.eval]

/-- Register semantics: the output of each elementary operation is reduced modulo
`2^bits` as soon as it is written. -/
def IndexExpr.evalWord (bits : ℕ) : IndexExpr → Fin (2 ^ bits)
  | .arg x => Fin.ofNat _ x
  | .add a b => Fin.ofNat _ ((a.evalWord bits).val + (b.evalWord bits).val)
  | .sub a b => Fin.ofNat _ ((a.evalWord bits).val - (b.evalWord bits).val)
  | .mul a b => Fin.ofNat _ ((a.evalWord bits).val * (b.evalWord bits).val)
  | .div a b => Fin.ofNat _ ((a.evalWord bits).val / (b.evalWord bits).val)
  | .mod a b => Fin.ofNat _ ((a.evalWord bits).val % (b.evalWord bits).val)
  | .xor a b => Fin.ofNat _ ((a.evalWord bits).val ^^^ (b.evalWord bits).val)
  | .shl a b => Fin.ofNat _ ((a.evalWord bits).val <<< (b.evalWord bits).val)
  | .shr a b => Fin.ofNat _ ((a.evalWord bits).val >>> (b.evalWord bits).val)

/-- A word evaluator recovers the exact address if all intermediate registers fit. -/
theorem IndexExpr.evalWord_eq {bits : ℕ} (e : IndexExpr) (h : e.peak < 2 ^ bits) :
    (e.evalWord bits).val = e.eval := by
  induction e <;> simp_all [IndexExpr.peak, IndexExpr.evalWord, IndexExpr.eval, max_lt_iff,
    Fin.ofNat, Nat.mod_eq_of_lt]

/-- A uniform bound for all register values in the sort address calculations. -/
def addressEnvelope (h d w : ℕ) : ℕ := 64 * (2 ^ (h+d) + w + 32) ^ 4

/-- Global index, XOR partner and direction test. The shift arguments and the mask
itself are included, even when the output direction bit is zero. -/
theorem wireAddress_peak_le {h d w site off a j : ℕ} (hs : site < 2 ^ d) (ho : off < 2 ^ h)
    (hj : j < a) (ha : a ≤ h + d) :
    (wireIndex h site off).peak ≤ addressEnvelope h d w ∧
    (wirePartner h site off j).peak ≤ addressEnvelope h d w ∧
    (directionBit h site off a).peak ≤ addressEnvelope h d w := by
  let n := 2 ^ (h+d) + w + 32
  have hn : 2 ≤ n := (by decide : 2 ≤ 32).trans (Nat.le_add_left ..)
  have hn4 : n ≤ n ^ 4 := by
    simpa using (Nat.pow_le_pow_right (by omega : 0 < n) (by decide : 1 ≤ 4))
  have hhd : h + d < 2 ^ (h+d) := Nat.lt_two_pow_self
  have h2h : 2 ^ h ≤ 2 ^ (h+d) := Nat.pow_le_pow_right (by decide) (by omega)
  have h2d : 2 ^ d ≤ 2 ^ (h+d) := Nat.pow_le_pow_right (by decide) (by omega)
  have h2j : 2 ^ j < 2 ^ (h+d) := Nat.pow_lt_pow_right (by decide) (hj.trans_le ha)
  have hi : site * 2 ^ h + off < 2 ^ (h+d) := by
    calc
      site * 2 ^ h + off < site * 2 ^ h + 2 ^ h := Nat.add_lt_add_left ho _
      _ = (site + 1) * 2 ^ h := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ 2 ^ d * 2 ^ h := Nat.mul_le_mul_right _ hs
      _ = 2 ^ (h+d) := by rw [Nat.pow_add, Nat.mul_comm]
  have hx := Nat.xor_lt_two_pow hi h2j
  have hquot := Nat.div_le_self (site * 2 ^ h + off) (2 ^ a)
  have hmod := Nat.mod_lt ((site * 2 ^ h + off) / 2 ^ a) (by decide : 0 < 2)
  have harray : 2 ^ (h+d) ≤ n := by dsimp [n]; omega
  change _ ≤ 64 * n ^ 4 ∧ _ ≤ 64 * n ^ 4 ∧ _ ≤ 64 * n ^ 4
  simp only [wireIndex, wirePartner, directionBit, IndexExpr.peak, IndexExpr.eval,
    Nat.shiftLeft_eq, Nat.one_mul, Nat.shiftRight_eq_div_pow, max_le_iff]
  exact ⟨by repeat' constructor <;> omega, by repeat' constructor <;> omega,
    by repeat' constructor <;> omega⟩

/-- Computing the physical address of an individual bit adds its in-record offset
only after computing the start address. -/
def fieldAddress (h w a j dir off bit : ℕ) : IndexExpr :=
  .add (fieldStart h w a j dir off) (.arg bit)

/-- The maximum register value includes the product before division by two in the
triangular ordinal and the product of the field number and the field width. -/
theorem fieldAddress_peak_le {h d w a j dir off bit : ℕ} (ha : a ≤ h + d) (hj : j < a)
    (hd : dir < 2) (ho : off < 2 ^ h) (hb : bit < 5 * w) :
    (fieldAddress h w a j dir off bit).peak ≤ addressEnvelope h d w := by
  let n := 2 ^ (h+d) + w + 32
  let p := a - h - 1
  let step := a - j - 1
  let ord := p * (p+1) / 2 + step
  let width := 2 ^ h * 5 * w
  have hn : 32 ≤ n := Nat.le_add_left ..
  have hn2 : n ≤ n ^ 2 := by
    simpa using (Nat.pow_le_pow_right (by omega : 0 < n) (by decide : 1 ≤ 2))
  have hn4 : n ^ 2 ≤ n ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
  have hhd : h+d < 2 ^ (h+d) := Nat.lt_two_pow_self
  have harray : 2 ^ (h+d) ≤ n := by dsimp [n]; omega
  have hword : w ≤ n := by dsimp [n]; omega
  have hwidth : 2 ^ h ≤ n := (Nat.pow_le_pow_right (by decide) (by omega : h ≤ h+d)).trans harray
  have hp : p + 1 ≤ n := by dsimp [p]; omega
  have hstep : step ≤ n := by dsimp [step]; omega
  have hprod : p * (p + 1) ≤ n ^ 2 := by
    rw [pow_two]; exact Nat.mul_le_mul (by omega) hp
  have hdiv := Nat.div_le_self (p * (p + 1)) 2
  have hord : ord ≤ 2 * n ^ 2 := by dsimp [ord]; omega
  have hfield : ord * 2 + dir ≤ 5 * n ^ 2 := by omega
  have hblock (k : ℕ) (hk : k ≤ n) : k * 5 * w ≤ 5 * n ^ 2 := by
    rw [pow_two, Nat.mul_comm k 5, Nat.mul_assoc]
    exact Nat.mul_le_mul_left 5 (Nat.mul_le_mul hk hword)
  have hspan : width ≤ 5 * n ^ 2 := hblock _ hwidth
  have hoff := hblock _ (ho.le.trans hwidth)
  have haddr : (ord * 2 + dir) * width ≤ 25 * n ^ 4 := by
    calc
      _ ≤ (5 * n ^ 2) * (5 * n ^ 2) := Nat.mul_le_mul hfield hspan
      _ = _ := by ring
  change _ ≤ 64 * n ^ 4
  simp only [fieldAddress, fieldStart, IndexExpr.peak, IndexExpr.eval, max_le_iff, Nat.shiftLeft_eq,
    Nat.one_mul]
  dsimp only [p, step, ord, width] at hp hstep hprod hdiv hord hfield hspan haddr
  repeat' constructor <;> omega

theorem fieldStart_peak_le {h d w a j dir off : ℕ} (ha : a ≤ h+d) (hj : j < a)
    (hd : dir < 2) (ho : off < 2 ^ h) (hw : 0 < w) :
    (fieldStart h w a j dir off).peak ≤ addressEnvelope h d w := by
  have hb := fieldAddress_peak_le ha hj hd ho (by omega : 0 < 5 * w)
  simp only [fieldAddress, IndexExpr.peak, max_le_iff] at hb
  exact hb.2.1

/-- For Section 9's choice `w = (r+10)^4`, all the sorting registers fit as soon
as the logarithm of the array length is at most `(r+10)^2`. In particular, for
`h+d ≤ C*r` this holds for every `r ≥ C`. -/
theorem addressEnvelope_lt_paperWord {h d r : ℕ} (hd : h+d ≤ (r+10)^2) :
    addressEnvelope h d ((r+10)^4) < 2 ^ ((r+10)^4) := by
  let t := r + 10
  have ht : 10 ≤ t := Nat.le_add_left ..
  have ht2 : 10 * t ≤ t ^ 2 := by simpa [pow_two] using Nat.mul_le_mul_right t ht
  have ht4 : 10 * t ^ 2 ≤ t ^ 4 := by
    calc
      _ ≤ t ^ 2 * t ^ 2 := Nat.mul_le_mul_right _ (by omega)
      _ = t ^ 4 := by ring
  have hw : t ^ 4 ≤ 2 ^ (t ^ 2) := by
    calc
      t ^ 4 ≤ (2 ^ t) ^ 4 := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
      _ = 2 ^ (t * 4) := (pow_mul ..).symm
      _ ≤ 2 ^ (t ^ 2) := Nat.pow_le_pow_right (by decide) (by omega)
  have h32 : 32 ≤ 2 ^ (t ^ 2) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 5 ≤ t ^ 2)
  have harr : 2 ^ (h+d) ≤ 2 ^ (t ^ 2) := Nat.pow_le_pow_right (by decide) hd
  have hscale : 2 ^ (h+d) + t ^ 4 + 32 ≤ 2 ^ (t ^ 2 + 2) := by
    rw [Nat.pow_add 2 (t ^ 2) 2, show 2 ^ 2 = 4 by decide]
    omega
  calc
    addressEnvelope h d (t ^ 4) ≤ 64 * (2 ^ (t ^ 2 + 2)) ^ 4 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hscale _)
    _ = 2 ^ (6 + (t ^ 2 + 2) * 4) := by rw [pow_add 2 6, pow_mul]; rfl
    _ < 2 ^ (t ^ 4) := Nat.pow_lt_pow_right (by decide) (by omega)

/-- The explicit eventual threshold for a linear phase bound `C*r`. -/
theorem addressEnvelope_lt_paperWord_of_linear {h d C r : ℕ} (hC : C ≤ r) (hd : h+d ≤ C*r) :
    addressEnvelope h d ((r+10)^4) < 2 ^ ((r+10)^4) :=
  addressEnvelope_lt_paperWord (hd.trans (by
    rw [pow_two]
    exact Nat.mul_le_mul (by omega) (by omega)))

end RAMSort

end VPVNP
end Computability
end OAI
