import OAI.Optimization.LinearProgramming.RAM.TapeBits
import OAI.Optimization.LinearProgramming.Farkas.Basic
import OAI.Optimization.LinearProgramming.Compression.ProjectionSmallPoint
import OAI.Optimization.LinearProgramming.Specification

/-! Converting witness heights into the scalar RAM's binary input convention. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators Matrix
open RAM

/-- Any coefficient on the input tape contributes to its total binary length. -/
theorem ratBits_le_totalBits_of_mem {q : ℚ} {tape : List ℚ} (hq : q ∈ tape) :
    ratBits q ≤ totalBits tape := RAM.member_bits_le_totalBits hq

/-- The scalar tape has at least one bit per entry, including zero entries. -/
theorem tape_length_le_totalBits (tape : List ℚ) : tape.length ≤ totalBits tape :=
  RAM.entry_count_le_totalBits tape

private theorem row_length_le_flatten {row : List ℚ} {rows : List (List ℚ)} (h : row ∈ rows) :
    row.length ≤ rows.flatten.length := by
  induction rows with
  | nil => simp at h
  | cons l ls ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · simpa using (ih h).trans (Nat.le_add_left ls.flatten.length l.length)

/-- The complete LP input bounds both dimensions when at least one row is present. -/
theorem dimensions_le_totalBits {m d : ℕ} (hm : 0 < m)
    (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) :
    m ≤ totalBits (lpInput A b) ∧ d ≤ totalBits (lpInput A b) := by
  let rows := List.ofFn fun i => List.ofFn (A i)
  have hlen : rows.flatten.length + m ≤ totalBits (lpInput A b) := by
    simpa [lpInput, rows] using tape_length_le_totalBits (lpInput A b)
  have hrow : List.ofFn (A ⟨0,hm⟩) ∈ rows := List.mem_ofFn.mpr ⟨⟨0,hm⟩, rfl⟩
  have hd : d ≤ rows.flatten.length := by simpa using row_length_le_flatten hrow
  omega

/-- Entrywise heights from the RAM's signed-numerator/positive-denominator bit count. -/
theorem height_le_two_pow_of_ratBits {q : ℚ} {L : ℕ} (h : ratBits q ≤ L) :
    q.num.natAbs ≤ 2 ^ L ∧ q.den ≤ 2 ^ L := by
  unfold ratBits at h
  constructor <;> exact Nat.lt_log2_self.le.trans (Nat.pow_le_pow_right (by decide) (by omega))

/-- A feasible input has a feasible rational output whose coordinate bit lengths
are bounded by one explicit cubic polynomial in the original scalar tape length. -/
theorem exists_lp_point_polynomial_bits {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {m d : ℕ} (hm : 0 < m)
    (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (hne : ∃ x : Fin d → K, A.map (fun z : ℚ => (z : K)) *ᵥ x ≤ fun i => (b i : K)) :
    let L := totalBits (lpInput A b)
    ∃ q, Feasible A b q ∧ ∀ j, ratBits (q j) ≤ 3 + 2 * (L*L + (L+1)*(L+2)*L) := by
  let L := totalBits (lpInput A b)
  have hA (i : Fin m) (j : Fin d) : ratBits (A i j) ≤ L := by
    apply ratBits_le_totalBits_of_mem
    apply List.mem_append_left
    exact List.mem_flatten.mpr ⟨List.ofFn (A i), List.mem_ofFn.mpr ⟨i, rfl⟩,
      List.mem_ofFn.mpr ⟨j, rfl⟩⟩
  have hb (i : Fin m) : ratBits (b i) ≤ L :=
    ratBits_le_totalBits_of_mem (List.mem_append_right _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
  obtain ⟨q, hq, hh⟩ := exists_small_rat_feasible A b Nat.one_le_two_pow
    (fun i j => height_le_two_pow_of_ratBits (hA i j)) (fun i => height_le_two_pow_of_ratBits (hb i)) hne
  refine ⟨q, hq, ?_⟩
  intro j
  have hn := log2_le_of_cramer_height (hh j).1
  have hd := log2_le_of_cramer_height (hh j).2
  simp only [Fintype.card_fin, Nat.log2_two_pow] at hn hd
  have hdim : d ≤ L := (dimensions_le_totalBits hm A b).2
  change ratBits (q j) ≤ 3 + 2 * (L*L + (L+1)*(L+2)*L)
  calc
    ratBits (q j) ≤ 3 + 2 * (d*d + (L+1)*(d+2)*d) := by unfold ratBits; omega
    _ ≤ _ := by gcongr

private abbrev CertificateRow (m d : ℕ) := Fin m ⊕ (Option (Fin d) × Bool)

private def certificateMatrix {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) :
    Matrix (CertificateRow m d) (Fin m) ℚ :=
  Matrix.of fun row i => row.elim (fun j => if i = j then -1 else 0) fun p =>
    let v := p.1.elim (b i) (fun j => A i j)
    if p.2 then v else -v

private def certificateRhs {m d : ℕ} : CertificateRow m d → ℚ :=
  Sum.elim (fun _ => 0) fun p =>
    let v := p.1.elim (-1 : ℚ) (fun _ => 0)
    if p.2 then v else -v

private theorem certificateRows_spec {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ)
    (b y : Fin m → ℚ) :
    certificateMatrix A b *ᵥ y ≤ certificateRhs ↔
      0 ≤ y ∧ A.transpose *ᵥ y = 0 ∧ b ⬝ᵥ y = -1 := by
  let M := certificateMatrix A b
  let val (k : Option (Fin d)) := k.elim (b ⬝ᵥ y) ((A.transpose *ᵥ y) ·)
  let rhs (k : Option (Fin d)) := k.elim (-1 : ℚ) (fun _ => 0)
  have row (k : Option (Fin d)) (s : Bool) :
      (M *ᵥ y) (.inr (k,s)) = if s then val k else -val k := by
    cases k <;> cases s <;> simp [M, certificateMatrix, val, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  have coord (i : Fin m) : (M *ᵥ y) (.inl i) = -y i := by
    simp [M, certificateMatrix, Matrix.mulVec, dotProduct, ite_mul]
  constructor
  · intro h
    have heq (k : Option (Fin d)) : val k = rhs k := by
      have h1 := h (.inr (k,true))
      have h2 := h (.inr (k,false))
      change (M *ᵥ y) (.inr (k,true)) ≤ rhs k at h1
      change (M *ᵥ y) (.inr (k,false)) ≤ -rhs k at h2
      simp only [row, ite_true, Bool.false_eq_true, ite_false, neg_le_neg_iff] at h1 h2
      exact le_antisymm h1 h2
    refine ⟨?_, funext (fun j => heq (some j)), heq none⟩
    intro i
    have h0 := h (.inl i)
    change (M *ᵥ y) (.inl i) ≤ 0 at h0
    simpa [coord] using h0
  · rintro ⟨h0,hA,hb⟩ (i | ⟨k,s⟩)
    · change (M *ᵥ y) (.inl i) ≤ 0
      simpa [coord] using h0 i
    · change (M *ᵥ y) (.inr (k,s)) ≤ (if s then rhs k else -rhs k)
      rw [row]
      have heq : val k = rhs k := by cases k <;> simp [val, rhs, hA, hb]
      simp [heq]

/-- Sparse normalized multipliers can be replaced by short rational multipliers
without activating any previously zero coordinate. -/
theorem exists_short_normalized_certificate {m d : ℕ}
    (A : Matrix (Fin m) (Fin d) ℚ) (b y : Fin m → ℚ) (hy : 0 ≤ y)
    (hyA : A.transpose *ᵥ y = 0) (hyb : b ⬝ᵥ y = -1) :
    let L := totalBits (lpInput A b)
    ∃ z : Fin m → ℚ, 0 ≤ z ∧ A.transpose *ᵥ z = 0 ∧ b ⬝ᵥ z = -1 ∧
      (∀ i, y i = 0 → z i = 0) ∧
      ∀ i, ratBits (z i) ≤ 3 + 2 * (L*L + (L+1)*(L+2)*L) := by
  classical
  let L := totalBits (lpInput A b)
  let B := 2 ^ L
  have hB : 1 ≤ B := Nat.one_le_two_pow
  have hA (i : Fin m) (j : Fin d) : (A i j).num.natAbs ≤ B ∧ (A i j).den ≤ B := by
    apply height_le_two_pow_of_ratBits
    apply ratBits_le_totalBits_of_mem
    apply List.mem_append_left
    exact List.mem_flatten.mpr ⟨List.ofFn (A i), List.mem_ofFn.mpr ⟨i, rfl⟩,
      List.mem_ofFn.mpr ⟨j, rfl⟩⟩
  have hb (i : Fin m) : (b i).num.natAbs ≤ B ∧ (b i).den ≤ B :=
    height_le_two_pow_of_ratBits (ratBits_le_totalBits_of_mem
      (List.mem_append_right _ (List.mem_ofFn.mpr ⟨i, rfl⟩)))
  let M := certificateMatrix A b
  let r : CertificateRow m d → ℚ := certificateRhs
  let zeroRows := {i : Fin m // y i = 0}
  have hM (i : CertificateRow m d) (j : Fin m) :
      (M i j).num.natAbs ≤ B ∧ (M i j).den ≤ B := by
    rcases i with k | ⟨_ | k,s⟩
    · by_cases hj : j = k <;> simpa [M, certificateMatrix, hj] using hB
    · cases s <;> simpa [M, certificateMatrix] using hb j
    · cases s <;> simpa [M, certificateMatrix] using hA j k
  have hr (i : CertificateRow m d) : (r i).num.natAbs ≤ B ∧ (r i).den ≤ B := by
    rcases i with k | ⟨_ | k,s⟩
    · simpa [r, certificateRhs] using hB
    · cases s <;> simpa [r, certificateRhs] using hB
    · cases s <;> simpa [r, certificateRhs] using hB
  have hne : ∃ t : Fin m → ℚ, M.map (fun z : ℚ => (z : ℚ)) *ᵥ t ≤ (fun i => (r i : ℚ)) ∧
      ∀ i : zeroRows, t i.val = (0 : ℚ) := by
    refine ⟨y, ?_, fun i => i.2⟩
    have h := (certificateRows_spec A b y).mpr ⟨hy, hyA, hyb⟩
    simpa [M, r] using h
  have hz0 (_ : zeroRows) : (0 : ℚ).num.natAbs ≤ B ∧ (0 : ℚ).den ≤ B := by simpa using hB
  obtain ⟨z,hz,hp,hh⟩ := exists_small_rat_feasible_with_fixed M r
    (fun i : zeroRows => i.val) (fun _ => 0) hB hM hr hz0 hne
  obtain ⟨hn,hAz,hbz⟩ := (certificateRows_spec A b z).mp hz
  refine ⟨z,hn,hAz,hbz, fun i hi => hp ⟨i,hi⟩, ?_⟩
  intro i
  have hn' := log2_le_of_cramer_height (hh i).1
  have hd' := log2_le_of_cramer_height (hh i).2
  simp only [Fintype.card_fin, B, Nat.log2_two_pow] at hn' hd'
  have hm : m ≤ L := (dimensions_le_totalBits (Nat.zero_lt_of_lt i.isLt) A b).1
  change ratBits (z i) ≤ 3 + 2 * (L*L + (L+1)*(L+2)*L)
  calc
    _ ≤ 3 + 2 * (m*m + (L+1)*(m+2)*m) := by unfold ratBits; omega
    _ ≤ _ := by gcongr

/-- The output-existence part of Theorem 1.1, including normalization, sparsity,
and an explicit polynomial bound in the actual input encoding for either tag. -/
theorem exists_short_feasibility_output {m d : ℕ} (hm : 0 < m)
    (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) :
    let L := totalBits (lpInput A b)
    let bits := 3 + 2 * (L*L + (L+1)*(L+2)*L)
    (∃ x, Feasible A b x ∧ ∀ j, ratBits (x j) ≤ bits) ∨
    (∃ y, Certificate A b y ∧ b ⬝ᵥ y = -1 ∧ ∀ i, ratBits (y i) ≤ bits) := by
  rcases Farkas.sparse_alternative A b with ⟨x,hx⟩ | ⟨y,hy,hAy,hby,hs⟩
  · left
    apply exists_lp_point_polynomial_bits (K := ℚ) hm A b
    exact ⟨x, by simpa using hx⟩
  · obtain ⟨z,hz,hAz,hbz,hsupport,hbits⟩ := exists_short_normalized_certificate A b y hy hAy hby
    refine Or.inr ⟨z, ⟨hz, hAz, by rw [hbz]; norm_num, ?_⟩, hbz, hbits⟩
    apply (Finset.card_le_card ?_).trans hs
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact fun h => hi (hsupport i h)

end Compression
end LinearProgramming
end Optimization
end OAI
