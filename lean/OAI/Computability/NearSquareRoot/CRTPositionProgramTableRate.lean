import OAI.Computability.NearSquareRoot.CRTPositionProgramTable

/-! # Clock of the assembled position-table sweep

When the payload width covers both fixed polynomial degrees, it pays for the
initial descriptor preparation and the table work at every row. The assembled
stream contains at most a constant times the logarithm of the address width
many opcodes.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionProgram

/-- Cost of one full array pass at exponent `ρ`. -/
noncomputable def rowRate (ρ : ℝ) (k l : ℕ) : ℝ :=
  ((2^k : ℕ) : ℝ) * l * ((k+1 : ℕ) : ℝ)^ρ

/-- Full-array pass cost times the number of guarded passes in a position sweep. -/
noncomputable def tableRate (ρ : ℝ) (k l : ℕ) : ℝ :=
  rowRate ρ k l * ((1 + Nat.clog 2 (k+1) : ℕ) : ℝ)

theorem rowRate_nonneg (ρ : ℝ) (k l : ℕ) : 0 ≤ rowRate ρ k l := by
  unfold rowRate
  positivity

theorem tableRate_nonneg (ρ : ℝ) (k l : ℕ) : 0 ≤ tableRate ρ k l := by
  exact mul_nonneg (rowRate_nonneg ..) (Nat.cast_nonneg _)

theorem volume_le_rowRate {ρ : ℝ} (hρ : 0 ≤ ρ) (k l : ℕ) :
    ((2^k : ℕ) : ℝ) * l ≤ rowRate ρ k l := by
  apply le_mul_of_one_le_right (by positivity)
  exact Real.one_le_rpow (by exact_mod_cast Nat.le_add_left 1 k) hρ

theorem width_le_rowRate {ρ : ℝ} (hρ : 0 ≤ ρ) (k l : ℕ) : (l : ℝ) ≤ rowRate ρ k l := by
  calc
    (l : ℝ) ≤ ((2^k : ℕ) : ℝ) * l := le_mul_of_one_le_left (by positivity)
      (by exact_mod_cast (Nat.one_le_pow k 2 (by decide)))
    _ ≤ _ := volume_le_rowRate hρ k l

theorem rowRate_le_tableRate (ρ : ℝ) (k l : ℕ) : rowRate ρ k l ≤ tableRate ρ k l := by
  apply le_mul_of_one_le_right (rowRate_nonneg ..)
  exact_mod_cast Nat.le_add_right 1 _

theorem one_le_rowRate {ρ : ℝ} (hρ : 0 ≤ ρ) (k : ℕ) {l : ℕ} (hl : 0 < l) :
    1 ≤ rowRate ρ k l :=
  (show (1 : ℝ) ≤ l by exact_mod_cast hl).trans (width_le_rowRate hρ k l)

theorem one_le_tableRate {ρ : ℝ} (hρ : 0 ≤ ρ) (k : ℕ) {l : ℕ} (hl : 0 < l) :
    1 ≤ tableRate ρ k l := (one_le_rowRate hρ k hl).trans (rowRate_le_tableRate ..)

/-- The fitted degree consumes at most one additional payload-width of storage
work per row. -/
theorem tableMass_le_rowRate (ρ : ℝ) (s : TableShape) (d : ℕ) (hd : (s.k+1)^d ≤ s.width) :
    tableMass ρ s d ≤ 2 * rowRate ρ s.k s.width := by
  have cap : ((s.k+1 : ℕ) : ℝ)^d ≤ s.width := by exact_mod_cast hd
  unfold tableMass rowRate
  calc
    _ ≤ ((2^s.k : ℕ) : ℝ) * (s.width + (s.width : ℝ)) * ((s.k+1 : ℕ) : ℝ)^ρ := by
      gcongr
    _ = _ := by ring

/-- A direct count of all emitted descriptors, including both reflected rounds
and the individual tail swaps. -/
theorem table_stream_length (s : TableShape) :
    s.stream.length ≤ 1804 * (1 + Nat.clog 2 (s.k+1)) := by
  apply (assemble_length (guardWidth s.k) s.p).trans
  unfold guardWidth
  omega

/-- Charge the setup clock, padded integer opcode clocks, and two boundary
steps to the same volume-times-logarithm estimate. -/
theorem table_clock_le {ρ : ℝ} (hρ : 0 ≤ ρ) (s : TableShape) (a d B C : ℕ)
    (ha : (s.k+1)^a ≤ s.width) (hd : (s.k+1)^d ≤ s.width) :
    ((B * (s.k+1)^a + s.stream.length * ((C+2)*⌈tableMass ρ s d⌉₊) + 2 : ℕ) : ℝ) ≤
      ((B + 5412*(C+2) + 2 : ℕ) : ℝ) * tableRate ρ s.k s.width := by
  have hw : 0 < s.width := lt_of_lt_of_le (by positivity) hd
  have h1 := one_le_rowRate hρ s.k hw
  have h2 := one_le_tableRate hρ s.k hw
  have hmass : 0 ≤ tableMass ρ s d := by unfold tableMass; positivity
  have round : (⌈tableMass ρ s d⌉₊ : ℝ) ≤ 3 * rowRate ρ s.k s.width := by
    linarith [Nat.ceil_lt_add_one hmass, tableMass_le_rowRate ρ s d hd]
  let J := 1 + Nat.clog 2 (s.k+1)
  have len : (s.stream.length : ℝ) ≤ 1804 * (J : ℝ) := by exact_mod_cast table_stream_length s
  have setup : (((s.k+1)^a : ℕ) : ℝ) ≤ tableRate ρ s.k s.width :=
    (show (((s.k+1)^a : ℕ) : ℝ) ≤ s.width by exact_mod_cast ha).trans
      ((width_le_rowRate hρ s.k s.width).trans (rowRate_le_tableRate ..))
  have sweep :
      (s.stream.length : ℝ) * (((C+2 : ℕ) : ℝ) * (⌈tableMass ρ s d⌉₊ : ℝ)) ≤
        ((5412 * (C+2) : ℕ) : ℝ) * tableRate ρ s.k s.width := by
    calc
      _ ≤ (1804 * (J : ℝ)) * (((C+2 : ℕ) : ℝ) * (3 * rowRate ρ s.k s.width)) :=
        mul_le_mul len (mul_le_mul_of_nonneg_left round (Nat.cast_nonneg _)) (by positivity) (by positivity)
      _ = _ := by unfold tableRate J; push_cast; ring
  push_cast only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  push_cast only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at sweep
  linarith [mul_le_mul_of_nonneg_left setup (Nat.cast_nonneg B)]

end Controlled.PositionProgram

end NearSquareRoot
end Computability
end OAI
