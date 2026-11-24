import OAI.Computability.VPVNP.CompressorDescriptorParameters
import OAI.Computability.VPVNP.CompressorCalendarRows

/-!
# Space for the cursor parameters in the chronological directory

The first level follows the exact number of rows published by the calendar.
Its address depends only on the polynomially bounded workspace base, the
fixed row pitch and that row count. Hence one threshold works independently
of the allocated position and level counts.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.DescriptorParameters

open BurstRAM CursorBounds DescriptorSpace LevelFields Filter CursorRAM.ParametersInit

private theorem bounded_blocks (D : CalendarRows.Spec) : PolynomiallyBounded (roundedDown D.p D.q) :=
  (PolynomiallyBounded.id.pow D.p).of_le fun n ↦ Nat.log_le_self (2^D.q) (n^D.p)

private theorem bounded_rows (D : CalendarRows.Spec) : PolynomiallyBounded (CalendarRows.rows D) :=
  (PolynomiallyBounded.const D.initialRows).add ((PolynomiallyBounded.const D.phaseRows).mul (bounded_blocks D))

theorem eventually_tight_capacity (D : CalendarRows.Spec) (F : Shape) (B a lanes : ℕ)
    (hB : 1 ≤ B) (hθ : (D.p : ℝ) / D.q ≤ 1) (hlanes : lanes ≤ B)
    {base : ℕ → ℕ} (hb : PolynomiallyBounded base) :
    ∀ᶠ n : ℕ in atTop, ∀ positions levels : ℕ,
      let L := tightDirectory ⟨F,base n,positions,levels⟩ (CalendarRows.rows D n)
      let l := roundedDown D.p D.q n * lanes
      l ≤ virtualBits B n ∧
      Capacity B n a l (directoryBase L) 1 (incidenceStart L 0) (levelStart L 0+6) := by
  let dir n := base n+9+(F.arity+1)+1
  let first n := dir n + CalendarRows.rows D n * (F.arity+3)
  let columns n := first n + (F.scalarFields+6+F.tables)
  let dest n := first n+6
  have hd : PolynomiallyBounded dir :=
    ((hb.add (PolynomiallyBounded.const 9)).add (PolynomiallyBounded.const (F.arity+1))).add
      (PolynomiallyBounded.const 1)
  have hfirst : PolynomiallyBounded first := hd.add ((bounded_rows D).mul (PolynomiallyBounded.const (F.arity+3)))
  have hcols : PolynomiallyBounded columns := hfirst.add (PolynomiallyBounded.const (F.scalarFields+6+F.tables))
  have hdest : PolynomiallyBounded dest := hfirst.add (PolynomiallyBounded.const 6)
  filter_upwards [eventually_ge_atTop 3, eventually_capacity B a hB hd (PolynomiallyBounded.const 1)
    hcols hdest] with n hn hc
  intro positions levels
  have hl : roundedDown D.p D.q n * lanes ≤ virtualBits B n := by
    rw [roundedDown_eq, Nat.mul_comm]
    exact laneBudget B lanes n hlanes hθ hn
  refine ⟨hl, ?_⟩
  let L := tightDirectory ⟨F,base n,positions,levels⟩ (CalendarRows.rows D n)
  have eqFirst : levelStart L 0 = first n := by
    simp only [L,levelStart,levelsBase,tight_rows,Nat.zero_mul,Nat.add_zero]
    rfl
  change Capacity B n a (roundedDown D.p D.q n * lanes) (directoryBase L) 1
    (levelStart L 0+levelHeaderWords L) (levelStart L 0+6)
  rw [eqFirst]
  exact hc _ hl

/-- The exclusive descriptor end placed in the history-arena scalar fits
even if the chronological calendar differs from the reserved pass schedule. -/
theorem eventually_tight_end (D : CalendarRows.Spec) (F : Shape) (B steps : ℕ) (hB : 1 ≤ B)
    {base : ℕ → ℕ} (hb : PolynomiallyBounded base) :
    ∀ᶠ n : ℕ in atTop,
      endAddress (tightDirectory (cursorLayout F B steps ((D.p : ℝ)/D.q) (base n) n)
        (CalendarRows.rows D n)) < 2^wordBits B n := by
  let dir n := base n+9+(F.arity+1)+1
  let first n := dir n + CalendarRows.rows D n * (F.arity+3)
  have hd : PolynomiallyBounded dir :=
    ((hb.add (PolynomiallyBounded.const 9)).add (PolynomiallyBounded.const (F.arity+1))).add
      (PolynomiallyBounded.const 1)
  have hf : PolynomiallyBounded first := hd.add ((bounded_rows D).mul (PolynomiallyBounded.const (F.arity+3)))
  have levels := (PolynomiallyBounded.const 1).add ((PolynomiallyBounded.const (steps+1)).mul (bounded_blocks D))
  have slots := (CursorRAM.bounded_positions B).mul (PolynomiallyBounded.const F.slots)
  have tables := (PolynomiallyBounded.const F.tables).mul (slots.mul (PolynomiallyBounded.const F.fields))
  have stride := ((PolynomiallyBounded.const (F.scalarFields+6+F.tables)).add
    ((PolynomiallyBounded.const 6).mul slots)).add tables
  filter_upwards [CursorRAM.eventual_word_room B hB (hf.add (levels.mul stride))] with n h
  simp only [endAddress,levelStart,levelsBase,tight_rows,tight_stride]
  rw [roundedDown_eq] at h
  exact h

end CompressorRecords.DescriptorParameters

end VPVNP
end Computability
end OAI
