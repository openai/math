import OAI.Computability.NearSquareRoot.InterchangeROMOuterBank
import OAI.Computability.NearSquareRoot.InterchangeROMExpose
import OAI.Computability.NearSquareRoot.InterchangeMixed
import OAI.Computability.NearSquareRoot.InterchangeFatRecursion

/-! # Geometry of the physical small-row bank and the full reserve ledger -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMOuter

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Adic IntegerMultiplication.Loom
  NearSquareRoot.InterchangeAddress NearSquareRoot.InterchangeAddress.Request
  NearSquareRoot.InterchangeFrame NearSquareRoot.InterchangeROMExpose

abbrev axisP (i : Input) (_ : Unit) := i.req.before
abbrev axisG (i : Input) (_ : Unit) := gap i.b 1 (rem i) i.req.between
abbrev axisB (i : Input) (_ : Unit) := post i.b (rem i) i.req.after_
abbrev axisF (i : Input) (_ : Unit) := f i

abbrev rowsAt (i : Input) (count : ℕ) :=
  BatchFrame.rows (b:=i.b) (ord i) (axisP i) (axisG i) (axisB i) (axisF i) count ()
abbrev groupedRows (i : Input) (W : ℕ) := rowsAt i (BatchRows.groups i.b W)
noncomputable abbrev paddedRow (i : Input) {W : ℕ} (u : Fin W) :=
  BatchFrame.padded (axisP i) (axisG i) (axisB i) (axisF i) (by have := i.radix; omega : 0 < i.b)
    (fun _ : Unit => centerValues i) u ()

theorem grouped_counts (i : Input) (W : ℕ) (hW : 3≤W) (hw : W ≤ i.b) :
    3*(groupedRows i W).count ≤ 2*i.req.rows.count ∧
    i.b*(groupedRows i W).count = BatchRows.groups i.b W*i.req.rows.count := by
  have same : (rowsAt i i.b).count=i.req.rows.count := (row_counts i).2.2
  rw [← same]
  exact ⟨(Nat.mul_le_mul_right _ hW).trans
    (BatchFrame.row_volume (ord i) (axisP i) (axisG i) (axisB i) (axisF i) (by omega) hw ()),
    BatchFrame.row_volume_exact (ord i) (axisP i) (axisG i) (axisB i) (axisF i) W ()⟩

/-- Assemble the exact multiplicity and mass of the two concrete ledgers. -/
theorem step_account (i : Input) (W C A : ℕ) (hW : 3≤W) (hw : W ≤ i.b) (valid : Request i.b → Prop)
    (small full : List (Request i.b)) (sm : small.length ≤ C) (fu : full.length ≤ A)
    (hs : ∀ q ∈ small, valid q ∧ q.width=f i ∧ q.recordWidth=i.req.recordWidth ∧
      q.rows.count=(groupedRows i W).count)
    (hf : ∀ q ∈ full, valid q ∧ q.width=f i ∧ q.recordWidth=i.req.recordWidth ∧
      q.rows.count=i.req.rows.count) :
    stepAccount valid i.n (((C*BatchRows.groups i.b W:ℕ):ℝ)/i.b+A) i.req (small++full) ∧
    ∀ q∈small, 3*q.rows.count ≤ 2*i.req.rows.count := by
  obtain ⟨shrink,ratio⟩ := grouped_counts i W hW hw
  let spec (_ : Unit) (q : Request i.b) := valid q ∧ q.width = f i ∧ q.recordWidth = i.req.recordWidth
  have one : Phase spec (fun _ => (groupedRows i W).count) C () small :=
    ⟨sm,fun q h => ⟨⟨(hs q h).1,(hs q h).2.1,(hs q h).2.2.1⟩,(hs q h).2.2.2⟩⟩
  have two : Phase spec (fun _ => i.req.rows.count) A () full :=
    ⟨fu,fun q h => ⟨⟨(hf q h).1,(hf q h).2.1,(hf q h).2.2.1⟩,(hf q h).2.2.2⟩⟩
  obtain ⟨closed,paid⟩ := merge_ledgers (b:=i.b) (by have := i.radix; omega)
    (fun _ => by omega) (fun _ => ratio.le) () small full one two
  exact ⟨⟨fun q h => ⟨(closed q h).1.1,(closed q h).1.2.1,(closed q h).1.2.2,(closed q h).2⟩,paid⟩,
    fun q h => (hs q h).2.2.2.symm ▸ shrink⟩

end InterchangeROMOuter

end NearSquareRoot
end Computability
end OAI
