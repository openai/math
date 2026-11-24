import OAI.Computability.VPVNP.CompressorDescriptorSpace
import OAI.Computability.VPVNP.CompressorFormulaRow

/-!
# Publishing the pointer words of a compressor level

After the scalar publisher has installed the current base count, degree and
lane count, a fixed burst writes the six incidence column heads and the heads
of all fixed-width record tables. The current row count comes from the current
header. The rectangular table capacity comes from the initial header, whose
base count times lane count gives the initial number of positions.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.DescriptorHeads

open BurstRAM BurstRAM.PrivateRAM DescriptorSpace PhaseRecipe
open scoped Fin.CommRing

variable {w : ℕ}

private def loadAt (p : Fin 5) (j : ℕ) : Expr := .load ((Expr.publicWord p).add (.lit j))

private def rowCount : Expr := ((loadAt 0 0).mul (loadAt 0 2)).mul (loadAt 0 1)

private def capacity (F : Shape) : Expr := ((loadAt 1 0).mul (loadAt 1 2)).mul (.lit F.slots)

private def firstColumn (F : Shape) : Expr := (Expr.publicWord 0).add (.lit (F.scalarFields+6+F.tables))

/-- The shape is compiled into the worker. Public words zero and one hold
the current level header address and the level-zero header address. -/
def publisher (F : Shape) : FormulaRow (F.tables + 3) where
  dest := (Expr.publicWord 0).add (.lit F.scalarFields)
  fields j := if j.val < 6 then (firstColumn F).add ((Expr.lit j.val).mul rowCount)
    else ((firstColumn F).add ((Expr.lit 6).mul (capacity F))).add
      ((Expr.lit (j.val-6)).mul ((capacity F).mul (.lit F.fields)))

/-- Catalog entry for one guarded call at cursor zero. -/
def worker (F : Shape) : Schedule.Pass :=
  ⟨_, _, _, (publisher F).recipe.table⟩

/-- The three live scalar cells shared with the scalar publisher. -/
structure CountsAt (base : Word w) (m : Memory w) (V D lanes : ℕ) : Prop where
  vertices : m base.val = (V : Word w)
  degree : m (base + 1).val = (D : Word w)
  replicas : m (base + 2).val = (lanes : Word w)

variable (L : Layout) (i : Fin L.levels) (pub : Fin 5 → Word w) (m : Memory w)

/-- Natural addresses calculated by the native code, expressed in the same
level-major coordinates as the cursor, shrink and refresh consumers. -/
theorem publish (s : Word w) (fit : endAddress L < 2^w)
    (current : pub 0 = (levelStart L i : Word w)) (first : pub 1 = (levelStart L 0 : Word w))
    {V D lanes V₀ D₀ lanes₀ : ℕ} (h : CountsAt (levelStart L i : Word w) m V D lanes)
    (h₀ : CountsAt (levelStart L 0 : Word w) m V₀ D₀ lanes₀)
    (hP : V₀ * lanes₀ = L.positions) :
    let R := publisher L.shape
    let M := R.recipe.table.instantiate w pub
    let rep := R.recipe.report pub s m
    let out := after m rep.events
    execute M.program (R.recipe.code.length+1) (M.program.start s) m [] = some rep ∧
      rep.result = some (s+1) ∧
      (∀ c : Fin 6, out (incidenceHead L i c) = (incidenceBase L i (V*lanes*D) c : Word w)) ∧
      (∀ a : Fin L.shape.tables, out (tableHead L i a) = (tableBase L i a : Word w)) ∧
      (∀ a, a < levelStart L i + L.shape.scalarFields ∨ incidenceStart L i ≤ a → out a = m a) ∧
      rep.events.length = R.recipe.code.length ∧ rep.probes = R.recipe.reads + (L.shape.tables+3+3) ∧
      choiceBits rep.events = [] := by
  intro R M rep out
  have hs := level_room L fit i
  have hh : incidenceStart L i ≤ levelStart L (i.val+1) := by
    simp only [incidenceStart, levelStart, Nat.succ_mul, levelWords]
    omega
  have hroom := hh.trans_lt hs
  change levelStart L i + (L.shape.scalarFields + 6 + L.shape.tables) < 2^w at hroom
  have dest : R.dest.eval pub s m = ((levelStart L i + L.shape.scalarFields : ℕ) : Word w) := by
    simp [R, publisher, Expr.eval, Expr.add, BinaryOp.eval, current]
  have hv : (R.dest.eval pub s m).val = levelStart L i + L.shape.scalarFields := by
    rw [dest, Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have hfit : (R.dest.eval pub s m).val + (L.shape.tables+3+3) ≤ 2^w := by rw [hv]; omega
  have run := R.execute pub s m hfit
  have hV : m (levelStart L i % 2^w) = (V : Word w) := h.vertices
  have hV₀ : m (levelStart L 0 % 2^w) = (V₀ : Word w) := h₀.vertices
  have rows : rowCount.eval pub s m = ((V * lanes * D : ℕ) : Word w) := by
    simp [rowCount, loadAt, Expr.add, Expr.mul, Expr.eval, BinaryOp.eval, current,
      hV, h.degree, h.replicas]
  have cap : (capacity L.shape).eval pub s m = (slotCapacity L : Word w) := by
    simp [capacity, loadAt, Expr.add, Expr.mul, Expr.eval, BinaryOp.eval, first,
      hV₀, h₀.replicas, slotCapacity, ← hP]
  have col : (firstColumn L.shape).eval pub s m = (incidenceStart L i : Word w) := by
    simp [firstColumn, Expr.eval, Expr.add, BinaryOp.eval, current, incidenceStart, levelHeaderWords]
  refine ⟨run.1, run.2.1, ?_, ?_, ?_, run.2.2.2.2⟩
  · intro c
    let j : Fin (L.shape.tables+3+3) := ⟨c.val, by have := c.isLt; omega⟩
    have hw := run.2.2.1 j
    rw [hv] at hw
    change out (incidenceHead L i c) = _
    have hf : (R.fields j).eval pub s m =
        (incidenceBase L i (V * lanes * D) c : Word w) := by
      change (if c.val < 6 then _ else _ : Expr).eval pub s m = _
      rw [ite_eq_left c.isLt]
      simp only [j, Expr.add, Expr.mul, Expr.eval, BinaryOp.eval, col, rows, incidenceBase, Nat.cast_add,
        Nat.cast_mul]
    exact hw.trans hf
  · intro a
    let j : Fin (L.shape.tables+3+3) := ⟨6+a.val, by have := a.isLt; omega⟩
    have hw := run.2.2.1 j
    rw [hv] at hw
    have hf : (R.fields j).eval pub s m = (tableBase L i a : Word w) := by
      change (if 6+a.val < 6 then _ else _ : Expr).eval pub s m = _
      rw [ite_eq_right (by omega)]
      simp only [j, Expr.add, Expr.mul, Expr.eval, BinaryOp.eval, col, cap,
        Nat.add_sub_cancel_left, tableBase, tableWords, arrayBase, Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat]
    simpa only [j, tableHead, Nat.add_assoc] using hw.trans hf
  · intro a ha
    apply run.2.2.2.1
    rw [hv]
    simpa only [incidenceStart, levelHeaderWords, Nat.add_assoc, Nat.add_comm 6 L.shape.tables] using ha

end CompressorRecords.DescriptorHeads

end VPVNP
end Computability
end OAI
