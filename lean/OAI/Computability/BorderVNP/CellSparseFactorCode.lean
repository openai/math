import OAI.Computability.BorderVNP.CellSparseSweep
import OAI.Computability.BorderVNP.CellProfileGenerator

/-! # Signed and Boolean observations of the private one-copy boxes -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

open CellMacro
open Profile (data)

/-- Relocate a cell bit port behind the guessed auxiliary prefix. -/
def Port.shift (p : Port) (off : ℕ) : Port := {p with base := off + p.base}

@[simp] theorem Port.atBit_shift (p : Port) (off i k : ℕ) :
    (p.shift off).atBit i k = off + p.atBit i k := by simp [Port.shift, Port.atBit, Nat.add_assoc]

/-- Only the outer usage-bit port is absolute inside a one-copy table; its own
table arguments are relative to the physical base of the box copy. -/
def Factor.shift (off : ℕ) : Factor → Factor
  | .unary i p => .unary i (p.shift off)
  | f => f

private theorem word_offset (ws : List ℕ) (bank : ℕ → Bool) (shift off : ℕ) :
    word bank (ws.map (shift + off + ·)) = word (data shift bank) (ws.map (off + ·)) := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    simp only [List.map_cons, word, ih]
    simp [data, Nat.add_assoc]
    rfl

/-- Physical offsets behind the auxiliary scratch region realize the original
unshifted site-box assignment. -/
theorem Factor.observe_shift (f : Factor) (shift off copy : ℕ) (bank : ℕ → Bool) :
    (f.shift shift).observe bank (shift+off) copy = f.observe (data shift bank) off copy := by
  cases f <;> simp only [Factor.shift, observe, word_offset, Port.atBit_shift]; simp [data, Nat.add_assoc]
  rfl

/-- A local observation updates success and sign, without evaluating the field
coefficient associated with its optional gadget identifier. -/
def updateObservation (obs : Option (Bool × Option ℕ)) (f : Flags) : Flags :=
  ⟨f.ok && obs.isSome, f.minus ^^ (obs.map Prod.fst).getD false⟩

private theorem sign_total (f : Factor) (off copy : NatExpr) (e : List ℕ) (bank : ℕ → Bool) :
    (factorSign off f).eval e bank =
      ((f.observe bank (off.eval e) (copy.eval e)).map Prod.fst).getD false := by
  cases h : f.observe bank (off.eval e) (copy.eval e) with
  | some bg => exact factorSign_correct f off copy e bank bg.1 bg.2 h
  | none =>
    cases f with
    | sign ws rs =>
      apply Bool.eq_false_iff.mpr
      intro ht
      rw [factorSign, rowTest_correct, tableWires_eval] at ht
      simp only [Factor.observe, Option.map_eq_none_iff] at h
      simp [h] at ht
    | _ => rfl

/-- Check the factor and toggle the sign only for a selected negative entry. -/
def factorBody (aux : ℕ) : FactorBody := fun f _ off copy =>
  let g := f.shift aux
  let physical := NatExpr.add (.lit aux) off
  .seq (factorPass physical copy g).guard (factorSign physical g).sign

private theorem factor_acts (aux : ℕ) (f : Factor) (idx off copy : NatExpr) (e : List ℕ) :
    Acts (factorBody aux f idx off copy) e (fun bank st =>
      updateObservation (f.observe (data aux bank) (off.eval e) (copy.eval e)) st) := by
  intro ops st v
  simp only [factorBody, Stmt.expand, List.append_assoc, Term.value_guard, Term.value_sign]
  have hpass := Bool.eq_iff_iff.mpr (factorPass_correct (f.shift aux) (.add (.lit aux) off) copy e (lookup v))
  rw [hpass, sign_total (f.shift aux) (.add (.lit aux) off) copy e (lookup v)]
  simp only [NatExpr.eval, Factor.observe_shift, updateObservation]

/-- The generator scans all repeated one-copy boxes while preserving their actual
order and signs. No expanded list of per-copy factor records is an input. -/
theorem factor_sweep (D : Directory) (aux : ℕ) (e : List ℕ) :
    Acts (sweep (factorBody aux) D.blocks 0) e (fun bank st =>
      D.occurrences.foldl (fun f o => updateObservation (o.factor.observe (data aux bank) o.offset o.copy) f) st) := by
  intro ops f v
  have h := sweep_acts (factorBody aux) D.blocks 0 e
    (fun bank st z => updateObservation (z.1.factor.observe (data aux bank) z.1.offset z.1.copy) st)
    (factor_acts aux) ops f v
  rw [D.blocks_visits] at h
  rw [h]
  congr 1
  conv_rhs => rw [← List.zipIdx_map_fst 0 D.occurrences]
  simp only [List.foldl_map]

/-- Read a particular gadget-position indicator on a physical occurrence. Missing
entries have no selected position and are separately rejected by the validity scan. -/
def selected (id : ℕ) (bank : ℕ → Bool) (o : Occurrence) : Bool :=
  ((o.factor.observe bank o.offset o.copy).bind Prod.snd) == some id

/-- The compiled indicator matches the original occurrence, on both passing and
malformed assignments. -/
theorem factorSelect_total (id aux : ℕ) (f : Factor) (off copy : NatExpr) (e : List ℕ) (bank : ℕ → Bool) :
    (factorSelect (.add (.lit aux) off) id (f.shift aux)).eval e bank =
      selected id (data aux bank) ⟨f, off.eval e, copy.eval e⟩ := by
  apply Bool.eq_iff_iff.mpr
  cases f with
  | gadget wires rows =>
    simp [selected, factorSelect, Factor.shift, Factor.observe, rowTest_correct, NatExpr.eval,
      tableWires_eval, word_offset]
    cases rows[word (data aux bank) (wires.map (off.eval e + ·))]? <;> simp
  | truth wires rows => simp [selected, factorSelect, Factor.shift, Factor.observe, Term.eval]; split <;> simp
  | sign wires rows =>
    simp [selected, factorSelect, Factor.shift, Factor.observe, Term.eval]
    cases rows[word (data aux bank) (wires.map (off.eval e + ·))]? <;> simp
  | unary i p => simp [selected, factorSelect, Factor.shift, Factor.observe, Term.eval]; split <;> simp

end CellSparse

end BorderVNP
end Computability
end OAI
