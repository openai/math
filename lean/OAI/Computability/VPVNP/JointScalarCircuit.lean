import OAI.Computability.VPVNP.JointScalarCore
import OAI.Computability.VPVNP.JointScalarMotifCircuit

/-!
# The advised signed scalar checker

This Boolean circuit takes the raw binary equation address, the formal
exponent array, and a polarity bit. Its witness banks are counted by the
fixed bit-stack enumerator. Inactive banks are forced to zero, preserving
the number of accepting witnesses on the selected branch.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace JointScalar

open VerifierNetwork ParseGrammar
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit
  (Expr.eval Expr.size Expr.and Expr.mux Expr.eval_mux Expr.disjoin Expr.eval_disjoin_true Expr.size_disjoin_le
   Expr.eval_rename Expr.size_rename)
open scoped Classical

variable {n high t W flags clock motif g m q : ℕ}

/-- Wire the parse verifier to the low equation-address bits, the formal exponent array and the
parse-event flags of the joint checker. -/
def parseWire : ParseOracle.Input n t W flags → Input n high t W flags clock motif :=
  Sum.elim (Fin.addCases (fun j => rowWire (j.castAdd high))
    (fun j => let jb := finProdFinEquiv.symm j; exponentWire jb.1 jb.2)) flagWire

/-- Wire the universal-machine path verifier to the low equation-address bits and the clocked
choice bits of the joint checker. -/
def pathWire : Fin n ⊕ Fin clock → Input n high t W flags clock motif :=
  Sum.elim (fun j => rowWire (j.castAdd high)) choiceWire

private theorem assign_parse (negative : Bool) (row : ℕ) (a : Fin t → ℕ) (f : Fin flags → Bool)
    (u : Fin clock → Bool) (b : Fin motif → Bool) :
    assignment (n := n) (high := high) (W := W) negative row a f u b ∘ parseWire =
      Sum.elim (ParseOracle.query (fun j => row.testBit j.val) a W) f := by
  funext i
  rcases i with i | i
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [parseWire, ParseOracle.query]
  · simp [parseWire]

private theorem assign_path (negative : Bool) (row : ℕ) (a : Fin t → ℕ) (f : Fin flags → Bool)
    (u : Fin clock → Bool) (b : Fin motif → Bool) :
    assignment (n := n) (high := high) (W := W) negative row a f u b ∘ pathWire =
      Sum.elim (fun j => row.testBit j.val) u := by
  funext i
  cases i <;> simp [pathWire]

/-- Boolean expression testing whether every supplied fixed-width exponent word represents
zero. -/
def zeroWords {σ : Type*} (wire : Fin m → Fin W → σ) : Expr σ :=
  .not (Expr.disjoin (List.ofFn fun i => .not (OracleBinaryTarget.expr (wire i) 0)))

private theorem zeroWords_eval {σ : Type*} (wire : Fin m → Fin W → σ) (a : Fin m → ℕ)
    (ha : ∀ i, a i < 2^W) (x : σ → Bool) (hx : ∀ i j, x (wire i j) = (a i).testBit j.val) :
    (zeroWords wire).eval x = decide (∀ i, a i = 0) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  simp only [zeroWords, Expr.eval, Bool.not_eq_true']
  rw [Bool.eq_false_iff]
  change (¬ (Expr.disjoin _).eval x = true) ↔ _
  rw [Expr.eval_disjoin_true]
  simp only [List.mem_ofFn, exists_exists_eq_and, Expr.eval, Bool.not_eq_true',
    OracleBinaryTarget.expr_eval _ _ _ (ha _) x (hx _), decide_eq_false_iff_not, not_exists, not_not]

/-- The two Boolean outputs retained from the parse verifier and the clocked path verifier. -/
abbrev Checks := Unit ⊕ Unit

/-- Formal coordinate placements are encoded in the circuit wiring. The
negative grammar branch is enabled precisely for the zero exponent. -/
def finish (prod : Fin g → Fin t) (localMap : Fin m → Fin t)
    (tables : Fin q → Motif.Table m) :
    Expr (Input n high t W flags clock motif ⊕ Checks) :=
  let raw : Input n high t W flags clock motif → _ := Sum.inl
  let gram := Motif.below (raw ∘ rowWire) (2^n)
  let maskProd := zeroWords fun i j => raw (exponentWire (prod i) j)
  let maskMotif := zeroWords fun i j => raw (exponentWire (localMap i) j)
  let maskAll := zeroWords fun i j => raw (exponentWire i j)
  let padF := allZero (raw ∘ flagWire)
  let padU := allZero (raw ∘ choiceWire)
  let padM := allZero (raw ∘ motifWire)
  let pos := Expr.and (.input (.inr (.inl ()))) (.and maskMotif (.and padU padM))
  let neg := Expr.and (.input (.inr (.inr ()))) (.and maskAll (.and padF padM))
  let getRow := fun j : Fin q => OracleBinaryTarget.expr (raw ∘ rowWire) (2^n + j.val)
  let mt := Motif.expr tables getRow (fun i j => raw (exponentWire (localMap i) j)) (raw polarity) (raw ∘ motifWire)
  Expr.mux gram (Expr.mux (.input (raw polarity)) neg pos) (.and mt (.and maskProd (.and padF padU)))

/-- Use the actual grammar and clock circuits as shared subcircuits on the
same raw inputs. -/
noncomputable def frame (prod : Fin g → Fin t) (localMap : Fin m → Fin t)
    (tables : Fin q → Motif.Table m) (parse : Frame (ParseOracle.Input n t W flags) Unit)
    (path : Frame (Fin n ⊕ Fin clock) Unit) : Frame (Input n high t W flags clock motif) Unit :=
  let checks := parallel (parse.subst (Frame.initial parseWire)) (path.subst (Frame.initial pathWire))
  checks.withInput.step fun _ : Unit => finish prod localMap tables

private theorem frame_eval (prod : Fin g → Fin t) (localMap : Fin m → Fin t)
    (tables : Fin q → Motif.Table m) (parse : Frame (ParseOracle.Input n t W flags) Unit)
    (path : Frame (Fin n ⊕ Fin clock) Unit) (x : Input n high t W flags clock motif → Bool) :
    (frame prod localMap tables parse path).eval x () =
      (finish prod localMap tables).eval (Sum.elim x (Sum.elim
        (parse.eval (x ∘ parseWire)) (path.eval (x ∘ pathWire)))) := by
  rw [frame, Frame.step_eval]
  congr 1
  funext i
  rcases i with i | (i | i) <;> simp [Function.comp_def]
  all_goals
    congr 1
    funext j
    simp

private theorem all_false_iff {α : Type*} (f : α → Bool) : (∀ i, f i = false) ↔ f = fun _ => false :=
  funext_iff.symm

/-- On a grammar row the sign bit selects either the positive parse count or
the negative constant path count. -/
theorem eval_grammar (prod : Fin g → Fin t) (localMap : Fin m → Fin t)
    (tables : Fin q → Motif.Table m) (parse : Frame (ParseOracle.Input n t W flags) Unit)
    (path : Frame (Fin n ⊕ Fin clock) Unit) (negative : Bool) (row : ℕ) (hr : row < 2^n)
    (a : Fin t → ℕ) (ha : ∀ j, a j < 2^W) (f : Fin flags → Bool)
    (u : Fin clock → Bool) (b : Fin motif → Bool) :
    (frame (high := high) prod localMap tables parse path).eval (assignment negative row a f u b) () =
      if negative then
        path.eval (Sum.elim (fun j => row.testBit j.val) u) () &&
          decide ((∀ j, a j = 0) ∧ f = (fun _ => false) ∧ b = (fun _ => false))
      else
        parse.eval (Sum.elim (ParseOracle.query (fun j => row.testBit j.val) a W) f) () &&
          decide ((∀ j, a (localMap j) = 0) ∧ u = (fun _ => false) ∧ b = (fun _ => false)) := by
  have hfit := hr.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_add_right n high))
  rw [frame_eval, assign_parse, assign_path]
  simp only [finish, Expr.eval_mux]
  rw [Motif.below_eval _ _ row hfit _ (fun j => by simp)]
  simp only [hr, decide_true, ite_true, Expr.eval, Sum.elim_inl, Sum.elim_inr, assignment_polarity]
  rw [zeroWords_eval _ a ha _ (by simp), zeroWords_eval _ (fun i => a (localMap i)) (fun i => ha _) _ (by simp)]
  simp [allZero_eval, Function.comp_def, all_false_iff]

/-- On a fixed row the signed coefficient is counted by an unsigned witness
comparison. The two machine banks contribute their unique all-zero strings. -/
theorem eval_motif (prod : Fin g → Fin t) (localMap : Fin m → Fin t)
    (tables : Fin q → Motif.Table m) (parse : Frame (ParseOracle.Input n t W flags) Unit)
    (path : Frame (Fin n ⊕ Fin clock) Unit) (negative : Bool) (o : Fin q)
    (hr : 2^n + o.val < 2^(n+high)) (a : Fin t → ℕ) (ha : ∀ j, a j < 2^W) (f : Fin flags → Bool)
    (u : Fin clock → Bool) (v : Fin (2^motif)) :
    (frame (high := high) prod localMap tables parse path).eval
      (assignment negative (2^n+o.val) a f u (RAMSerialization.wordBits motif v)) () =
      decide (v.val < Motif.part negative (JointLabelSystem.FixedRows.tableLookup (tables o) (a ∘ localMap)) ∧
        (∀ i, a (prod i) = 0) ∧ f = (fun _ => false) ∧ u = (fun _ => false)) := by
  rw [frame_eval, assign_parse, assign_path]
  simp only [finish, Expr.eval_mux]
  rw [Motif.below_eval _ _ (2^n + o.val) hr _ (fun j => by simp)]
  simp only [Nat.not_lt_of_ge (Nat.le_add_right ..), decide_false, Bool.false_eq_true, ite_false, Expr.eval]
  rw [zeroWords_eval _ (fun i => a (prod i)) (fun i => ha _) _ (by simp)]
  rw [Motif.eval_selected _ _ _ _ _ o (a ∘ localMap) v.val (fun i => ha _) v.isLt _ ?_ ?_ ?_]
  · simp [allZero_eval, Function.comp_def, all_false_iff]
    rfl
  · intro j
    rw [OracleBinaryTarget.expr_eval _ _ (2^n + o.val) hr _ (by simp)]
    simp [Fin.ext_iff, eq_comm]
  · simp
  · intro j
    simpa using (LiveHeader.testBit_wordBits v j).symm

end JointScalar

end VPVNP
end Computability
end OAI
