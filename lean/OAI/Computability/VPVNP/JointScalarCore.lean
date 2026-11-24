import OAI.Computability.VPVNP.ParseOracleResources
import OAI.Computability.VPVNP.LiveHeaderBits

/-!
# Gates and bit addresses of the joint scalar query

The input contains the sign selector, the unsigned equation address, and one
fixed-width exponent per formal coordinate. Witnesses for the parse, the
clocked computation, and the fixed motif comparison occupy separate banks.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace JointScalar

open VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr.eval Expr.size Expr.disjoin Expr.eval_disjoin_true Expr.size_disjoin_le Expr.input)

/-- Evaluate two verifier frames on a shared input and expose both sets of outputs, indexed by
their disjoint union. -/
noncomputable def parallel {X A B : Type*} [Fintype X] [Fintype A] [Fintype B]
    (p : Frame X A) (q : Frame X B) : Frame X (A ⊕ B) :=
  let retained := (q.subst (Frame.initial (Sum.inl : X → X ⊕ A))).withInput.subst p.withInput
  retained.select (Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr)

@[simp] theorem parallel_eval {X A B : Type*} [Fintype X] [Fintype A] [Fintype B]
    (p : Frame X A) (q : Frame X B) (x : X → Bool) (i : A ⊕ B) :
    (parallel p q).eval x i = Sum.elim (p.eval x) (q.eval x) i := by
  cases i with
  | inl i => simp [parallel]
  | inr i =>
    simp only [parallel, Frame.select_eval, Sum.elim_inr, Frame.subst_eval, Frame.withInput_eval_inr]
    congr 1
    funext j
    simp

@[simp] theorem parallel_size {X A B : Type*} [Fintype X] [Fintype A] [Fintype B]
    (p : Frame X A) (q : Frame X B) : (parallel p q).size = p.size + q.size := by simp [parallel]

/-- A linear-size conjunction checking that every specified bit is zero. -/
def allZero {X : Type*} {k : ℕ} (wire : Fin k → X) : Expr X :=
  .not (Expr.disjoin (List.ofFn fun j => .input (wire j)))

theorem allZero_eval {X : Type*} {k : ℕ} (wire : Fin k → X) (x : X → Bool) :
    (allZero wire).eval x = decide (∀ j, x (wire j) = false) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  rw [allZero, Expr.eval, Bool.not_eq_true', Bool.eq_false_iff]
  change ¬(_ = true) ↔ _
  rw [Expr.eval_disjoin_true]
  simp only [List.mem_ofFn, exists_exists_eq_and, Expr.eval, not_exists, Bool.not_eq_true]

theorem allZero_size {X : Type*} {k : ℕ} (wire : Fin k → X) :
    (allZero wire).size ≤ 2*k + 2 := by
  have h := Expr.size_disjoin_le (List.ofFn fun j => Expr.input (wire j)) 1 (by
    intro e he
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp he
    rfl)
  simp only [List.length_ofFn] at h
  change _ + 1 ≤ _
  omega

/-- Number of bits for the sign selector, equation address and fixed-width array of formal
exponents. -/
abbrev queryWidth (n high t W : ℕ) := 1 + ((n + high) + t * W)
/-- Combined width of the parse flags, clocked computation choices and motif coefficient
witness. -/
abbrev witnessWidth (flags clock motif : ℕ) := flags + (clock + motif)
/-- Input addresses of the signed coefficient checker, divided between the coefficient query
and its witness. -/
abbrev Input (n high t W flags clock motif : ℕ) :=
  Fin (queryWidth n high t W) ⊕ Fin (witnessWidth flags clock motif)

section

variable {n high t W flags clock motif : ℕ}

/-- First query wire, which selects the positive or negative part of the requested coefficient. -/
def polarity : Input n high t W flags clock motif := .inl 0

/-- Query wire carrying a specified little-endian bit of the joint equation address. -/
def rowWire (j : Fin (n + high)) : Input n high t W flags clock motif :=
  .inl ((j.castAdd (t*W)).natAdd 1)

/-- Query wire carrying bit `b` of the fixed-width exponent of formal label `j`. -/
def exponentWire (j : Fin t) (b : Fin W) : Input n high t W flags clock motif :=
  .inl (((finProdFinEquiv (j,b)).natAdd (n+high)).natAdd 1)

/-- Witness wire carrying one parse-event flag at the start of the witness array. -/
def flagWire (j : Fin flags) : Input n high t W flags clock motif := .inr (j.castAdd (clock+motif))
/-- Witness wire carrying one clocked machine choice after the parse-event flags. -/
def choiceWire (j : Fin clock) : Input n high t W flags clock motif := .inr ((j.castAdd motif).natAdd flags)
/-- Witness wire carrying one bit of the motif coefficient witness after the parse and
clocked-choice fields. -/
def motifWire (j : Fin motif) : Input n high t W flags clock motif := .inr ((j.natAdd clock).natAdd flags)

/-- Physical little-endian row and exponent words. The sign bit is the head. -/
def query (negative : Bool) (row : ℕ) (a : Fin t → ℕ) : Fin (queryWidth n high t W) → Bool :=
  Fin.append (fun _ : Fin 1 => negative)
    (Fin.append (fun j : Fin (n + high) => row.testBit j.val)
      (fun j : Fin (t*W) => (a (finProdFinEquiv.symm j).1).testBit (finProdFinEquiv.symm j).2.val))

/-- The physical witness bit string has the three banks in this order. -/
def witnesses (f : Fin flags → Bool) (u : Fin clock → Bool) (m : Fin motif → Bool) :
    Fin (witnessWidth flags clock motif) → Bool := Fin.append f (Fin.append u m)

/-- Supply the signed row and exponent query together with the parse, clock and motif witness
bits to the checker. -/
def assignment (negative : Bool) (row : ℕ) (a : Fin t → ℕ) (f : Fin flags → Bool)
    (u : Fin clock → Bool) (m : Fin motif → Bool) : Input n high t W flags clock motif → Bool :=
  Sum.elim (query negative row a) (witnesses f u m)

variable (negative : Bool) (row : ℕ) (a : Fin t → ℕ) (f : Fin flags → Bool)
  (u : Fin clock → Bool) (m : Fin motif → Bool)

@[simp] theorem assignment_polarity :
    assignment (n := n) (high := high) (W := W) negative row a f u m polarity = negative := rfl

@[simp] theorem assignment_rowWire (j : Fin (n+high)) :
    assignment (W := W) negative row a f u m (rowWire j) = row.testBit j.val := by
  simp [assignment, query, rowWire]

@[simp] theorem assignment_exponentWire (j : Fin t) (b : Fin W) :
    assignment (n := n) (high := high) negative row a f u m (exponentWire j b) = (a j).testBit b.val := by
  simp only [assignment, exponentWire, query, Sum.elim_inl, Fin.append_right, Equiv.symm_apply_apply]

@[simp] theorem assignment_flagWire (j : Fin flags) :
    assignment (n := n) (high := high) (W := W) negative row a f u m (flagWire j) = f j := by
  simp [assignment, witnesses, flagWire]

@[simp] theorem assignment_choiceWire (j : Fin clock) :
    assignment (n := n) (high := high) (W := W) negative row a f u m (choiceWire j) = u j := by
  simp [assignment, witnesses, choiceWire]

@[simp] theorem assignment_motifWire (j : Fin motif) :
    assignment (n := n) (high := high) (W := W) negative row a f u m (motifWire j) = m j := by
  simp [assignment, witnesses, motifWire]

end

/-- Split a sum over joint witnesses into three independent sums in physical
bit order. This permits zero padding on every inactive bank without changing
the number of accepted witnesses. -/
theorem sum_witnesses {a b c : ℕ} (p : (Fin (witnessWidth a b c) → Bool) → ℕ) :
    (∑ w, p w) = ∑ f : Fin a → Bool, ∑ u : Fin b → Bool, ∑ m : Fin c → Bool, p (witnesses f u m) := by
  let join (a b : ℕ) : ((Fin a → Bool) × (Fin b → Bool)) ≃ (Fin (a+b) → Bool) :=
    (Equiv.sumArrowEquivProdArrow (Fin a) (Fin b) Bool).symm.trans (finSumFinEquiv.arrowCongr (Equiv.refl _))
  have h (a b : ℕ) (f : Fin a → Bool) (u : Fin b → Bool) : join a b (f,u) = Fin.append f u := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [join]
  rw [← (join a (b+c)).sum_comp p, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro f _
  rw [← (join b c).sum_comp (fun w => p (join a (b+c) (f,w))), Fintype.sum_prod_type]
  simp only [h, witnesses]

end JointScalar

end VPVNP
end Computability
end OAI
