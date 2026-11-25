import OAI.Computability.BorderVNP.PackedDeckScoreSum

/-! # Fixed-width natural score expressions with shared binary multiplication

All operations compute their residues. Exact evaluation consequently requires
a capacity check only on the final result of the expression.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedDeckCandidate.Word

open PackedHistogram ParseBatchLookup ParseBatchSort VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

variable {σ I : Type*} [Fintype σ] [Fintype I] {w a : ℕ}

private theorem repack (v : Fin (w+a) → Bool) : prepend (v ∘ highPin w) (v ∘ lowPin a) = v := by
  induction a with
  | zero => rfl
  | succ a ih =>
    funext j
    refine Fin.cases rfl (fun i => ?_) j
    simpa [prepend, highPin, lowPin, Function.comp_def] using congrFun (ih (v ∘ Fin.succ)) i

/-- Discarding the high field computes reduction modulo the low word capacity. -/
theorem low_value (v : Fin (w+a) → Bool) :
    value (v ∘ lowPin a) = value v % 2^w := by
  have he := congrArg value (repack v)
  rw [value_prepend] at he
  rw [← he, Nat.mul_comm _ (2^w), Nat.mul_add_mod, Nat.mod_eq_of_lt (value_lt _)]

private theorem cast_value {s t : ℕ} (h : s=t) (v : Fin t → Bool) : value (v ∘ Fin.cast h) = value v := by
  subst t
  rfl

/-- Expose the low w bits of any sufficiently long word without adding a gate. -/
noncomputable def trim {s : ℕ} (h : w ≤ s) (f : Frame σ (Fin s)) : Frame σ (Fin w) :=
  f.select (Fin.cast (show w+(s-w)=s by omega) ∘ lowPin (s-w))

theorem trim_value {s : ℕ} (h : w ≤ s) (f : Frame σ (Fin s)) (x : σ → Bool) :
    value ((trim h f).eval x) = value (f.eval x) % 2^w := by
  let eq : w+(s-w)=s := by omega
  let v := f.eval x ∘ Fin.cast eq
  have hbit : (trim h f).eval x = v ∘ lowPin (s-w) := by
    funext j
    exact Frame.select_eval _ _ _ _
  rw [hbit, low_value, cast_value]

private def addExpr (w : ℕ) : Fin w → Expr (Fin w ⊕ Fin w) :=
  addWord (fun j => .input (.inl j)) (fun j => .input (.inr j))

private theorem add_value (x : Fin w ⊕ Fin w → Bool) :
    wordValue x (addExpr w) = (value (x ∘ Sum.inl) + value (x ∘ Sum.inr)) % 2^w := by
  let a : Fin w → Expr (Fin w ⊕ Fin w) := fun j => .input (.inl j)
  let b : Fin w → Expr (Fin w ⊕ Fin w) := fun j => .input (.inr j)
  have h := sumWord_value_carry x false a b
  change ((carryWord false a b).eval x).toNat*2^w + wordValue x (addExpr w) =
    value (x ∘ Sum.inl) + value (x ∘ Sum.inr) + 0 at h
  rw [Nat.add_zero] at h
  rw [← h, Nat.mul_comm _ (2^w), Nat.mul_add_mod]
  exact (Nat.mod_eq_of_lt (value_lt _)).symm

/-- A fixed arithmetic score expression over natural-valued fields. -/
inductive Formula (I : Type*) where
  | var (i : I) | num (n : ℕ) | add (a b : Formula I) | mul (a b : Formula I)

namespace Formula

/-- Unbounded natural semantics of the score expression. -/
def eval (x : I → ℕ) : Formula I → ℕ
  | .var i => x i | .num n => n | .add a b => a.eval x + b.eval x | .mul a b => a.eval x * b.eval x

omit [Fintype I] in
/-- Reducing all field inputs before arithmetic preserves the final residue. -/
theorem eval_mod (p : Formula I) (x : I → ℕ) (m : ℕ) :
    p.eval (fun i => x i % m) % m = p.eval x % m := by
  induction p with
  | var i => simp [eval]
  | num n => rfl
  | add a b ha hb =>
    simp only [eval]
    rw [Nat.add_mod, ha, hb, ← Nat.add_mod]
  | mul a b ha hb =>
    simp only [eval]
    rw [Nat.mul_mod, ha, hb, ← Nat.mul_mod]

/-- Number of nodes in the fixed scalar score formula. -/
def nodes : Formula I → ℕ
  | .var _ | .num _ => 1 | .add a b | .mul a b => a.nodes + b.nodes + 1

/-- Compile one arithmetic expression using a full-width local binary multiplier. -/
noncomputable def compile (mul : Frame (Fin w ⊕ Fin w) (Fin (2*w))) : Formula I → Frame (I × Fin w) (Fin w)
  | .var i => Frame.initial (fun j => (i,j))
  | .num n => (Frame.initial id).step (fixed ⟨n%2^w, Nat.mod_lt _ (Nat.two_pow_pos _)⟩)
  | .add a b => (Crossing.parallelFrame (a.compile mul) (b.compile mul)).step (addExpr w)
  | .mul a b => (trim (by omega : w ≤ 2*w) mul).subst (Crossing.parallelFrame (a.compile mul) (b.compile mul))

/-- The compiled expression gives the exact residue for every input, even if a subexpression overflows. -/
theorem compile_value (mul : Frame (Fin w ⊕ Fin w) (Fin (2*w)))
    (hm : ∀ x y, value (mul.eval (Sum.elim x y)) = value x * value y)
    (p : Formula I) (z : I × Fin w → Bool) :
    value ((p.compile mul).eval z) = p.eval (fun i => value (fun j => z (i,j))) % 2^w := by
  induction p with
  | var i =>
    have hz : (Frame.initial (fun j : Fin w => (i,j))).eval z = fun j => z (i,j) := funext (Frame.initial_eval _ _)
    simp [compile, hz, eval, Nat.mod_eq_of_lt (value_lt _)]
  | num n =>
    change value (fun j => ((Frame.initial id).step _).eval z j) = n%2^w
    simp only [Frame.step_eval, fixed, StatementCircuit.Expr.eval, ParseBatchCounts.value_encode]
  | add a b ha hb =>
    let t := (Crossing.parallelFrame (a.compile mul) (b.compile mul)).eval z
    have h := add_value t
    simp only [t, Function.comp_def, Crossing.parallelFrame_eval_inl, Crossing.parallelFrame_eval_inr, ha, hb] at h
    change value (fun j => ((Formula.add a b).compile mul).eval z j) = _
    simpa only [compile, Frame.step_eval, wordValue, eval, Nat.add_mod_mod, Nat.mod_add_mod] using h
  | mul a b ha hb =>
    let t := (Crossing.parallelFrame (a.compile mul) (b.compile mul)).eval z
    have he : t = Sum.elim ((a.compile mul).eval z) ((b.compile mul).eval z) := by
      funext j
      cases j <;> simp [t]
    have hz : ((Formula.mul a b).compile mul).eval z = (trim (by omega : w ≤ 2*w) mul).eval t :=
      funext fun j => Frame.subst_eval _ _ _ _
    rw [hz, trim_value, he, hm, ha, hb, Nat.mul_mod_mod, Nat.mod_mul_mod]
    rfl

/-- Word size times a local arithmetic cost bounds every node of a fixed expression. -/
theorem compile_size (mul : Frame (Fin w ⊕ Fin w) (Fin (2*w))) (p : Formula I) :
    (p.compile mul).size ≤ p.nodes * (mul.size + w*(16*w+22) + 1) := by
  induction p with
  | var i => simp [compile]
  | num n =>
    apply (Frame.step_size_le _ _ 1 (fun _ => le_rfl)).trans
    simp [nodes]
    nlinarith
  | add a b ha hb =>
    have h := Frame.step_size_le (Crossing.parallelFrame (a.compile mul) (b.compile mul)) (addExpr w) (16*w+22)
      (fun j => sumWord_size_le false _ _ 1 (fun _ => le_rfl) (fun _ => le_rfl) j)
    simp only [Crossing.parallelFrame_size, Fintype.card_fin] at h
    exact h.trans (by simp only [nodes, Nat.add_mul, Nat.one_mul]; omega)
  | mul a b ha hb =>
    simp only [compile, trim, Frame.subst_size, Frame.select_size, Crossing.parallelFrame_size, nodes, Nat.add_mul, Nat.one_mul]
    omega

end Formula
end PackedDeckCandidate.Word

end BorderVNP
end Computability
end OAI
