import OAI.ThreeFlat.Diagonal.RankDefect

namespace OAI
/-! # Entry evaluation by guesses at block boundaries

The evaluator guesses a fixing and a successor state for each block. On the
final block the boundary state is prescribed externally. The remaining
identity, touched-index tests and catalyst entry are all explicit.
-/

namespace ThreeFlat.Diagonal

variable {F I : Type*} [Field F] [Fintype I] [DecidableEq I] {T J : Type*}

/-- Weighted path expansion of the ordered block contraction. -/
noncomputable def evalBlocks (s : Finset J) (entry : T → J → I → I → F) :
    List T → I → I → F
  | [], x, y => if x = y then 1 else 0
  | t :: ts, x, y => ∑ j ∈ s, ∑ m, entry t j x m * evalBlocks s entry ts m y

theorem evalBlocks_eq_prod (steps : List T) (s : Finset J)
    (A : T → J → Matrix I I F) (x y : I) :
    evalBlocks s (fun t j x y => A t j x y) steps x y =
      (steps.map fun t => ∑ j ∈ s, A t j).prod x y := by
  classical
  induction steps generalizing x with
  | nil => simp [evalBlocks, Matrix.one_apply]
  | cons t rest ih =>
    simp only [evalBlocks, List.map_cons, List.prod_cons, Matrix.mul_apply, Matrix.sum_apply,
      Finset.sum_mul, ih]
    rw [Finset.sum_comm]

omit [Fintype I] [DecidableEq I] in
/-- Exact local summand for a fixed transition and fixing in the evaluation
of the approximant. -/
theorem fixingMatrix_apply {τ υ κ : Type*} [DecidableEq υ]
    (r c : I → (τ × υ) × κ) (u v : τ → F) (M : Matrix κ κ F) (x y : I) :
    fixingMatrix r c u v M x y =
      if (r x).1.2 = (c y).1.2 then
        u (r x).1.1 * v (c y).1.1 * M (r x).2 (c y).2 else 0 := by
  change (u _ * v _ * (1 : Matrix υ υ F) _ _) * M _ _ = _
  by_cases h : (r x).1.2 = (c y).1.2 <;> simp [Matrix.one_apply, h]

/-- End-to-end path evaluation, starting and finishing with the auxiliary
coordinates fixed by `external`. This is the scalar computed by the matrix
entry program in the diagonal approximation. -/
theorem eval_approximate_entry {τ υ κ γ : Type*} [DecidableEq υ]
    (steps : List T) (s : Finset J) (r c : T → J → I → (τ × υ) × κ)
    (u v : T → J → τ → F) (M : T → J → Matrix κ κ F) (external : γ → I) (x y : γ) :
    evalBlocks s (fun t j a b =>
      if (r t j a).1.2 = (c t j b).1.2 then
        u t j (r t j a).1.1 * v t j (c t j b).1.1 * M t j (r t j a).2 (c t j b).2
      else 0) steps (external x) (external y) =
        blockedComputation steps s r c u v M external x y := by
  simp_rw [← fixingMatrix_apply]
  exact evalBlocks_eq_prod _ _ _ _ _

end ThreeFlat.Diagonal

end OAI
