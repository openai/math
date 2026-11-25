import OAI.Hierarchy.GridLensWiring
import OAI.Hierarchy.GridSum
import OAI.Hierarchy.GridIdentity
import OAI.Hierarchy.GridLensWeights

namespace OAI
/-! # Pricing the two evaluations of the same selected wirings -/

namespace Hierarchy.UniversalGrid

open LinearAlgebra.SpectralBooks Filter
open scoped BigOperators Classical

abbrev Changed (L : ℕ) := {s : Finset (Fin L) // s ≠ ∅}

namespace Wiring

variable {E P : Type} {L : ℕ} {F : Type*} [Field F]

/-- The common scalar of the free bit equalities in a single hidden assignment. -/
noncomputable def wireWeight (W : Wiring E P L) (x : GridDiagonal.Pins E) (w : Bits W.internal) : F :=
  if ∀ uv ∈ W.equal, bit x w uv.1 = bit x w uv.2 then 1 else 0

/-- The summand of exact minus accelerated. Each changed cell contains the
local error and the remaining cells use the low-cost exact through factor. -/
noncomputable def errorTerm (W : Wiring E P L) (exact accelerated : (P → Bool) → F)
    (s : Changed L) (x : GridDiagonal.Pins E) : F :=
  -∑ w : Bits W.internal, W.wireWeight x w *
    ((∏ i ∈ s.val, (accelerated (fun j => bit x w (W.pin i j)) -
        exact (fun j => bit x w (W.pin i j)))) *
      ∏ i ∈ s.valᶜ, exact (fun j => bit x w (W.pin i j)))

theorem eval_difference (W : Wiring E P L) (exact accelerated : (P → Bool) → F)
    (x : GridDiagonal.Pins E) :
    W.eval exact x - W.eval accelerated x = ∑ s, W.errorTerm exact accelerated s x := by
  classical
  let base (h : Bits W.internal) (i : Fin L) := exact (fun j => bit x h (W.pin i j))
  let new (h : Bits W.internal) (i : Fin L) := accelerated (fun j => bit x h (W.pin i j))
  have extract (f : (P → Bool) → F) : W.eval f x = GridSum.contraction
      (W.wireWeight x) (fun h i => f (fun j => bit x h (W.pin i j))) := by
    unfold eval GridSum.contraction wireWeight
    apply Finset.sum_congr rfl
    intro w _
    split_ifs <;> simp
  rw [extract,extract, ←neg_sub (GridSum.contraction _ _) (GridSum.contraction _ _),
    GridSum.contraction_difference]
  simp only [errorTerm, Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr
  · apply congrArg (@Finset.univ (Changed L))
    exact Subsingleton.elim _ _
  · intro s _
    apply Finset.sum_congr
    · apply congrArg (@Finset.univ (Bits W.internal))
      exact Subsingleton.elim _ _
    · intro h _
      congr 1
      congr 1
      apply Finset.prod_congr
      · ext i
        simp only [Finset.mem_compl]
      · intro i _
        rfl

/-- Changing the sign of every coefficient amounts to one invertible local
operation on the grouped tensor, even in characteristic two. -/
theorem price_neg {I J : Type} [Fintype I] [Fintype J] [Nontrivial J]
    {M : Type*} [MetricSpace M] (P : SpectralPlacementPrices F M) (y : J ↪ M)
    (atSite : I → J) (f : (I → Bool) → F) :
    P.price (CorrectionProducts.raw (-f)) (y ∘ atSite) =
      P.price (CorrectionProducts.raw f) (y ∘ atSite) := by
  classical
  by_cases vanish : f = 0
  · simp [vanish]
  obtain ⟨φ, _, prices⟩ := P.normalized_group y
  rw [prices atSite _ (show -f ≠ 0 from neg_ne_zero.mpr vanish),prices atSite _ vanish]
  change _ * Real.logb 2 (CorrectionProducts.value φ atSite (-f) : ℝ) =
    _ * Real.logb 2 (CorrectionProducts.value φ atSite f : ℝ)
  rw [CorrectionProducts.value_neg]

/-- Exact-to-accelerated subtraction puts a single minus sign on the tensor
with the indicated error holes, independent of the characteristic. -/
theorem errorTerm_eq_neg_mixedEval (W : Wiring E P L) (exact accelerated : (P → Bool) → F)
    (s : Changed L) :
    W.errorTerm exact accelerated s =
      -(W.mixedEval (fun i => if i ∈ s.val then accelerated-exact else exact)) := by
  classical
  funext x
  change -(∑ _, _) = -(∑ _, _)
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  by_cases legal : ∀ uv ∈ W.equal, bit x h uv.1 = bit x h uv.2
  · simp only [wireWeight,ite_eq_left legal,one_mul]
    symm
    rw [← Finset.prod_mul_prod_compl s.val]
    congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      simp [hi]
    · apply Finset.prod_congr rfl
      intro i hi
      simp [Finset.mem_compl.mp hi]
  · simp only [wireWeight,ite_eq_right legal,zero_mul]

end Wiring

namespace Grid

variable {F : Type*} [Field F] {k : ℕ} (G : Grid F k)

noncomputable def errorTerm (a : Bits G.codeBits) (z : Bits G.selectorBits × Changed (G.g^k)) :
    GridDiagonal.Pins (Fin G.rails) → F :=
  fun x => (G.wiring a z.1).elim 0 (fun W => W.errorTerm G.exactCell G.replacement.coeff z.2 x)

theorem grid_difference (a : Bits G.codeBits) :
    G.exactGrid a - G.accelerated a = ∑ z, G.errorTerm a z := by
  classical
  funext x
  simp only [Pi.sub_apply,exactGrid,accelerated,← Finset.sum_sub_distrib,
    Finset.sum_apply,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  cases ws : G.wiring a s with
  | none => simp [row,errorTerm,ws]
  | some w => simpa [row,errorTerm,ws] using w.eval_difference G.exactCell G.replacement.coeff x

/-- The coarser lens estimate already gives the strict inequality used by the
self-programmed grid. Every zero term is allowed, even when the height
upper bound is negative. -/
theorem price_strict [Nonempty (Fin G.rails)] [Nontrivial (Fin k × Bool)]
    (P : SpectralPlacementPrices F (EuclideanSpace ℝ (Fin k))) (R D excess : ℝ)
    (hR : 0 < R) (a : Bits G.codeBits)
    (bound : ∀ z, G.errorTerm a z ≠ 0 →
      P.price (GridDiagonal.raw (G.errorTerm a z))
        (fun u => GridDiagonal.focus R (G.direction u.1,u.2)) ≤ 2*R*G.rails + excess-D)
    (margin : excess + 2*k*R*(G.selectorBits + (G.g^k : ℕ) : ℕ) < D) :
    G.exactGrid a - G.accelerated a = 0 ∨
      P.price (GridDiagonal.raw (G.exactGrid a - G.accelerated a))
        (fun u => GridDiagonal.focus R (G.direction u.1,u.2)) <
      P.price (GridDiagonal.raw (GridDiagonal.identity F))
        (fun u => GridDiagonal.focus R (G.direction u.1,u.2)) := by
  classical
  rw [G.grid_difference]
  by_cases nz : ∑ z, G.errorTerm a z = 0
  · exact Or.inl nz
  right
  let y : Fin k × Bool ↪ EuclideanSpace ℝ (Fin k) :=
    ⟨GridDiagonal.focus R,GridDiagonal.focus_injective hR⟩
  let atSite : GridDiagonal.Ends (Fin G.rails) → Fin k × Bool := fun u => (G.direction u.1,u.2)
  obtain ⟨z,nonzero,small⟩ := GridSum.price_sum P y atSite (G.errorTerm a) nz
  have count : Fintype.card (Bits G.selectorBits × Changed (G.g^k)) ≤ 2^(G.selectorBits+G.g^k) := by
    rw [Fintype.card_prod,pow_add]
    apply Nat.mul_le_mul
    · simp [Bits]
    · exact (Fintype.card_subtype_le _).trans (by simp)
  have pos : 0 < Fintype.card (Bits G.selectorBits × Changed (G.g^k)) := Fintype.card_pos_iff.mpr ⟨z⟩
  have logCount : Real.logb 2 (Fintype.card (Bits G.selectorBits × Changed (G.g^k))) ≤
      (G.selectorBits+G.g^k : ℕ) := by
    have length := Real.logb_le_logb_of_le (by norm_num : 1<(2:ℝ)) (by exact_mod_cast pos)
      (show (Fintype.card (Bits G.selectorBits × Changed (G.g^k)) : ℝ) ≤
        (2:ℝ)^(G.selectorBits+G.g^k) by exact_mod_cast count)
    simpa [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)] using length
  have charge := mul_le_mul_of_nonneg_left logCount (P.diagonal_pos y).le
  have star := mul_le_mul_of_nonneg_right (GridDiagonal.focus_scale P R hR.le)
    (Nat.cast_nonneg (α:=ℝ) (G.selectorBits+G.g^k))
  rw [GridDiagonal.identity_price P R hR.le G.direction]
  exact (small.trans (add_le_add (bound z nonzero) (charge.trans star))).trans_lt (by simpa only [Fintype.card_fin] using (show 2*R*G.rails+excess-D+2*k*R*(G.selectorBits+G.g^k : ℕ) < 2*R*G.rails by linarith))

end Grid
end Hierarchy.UniversalGrid

end OAI
