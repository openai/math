import OAI.LinearAlgebra.FiniteFourier.CharacterBasis

/-!
# Two character-table phases implement a weighted swap

A state is its coefficient function on the ordered pair of register labels.
Each local map below is a product of two invertible changes of coordinates.
The controlled phase acts diagonally by the entries of its matrix.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

section

variable {G K : Type*} [Field K]

/-- Apply a change of coordinates to the first register. -/
def onFirst (Q : (G → K) ≃ₗ[K] (G → K)) (v : G × G → K) (p : G × G) : K :=
  Q (fun x ↦ v (x, p.2)) p.1

/-- Apply a change of coordinates to the second register. -/
def onSecond (Q : (G → K) ≃ₗ[K] (G → K)) (v : G × G → K) (p : G × G) : K :=
  Q (fun y ↦ v (p.1, y)) p.2

/-- The product of independent maps on the two registers. -/
def localProduct (A B : (G → K) ≃ₗ[K] (G → K)) (v : G × G → K) : G × G → K :=
  onSecond B (onFirst A v)

/-- The controlled diagonal phase of a matrix. -/
def controlledPhase (M : Matrix G G K) (v : G × G → K) (p : G × G) : K :=
  M p.1 p.2 * v p

/-- Two occurrences of the indicated phase, interleaved with local products,
send each standard basis vector to a nonzero multiple of its swapped vector. -/
def TwoPhasesGiveWeightedSwap (M : Matrix G G K) : Prop :=
  ∃ (A₀ B₀ A₁ B₁ A₂ B₂ : (G → K) ≃ₗ[K] (G → K)) (w : G × G → Kˣ),
    ∀ (v : G × G → K) (p : G × G),
      localProduct A₂ B₂ (controlledPhase M
        (localProduct A₁ B₁ (controlledPhase M (localProduct A₀ B₀ v)))) p =
        (w p : K) * v p.swap

variable [Fintype G]

/-- Product maps acting on different registers commute. -/
theorem onSecond_onFirst (A B : (G → K) ≃ₗ[K] (G → K)) (v : G × G → K) :
    onSecond B (onFirst A v) = onFirst A (onSecond B v) := by
  classical
  have applyMatrix (Q : (G → K) ≃ₗ[K] (G → K)) (u : G → K) (i : G) :
      Q u i = ∑ j, Q.toLinearMap.toMatrix' i j * u j :=
    congrFun (LinearMap.toMatrix'_mulVec Q.toLinearMap u).symm i
  funext p
  simp only [onFirst, onSecond, applyMatrix A, applyMatrix B, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ mul_left_comm _ _ _

variable [AddCommGroup G]

omit [Fintype G] in
private theorem controlledAddition (Q : (G → K) ≃ₗ[K] (G → K)) (M : Matrix G G K)
    (hQ : ∀ (s : G) (u : G → K) y, Q (translate G K s u) y = M s y * Q u y)
    (v : G × G → K) :
    onSecond Q.symm (controlledPhase M (onSecond Q v)) = fun p ↦ v (p.1, p.2 - p.1) := by
  funext p
  have he := funext (hQ p.1 (fun y ↦ v (p.1, y)))
  change Q.symm (fun y ↦ M p.1 y * Q _ y) p.2 = _
  rw [← he, Q.symm_apply_apply]
  rfl

omit [Fintype G] in
private theorem controlledAddition_left (Q : (G → K) ≃ₗ[K] (G → K)) (M : Matrix G G K)
    (hM : ∀ x y, M x y = M y x)
    (hQ : ∀ (s : G) (u : G → K) y, Q (translate G K s u) y = M s y * Q u y)
    (v : G × G → K) :
    onFirst Q.symm (controlledPhase M (onFirst Q v)) = fun p ↦ v (p.1 - p.2, p.2) := by
  funext p
  have he := funext (hQ p.2 (fun x ↦ v (x, p.2)))
  change Q.symm (fun x ↦ M x p.2 * Q _ x) p.1 = _
  simp_rw [hM _ p.2]
  rw [← he, Q.symm_apply_apply]
  rfl

omit [AddCommGroup G] in
/-- Composition of two register products acts by composing the two maps on each register. -/
theorem localProduct_trans (A B C D : (G → K) ≃ₗ[K] (G → K)) (v : G × G → K) :
    localProduct (A.trans C) (B.trans D) v = localProduct C D (localProduct A B v) := by
  unfold localProduct
  rw [← onSecond_onFirst C B (onFirst A v)]
  rfl

omit [AddCommGroup G] in
/-- Independent row and column permutations can be absorbed in the neighboring
local changes of coordinates of both phases. -/
theorem TwoPhasesGiveWeightedSwap.reindex {M : Matrix G G K}
    (hM : TwoPhasesGiveWeightedSwap M) (a b : G ≃ G) :
    TwoPhasesGiveWeightedSwap (M.submatrix a b) := by
  obtain ⟨A₀, B₀, A₁, B₁, A₂, B₂, w, hw⟩ := hM
  let R := LinearEquiv.funCongrLeft K K a
  let S := LinearEquiv.funCongrLeft K K b
  have hconj (v : G × G → K) :
      controlledPhase (M.submatrix a b) (localProduct R S v) = localProduct R S (controlledPhase M v) := rfl
  have hinv (v : G × G → K) : localProduct R.symm S.symm (localProduct R S v) = v := by
    funext p
    change v (a (a.symm p.1), b (b.symm p.2)) = v p
    simp
  refine ⟨A₀.trans R, B₀.trans S, (R.symm.trans A₁).trans R, (S.symm.trans B₁).trans S,
    R.symm.trans A₂, S.symm.trans B₂, w, ?_⟩
  intro v p
  simp only [localProduct_trans, hconj, hinv, hw]

/-- A finite abelian character table, with its rows enumerated by a symmetric
identification with the dual, implements a weighted swap in exactly two phases.
This is Lemma `geo:swap`. -/
theorem twoPhases_fourier_weightedSwap (h : Admissible G K) :
    ∃ e : G ≃ Character G K, TwoPhasesGiveWeightedSwap ((fourierMatrix G K).submatrix e id) := by
  obtain ⟨e₀, hsymm⟩ := exists_symmetric_character_equiv G K h
  let e := Multiplicative.ofAdd.trans e₀.toEquiv
  let M := (fourierMatrix G K).submatrix e id
  let Q := (fourierEquiv G K h).trans (LinearEquiv.funCongrLeft K K e)
  let negR := LinearEquiv.funCongrLeft K K (Equiv.neg G)
  have hM : ∀ x y, M x y = M y x := fun x y ↦ congrArg (Units.val) (hsymm x y)
  have hQ (s : G) (u : G → K) (y : G) : Q (translate G K s u) y = M s y * Q u y := by
    change fourierEquiv G K h (translate G K s u) (e y) = M s y * fourierEquiv G K h u (e y)
    rw [fourierEquiv_translate, hM s y]
    rfl
  refine ⟨e, Q.symm, Q, negR.trans Q, Q.symm, Q.symm, Q,
    fun p ↦ e p.1 (Multiplicative.ofAdd p.2), ?_⟩
  intro v p
  let u := onFirst Q.symm v
  have hmid (w : G × G → K) :
      localProduct (negR.trans Q) Q.symm w = onFirst Q (onFirst negR (onSecond Q.symm w)) := by
    rw [localProduct, onSecond_onFirst]
    rfl
  change onSecond Q (onFirst Q.symm (controlledPhase M
    (localProduct (negR.trans Q) Q.symm (controlledPhase M (onSecond Q u))))) p =
    M p.1 p.2 * v p.swap
  rw [hmid, controlledAddition Q M hQ u, controlledAddition_left Q M hM hQ]
  have hperm : (fun y ↦ (onFirst negR (fun a : G × G ↦ u (a.1, a.2 - a.1)))
      (p.1 - y, y)) = translate G K p.1 (Q.symm (fun x ↦ v (x, p.1))) := by
    funext y
    change u (-(p.1 - y), y - -(p.1 - y)) = Q.symm (fun x ↦ v (x, p.1)) (y - p.1)
    rw [neg_sub, sub_sub_cancel]
    rfl
  change Q _ p.2 = _
  rw [hperm, hQ, Q.apply_symm_apply]
  rfl

/-- For every enumeration of a full character table the two phases give a
weighted swap, under the cardinal and invertibility hypotheses of the lemma. -/
theorem twoPhases_characterTable_weightedSwap
    (horder : (Fintype.card G : K) ≠ 0)
    (hfull : Fintype.card (Character G K) = Fintype.card G) (e : G ≃ Character G K) :
    TwoPhasesGiveWeightedSwap ((fourierMatrix G K).submatrix e id) := by
  obtain ⟨c, hc⟩ := twoPhases_fourier_weightedSwap ((admissible_iff_card_character G K).mpr ⟨horder, hfull⟩)
  have h := hc.reindex (e.trans c.symm) (Equiv.refl G)
  convert! h using 1
  ext i j
  simp [Matrix.submatrix_apply]

end

end

end FiniteFourier
end LinearAlgebra
end OAI
