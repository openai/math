import Mathlib.Algebra.BigOperators.Fin

/-! # Consecutive public cable intervals within each ordered label pair

Cables are numbered in their public order. A cable starts after the sum of
all earlier widths in its bin. The occupied positions are exactly the initial
interval of length equal to the bin's total width, including zero-width bins.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical

variable {P : Type*} [DecidableEq P] {m : ℕ}

/-- Width contributed by a cable to a specified bin. -/
def binWidth (pair : Fin m → P) (width : Fin m → ℕ) (u : P) (e : Fin m) : ℕ :=
  if pair e = u then width e else 0

/-- Total live bit width in one ordered-label bin. -/
def load (pair : Fin m → P) (width : Fin m → ℕ) (u : P) : ℕ :=
  ∑ e, binWidth pair width u e

/-- Start of a cable's interval, summed in the original cable order. -/
def intervalStart (pair : Fin m → P) (width : Fin m → ℕ) (e : Fin m) : ℕ :=
  ∑ i : Fin e.val, binWidth pair width (pair e) (Fin.castLE e.isLt.le i)

private theorem has_bin (pair : Fin m → P) (width : Fin m → ℕ) (u : P) (e : Fin m)
    (j : Fin (binWidth pair width u e)) : pair e = u := by
  by_contra h
  have hj := j.isLt
  simp [binWidth,h] at hj

private def binEquiv (pair : Fin m → P) (width : Fin m → ℕ) :
    ((e : Fin m) × Fin (width e)) ≃ ((u : P) × (e : Fin m) × Fin (binWidth pair width u e)) where
  toFun x := ⟨pair x.1, x.1, ⟨x.2.val, by simp [binWidth]⟩⟩
  invFun x := ⟨x.2.1, ⟨x.2.2.val, by
    have he := has_bin pair width x.1 x.2.1 x.2.2
    simpa [binWidth, he] using x.2.2.isLt⟩⟩
  left_inv := fun _ => rfl
  right_inv := by
    rintro ⟨u,e,j⟩
    obtain rfl := has_bin pair width u e j
    rfl

/-- Assign a live bit its bin and within-bin ordinal, bijectively. -/
def liveOrdinal (pair : Fin m → P) (width : Fin m → ℕ) :
    ((e : Fin m) × Fin (width e)) ≃ ((u : P) × Fin (load pair width u)) :=
  (binEquiv pair width).trans (Equiv.sigmaCongrRight fun _ => finSigmaFinEquiv)

/-- Embed the occupied prefix of each bin into its padded physical interval. -/
def slotEmbedding (pair : Fin m → P) (width : Fin m → ℕ) (blocks bc : ℕ)
    (hload : ∀ u, load pair width u ≤ blocks*bc) :
    ((e : Fin m) × Fin (width e)) ↪ P × Fin (blocks*bc) where
  toFun x := let y := liveOrdinal pair width x
             (y.1, Fin.castLE (hload y.1) y.2)
  inj' := by
    intro x y eqn
    apply (liveOrdinal pair width).injective
    rcases hx : liveOrdinal pair width x with ⟨a,i⟩
    rcases hy : liveOrdinal pair width y with ⟨b,j⟩
    dsimp only at eqn
    rw [hx,hy] at eqn
    obtain rfl : a = b := congrArg Prod.fst eqn
    have hij : i = j := Fin.ext (congrArg (fun q => q.2.val) eqn)
    subst j
    rfl

/-- The cable interval begins at the public width prefix; its bits are consecutive. -/
theorem slotEmbedding_address (pair : Fin m → P) (width : Fin m → ℕ) (blocks bc : ℕ)
    (hload : ∀ u, load pair width u ≤ blocks*bc) (e : Fin m) (j : Fin (width e)) :
    let z := slotEmbedding pair width blocks bc hload ⟨e,j⟩
    z.1 = pair e ∧ z.2.val = intervalStart pair width e + j.val := by
  refine ⟨rfl, ?_⟩
  apply finSigmaFinEquiv_apply (n := binWidth pair width (pair e))

/-- Occupancy in every bin is exactly the initial segment of its padded slots. -/
theorem mem_range_slotEmbedding_iff (pair : Fin m → P) (width : Fin m → ℕ) (blocks bc : ℕ)
    (hload : ∀ u, load pair width u ≤ blocks*bc) (u : P) (j : Fin (blocks*bc)) :
    (u,j) ∈ Set.range (slotEmbedding pair width blocks bc hload) ↔ j.val < load pair width u := by
  constructor
  · rintro ⟨x, eqn⟩
    have hf : (liveOrdinal pair width x).1 = u := congrArg Prod.fst eqn
    have hj : (liveOrdinal pair width x).2.val = j.val := congrArg (fun y => y.2.val) eqn
    rw [← hj, ← hf]
    exact (liveOrdinal pair width x).2.isLt
  · intro h
    let y : (v : P) × Fin (load pair width v) := ⟨u, ⟨j.val,h⟩⟩
    refine ⟨(liveOrdinal pair width).symm y, ?_⟩
    apply Prod.ext
    · change (liveOrdinal pair width ((liveOrdinal pair width).symm y)).1 = u
      rw [Equiv.apply_symm_apply]
    · apply Fin.ext
      change (liveOrdinal pair width ((liveOrdinal pair width).symm y)).2.val = j.val
      rw [Equiv.apply_symm_apply]

end Cube.Physical

end BorderVNP
end Computability
end OAI
