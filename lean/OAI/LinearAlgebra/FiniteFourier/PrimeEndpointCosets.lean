import Mathlib.Algebra.Group.AddChar
import OAI.LinearAlgebra.FiniteFourier.CircuitReindex

/-! # Changing representatives at a partial Fourier endpoint

Two direct-sum charts agreeing on the summation subgroup parameterize the same
cosets. Changing charts permutes the cosets and multiplies each partial Fourier
coefficient by a character value. No nondegeneracy of a form on the summation
subgroup is needed.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {V H C C' : Type*} [AddCommGroup V] [AddCommGroup H]
  [AddCommGroup C] [AddCommGroup C']
variable (e : H × C ≃+ V) (e' : H × C' ≃+ V)

/-- The coordinates in the first chart of a representative from the second chart. -/
def endpointRepresentative (c' : C') : H × C := e.symm (e' (0, c'))

private theorem endpoint_chart_change
    (he : ∀ h, e' (h, 0) = e (h, 0)) (h : H) (c' : C') :
    e.symm (e' (h, c')) = (h + (endpointRepresentative e e' c').1,
      (endpointRepresentative e e' c').2) := by
  calc
    _ = e.symm (e' (h, 0) + e' (0, c')) := by rw [← map_add]; simp
    _ = _ := by rw [map_add, he, e.symm_apply_apply]; ext <;> simp [endpointRepresentative]

/-- The permutation of cosets obtained by changing direct-sum charts. -/
def endpointCosetEquiv (he : ∀ h, e' (h, 0) = e (h, 0)) : C' ≃ C where
  toFun c' := (endpointRepresentative e e' c').2
  invFun c := (endpointRepresentative e' e c).2
  left_inv c' := by
    have h := congrArg Prod.snd (endpoint_chart_change e' e (fun h => (he h).symm)
      (endpointRepresentative e e' c').1 (endpointRepresentative e e' c').2)
    simpa [endpointRepresentative] using h.symm
  right_inv c := by
    have h := congrArg Prod.snd (endpoint_chart_change e e' he
      (endpointRepresentative e' e c).1 (endpointRepresentative e' e c).2)
    simpa [endpointRepresentative] using h.symm

variable {K : Type*} [CommSemiring K] [Fintype H]

/-- Positive-sign partial Fourier coefficient along one coset in a direct-sum chart. -/
def endpointCosetFourier (χ : AddChar H K) (f : V → K) (c : C) : K :=
  ∑ h : H, χ h * f (e (h, c))

/-- A change of representatives contributes the negative translation phase to
the positive-sign Fourier coefficient and permutes its coset coordinate. -/
theorem endpointCosetFourier_change (he : ∀ h, e' (h, 0) = e (h, 0))
    (χ : AddChar H K) (f : V → K) (c' : C') :
    endpointCosetFourier e' χ f c' =
      χ (-(endpointRepresentative e e' c').1) *
        endpointCosetFourier e χ f (endpointCosetEquiv e e' he c') := by
  let d := (endpointRepresentative e e' c').1
  unfold endpointCosetFourier
  rw [Finset.mul_sum]
  apply Fintype.sum_equiv (Equiv.addRight d)
  intro h
  have heq := congrArg e (endpoint_chart_change e e' he h c')
  rw [e.apply_symm_apply] at heq
  change _ = χ (-d) * (χ (h + d) * f (e (h + d, (endpointRepresentative e e' c').2)))
  rw [heq, ← mul_assoc, ← AddChar.map_add_eq_mul]
  simp [add_comm (-d), d]

/-- Choosing different coordinates on the summation subgroup reindexes the
frequency by precomposition with the coordinate isomorphism. -/
theorem endpointCosetFourier_reindex {H' : Type*} [AddCommGroup H'] [Fintype H']
    (b : H' ≃+ H) (χ : AddChar H K) (f : V → K) (c : C) :
    endpointCosetFourier ((b.prodCongr (AddEquiv.refl C)).trans e)
      (χ.compAddMonoidHom b.toAddMonoidHom) f c = endpointCosetFourier e χ f c :=
  Fintype.sum_equiv b.toEquiv _ _ fun _ => rfl

/-- A diagonal depending only on the coset can be applied after the endpoint. -/
theorem endpointCosetFourier_mul_coset (q : C → K) (χ : AddChar H K) (f : V → K) (c : C) :
    endpointCosetFourier e χ (fun v => q (e.symm v).2 * f v) c =
      q c * endpointCosetFourier e χ f c := by
  simp [endpointCosetFourier, Finset.mul_sum, mul_left_comm]

variable {F : Type*}

open scoped Classical in
/-- Ordinary-coordinate matrix of the partial endpoint, for any family of frequencies. -/
noncomputable def endpointCosetMatrix (χ : F → AddChar H K) : Matrix (F × C) V K :=
  Matrix.of fun o v => if (e.symm v).2 = o.2 then χ o.1 (e.symm v).1 else 0

/-- The matrix acts on a complete ordinary-coordinate array by partial Fourier summation. -/
theorem endpointCosetMatrix_mulVec [Fintype V] [Fintype C]
    (χ : F → AddChar H K) (f : V → K) (o : F × C) :
    (endpointCosetMatrix e χ).mulVec f o = endpointCosetFourier e (χ o.1) f o.2 := by
  classical
  change (∑ v : V, (endpointCosetMatrix e χ o v) * f v) = _
  rw [← e.toEquiv.sum_comp, Fintype.sum_prod_type]
  simp [endpointCosetMatrix, endpointCosetFourier, ite_mul]

omit [Fintype H] in
/-- Entrywise form of the free output permutation and diagonal scaling. -/
theorem endpointCosetMatrix_change (he : ∀ h, e' (h, 0) = e (h, 0))
    (χ : F → AddChar H K) (o : F × C') (v : V) :
    endpointCosetMatrix e' χ o v = χ o.1 (-(endpointRepresentative e e' o.2).1) *
      endpointCosetMatrix e χ (o.1, endpointCosetEquiv e e' he o.2) v := by
  classical
  obtain ⟨⟨h,c⟩,rfl⟩ := e'.surjective v
  simp only [endpointCosetMatrix, Matrix.of_apply, e'.symm_apply_apply, endpoint_chart_change e e' he]
  by_cases hc : c = o.2
  · simp [hc, endpointCosetEquiv, ← AddChar.map_add_eq_mul]
  · have hne : (endpointRepresentative e e' c).2 ≠ (endpointRepresentative e e' o.2).2 :=
      (endpointCosetEquiv e e' he).injective.ne hc
    simp [hc, endpointCosetEquiv, hne]


section Circuit

variable {L : Type*} [CommSemiring L]

omit [Fintype H] in
/-- Changing both complement and representatives preserves every gate-count bound. -/
theorem endpointCosetMatrix_change_realizable (he : ∀ h, e' (h, 0) = e (h, 0))
    (χ : F → AddChar H L) {s : ℕ} (hc : RealizableAtMost (endpointCosetMatrix e χ) s) :
    RealizableAtMost (endpointCosetMatrix e' χ) s := by
  let p := (Equiv.refl F).prodCongr (endpointCosetEquiv e e' he)
  let q (o : F × C') := χ o.1 (-(endpointRepresentative e e' o.2).1)
  convert (hc.reindex p.symm (Equiv.refl V)).diagonal q (fun _ => 1) using 1
  ext ⟨x,c⟩ v
  simpa [p, q] using endpointCosetMatrix_change e e' he χ (x,c) v

end Circuit

end FiniteFourier
end LinearAlgebra
end OAI
