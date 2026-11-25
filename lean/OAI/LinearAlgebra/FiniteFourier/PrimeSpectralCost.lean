import OAI.LinearAlgebra.FiniteFourier.PrimeEndpointCost
import OAI.LinearAlgebra.FiniteFourier.PrimeSpectrumEquiv

/-! # Converting a full work row and removing its quadratic chirps

The paired column coordinates pack into the digits of the ordinary positive-sign
transform. Negating the frequencies and multiplying by the inverse volume gives
the inverse conversion. For the product query, free input and output phases and
a swap of the output halves recover the unnormalized transform on every row.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

open scoped Classical

variable {ι : Type} [Fintype ι] {ℓ n f A F c s : ℕ} [NeZero ℓ]
variable {K : Type*} [CommRing K] {ζ : K}

/-- Pack two tuples of residues into a single tuple of standard digit representatives. -/
def primePackDigits (e : (ι ⊕ ι) ≃ Fin n) : PrimeSpectrumDigits ι ℓ ≃ (Fin n → Fin ℓ) :=
  (Equiv.sumArrowEquivProdArrow ι ι (ZMod ℓ)).symm.trans
    (e.arrowCongr (ZMod.finEquiv ℓ).toEquiv.symm)

private theorem digitRep_val (z : ZMod ℓ) : ((ZMod.finEquiv ℓ).symm z).val = z.val := by
  cases ℓ with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ _ => rfl

omit [Fintype ι] in
private theorem pack_inl (e : (ι ⊕ ι) ≃ Fin n) (x : PrimeSpectrumDigits ι ℓ) (i : ι) :
    (primePackDigits e x (e (.inl i))).val = (x.1 i).val := by
  obtain ⟨x,y⟩ := x
  simpa [primePackDigits, Equiv.arrowCongr] using digitRep_val (x i)

omit [Fintype ι] in
private theorem pack_inr (e : (ι ⊕ ι) ≃ Fin n) (x : PrimeSpectrumDigits ι ℓ) (i : ι) :
    (primePackDigits e x (e (.inr i))).val = (x.2 i).val := by
  obtain ⟨x,y⟩ := x
  simpa [primePackDigits, Equiv.arrowCongr] using digitRep_val (y i)

/-- In the packed coordinates the full spectral pairing is exactly the prime transform. -/
theorem primeTransform_packDigits (hζ : IsPrimitiveRoot ζ ℓ) (e : (ι ⊕ ι) ≃ Fin n)
    (x ω : PrimeSpectrumDigits ι ℓ) :
    primeTransform ℓ n ζ (primePackDigits e x) (primePackDigits e ω) =
      digitPhase hζ (primeSpectrumPair x ω) := by
  rw [primeTransform_apply, ← e.prod_comp, Fintype.prod_sum_type]
  simp only [pack_inl, pack_inr, primeSpectrumPair, Finset.sum_add_distrib,
    AddChar.map_add_eq_mul, digitPhase_sum]
  simp only [digitPhase_apply, ZMod.val_mul, ← pow_eq_pow_mod _ hζ.pow_eq_one]

private def digitOrdering (h : 2 * Fintype.card ι = n) : (ι ⊕ ι) ≃ Fin n :=
  Fintype.equivFinOfCardEq (by simpa [two_mul] using h)

omit [NeZero ℓ] in
private theorem pair_comm (x y : PrimeSpectrumDigits ι ℓ) :
    primeSpectrumPair x y = primeSpectrumPair y x := by
  unfold primeSpectrumPair
  simp only [mul_comm]

variable [Invertible (ℓ : K)]

/-- Conversion from ordinary to frequency coordinates uses one call for each f-digit axis. -/
theorem primeTemplate_spectral_forward (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ]
    (hsize : 2 * Fintype.card ι = A * f) :
    PrimeTemplateProgram ℓ f (ℓ ^ ((A-1)*f)) ζ
      (primeSpectrumEquiv (ι := ι) hζ).toLinearMap.toMatrix' 0 A := by
  let e := digitOrdering hsize
  let g (x : PrimeSpectrumDigits ι ℓ) := (primePackDigits e x, ())
  have p := primeTemplate_partialTransform (ℓ := ℓ) (f := f) (F := ℓ ^ ((A-1)*f)) ζ A Unit (fun _ => by simp)
  have h := p.submatrix g ⟨g, fun _ _ h => (primePackDigits e).injective (congrArg Prod.fst h)⟩
  convert h using 1
  ext o i
  change primeSpectrumEquiv hζ (Pi.single i 1) o =
    Matrix.blockDiagonal (fun _ : Unit => primeTransform ℓ (A*f) ζ) (g o) (g i)
  rw [primeSpectrumEquiv_apply]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, Matrix.blockDiagonal_apply, g]
  rw [pair_comm i o, primeTransform_packDigits]

/-- Negating the output and rescaling by the inverse volume gives the inverse
conversion for the same number of axis calls, including zero-dimensional rows. -/
theorem primeTemplate_spectral_inverse (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ]
    (hsize : 2 * Fintype.card ι = A * f) :
    PrimeTemplateProgram ℓ f (ℓ ^ ((A-1)*f)) ζ
      (primeSpectrumEquiv (ι := ι) hζ).symm.toLinearMap.toMatrix' 0 A := by
  let p := primeTemplate_spectral_forward hζ hsize
  let e := Equiv.neg (PrimeSpectrumDigits ι ℓ)
  have h := (p.reindex e (Equiv.refl _)).diagonal
    (fun _ => (⅟ (ℓ : K)) ^ (2 * Fintype.card ι)) (fun _ => (1 : K))
  convert h using 1
  ext o i
  change (primeSpectrumEquiv hζ).symm (Pi.single i 1) o =
    (⅟ (ℓ : K)) ^ (2 * Fintype.card ι) * (1 * primeSpectrumEquiv hζ (Pi.single i 1) (-o))
  rw [primeSpectrumEquiv_symm_apply, primeSpectrumEquiv_apply, one_mul]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  congr 2
  rw [pair_comm o i]
  unfold primeSpectrumPair
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  change -(i.1 j * o.1 j + i.2 j * o.2 j) = i.1 j * -(o.1 j) + i.2 j * -(o.2 j)
  ring

/-- Exponent of the diagonal chirp on one paired tuple. -/
def chirpArgument (x : PrimeSpectrumDigits ι ℓ) : ZMod ℓ := ∑ i, x.1 i * x.2 i

/-- Multiplying the two chirps by their inverse phases, undoing the volume
normalization, and exchanging output halves gives the bare transform entry. -/
theorem primeTupleKernelRing_removeChirps (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ]
    (e : (ι ⊕ ι) ≃ Fin n) (o i : PrimeSpectrumDigits ι ℓ) :
    ((ℓ : K) ^ Fintype.card ι * digitPhase hζ (chirpArgument o)) *
      (digitPhase hζ (chirpArgument i) * primeTupleKernelRing hζ i.1 i.2 o.1 o.2) =
    primeTransform ℓ n ζ (primePackDigits e o.swap) (primePackDigits e i) := by
  let ψ := digitPhase hζ
  have hinv (v : PrimeSpectrumDigits ι ℓ) : ψ (chirpArgument v) * ψ (-chirpArgument v) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hnorm : (ℓ : K) ^ Fintype.card ι * (⅟ (ℓ : K)) ^ Fintype.card ι = 1 := by
    rw [← mul_pow, mul_invOf_self, one_pow]
  rw [primeTupleKernelRing_eq_fourierPhase, primeTransform_packDigits, pair_comm o.swap i]
  change (_ * ψ (chirpArgument o)) * (ψ (chirpArgument i) *
    (_ * ψ (-chirpArgument i) * ψ (-chirpArgument o) * ψ (primeSpectrumPair i o.swap))) =
    ψ (primeSpectrumPair i o.swap)
  calc
    _ = ((ℓ : K) ^ Fintype.card ι * (⅟ (ℓ : K)) ^ Fintype.card ι) *
        (ψ (chirpArgument o) * ψ (-chirpArgument o)) *
        (ψ (chirpArgument i) * ψ (-chirpArgument i)) * ψ (primeSpectrumPair i o.swap) := by ring
    _ = _ := by rw [hnorm, hinv, hinv]; simp

/-- A simultaneous quadratic-kernel template gives the exact unnormalized
prime transform on the same batch with unchanged gate and axis-call budgets. -/
theorem primeTemplate_batchedTupleKernel {B : Type} [Fintype B] [DecidableEq B]
    (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ] (hsize : 2 * Fintype.card ι = n)
    (p : PrimeTemplateProgram ℓ f F ζ (Matrix.blockDiagonal (fun _ : B =>
      Matrix.of (fun o i : PrimeSpectrumDigits ι ℓ => primeTupleKernelRing hζ i.1 i.2 o.1 o.2))) c s) :
    PrimeTemplateProgram ℓ f F ζ (Matrix.blockDiagonal (fun _ : B => primeTransform ℓ n ζ)) c s := by
  let e := digitOrdering hsize
  let ei := (primePackDigits (ℓ := ℓ) e).prodCongr (Equiv.refl B)
  let eo := ((Equiv.prodComm _ _).trans (primePackDigits (ℓ := ℓ) e)).prodCongr (Equiv.refl B)
  let a (x : PrimeSpectrumDigits ι ℓ × B) := digitPhase hζ (chirpArgument x.1)
  let b (x : PrimeSpectrumDigits ι ℓ × B) := (ℓ : K) ^ Fintype.card ι * a x
  have q := (p.diagonal b a).reindex eo ei
  convert q using 1
  ext o i
  obtain ⟨⟨x,v⟩,rfl⟩ := eo.surjective o
  obtain ⟨⟨y,w⟩,rfl⟩ := ei.surjective i
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.of_apply,
    Matrix.blockDiagonal_apply]
  change (if v = w then primeTransform ℓ n ζ (primePackDigits e x.swap) (primePackDigits e y) else 0) =
    b (x,v) * (a (y,w) * if v = w then primeTupleKernelRing hζ y.1 y.2 x.1 x.2 else 0)
  split_ifs
  · exact (primeTupleKernelRing_removeChirps hζ e x y).symm
  · simp

/-- Free monomial maps also recover a simultaneous bare transform from
a batch of quadratic-kernel binary circuits at their original size. -/
theorem realizableAtMost_batchedTupleKernel {B : Type} [Fintype B] [DecidableEq B]
    (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ] (hsize : 2 * Fintype.card ι = n)
    (p : RealizableAtMost (Matrix.blockDiagonal (fun _ : B =>
      Matrix.of (fun o i : PrimeSpectrumDigits ι ℓ => primeTupleKernelRing hζ i.1 i.2 o.1 o.2))) c) :
    RealizableAtMost (Matrix.blockDiagonal (fun _ : B => primeTransform ℓ n ζ)) c := by
  simpa using (primeTemplate_batchedTupleKernel (f := 0) (F := 0) hζ hsize (.localCircuit p)).compile

end

end

end FiniteFourier
end LinearAlgebra
end OAI
