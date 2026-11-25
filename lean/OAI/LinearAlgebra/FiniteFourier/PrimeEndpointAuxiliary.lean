import OAI.LinearAlgebra.FiniteFourier.PrimeEndpointCosets
import OAI.LinearAlgebra.FiniteFourier.PrimeQueryProduct

/-! # Auxiliary Fourier endpoints independent of the selected digit

A partial transform along the auxiliary coordinates of both halves acts inside
every distinguished-digit fiber. The chirp on the selected distinguished
coordinates is constant inside that fiber, so it can be applied after the
partial Fourier sum.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

/-- The two halves of a digit array, with columns indexed by `C`. -/
abbrev EndpointDigitPairs (C I L : Type*) := (C → I → L) × (C → I → L)

variable {C J U L H R : Type*}

/-- Separate all distinguished coordinates from all auxiliary coordinates. -/
def endpointDigitSplit : EndpointDigitPairs C (J ⊕ U) L ≃
    EndpointDigitPairs C J L × EndpointDigitPairs C U L where
  toFun x := ((fun c j => x.1 c (.inl j), fun c j => x.2 c (.inl j)),
    (fun c u => x.1 c (.inr u), fun c u => x.2 c (.inr u)))
  invFun x := (fun c => Sum.elim (x.1.1 c) (x.2.1 c), fun c => Sum.elim (x.1.2 c) (x.2.2 c))
  left_inv x := by ext c i <;> cases i <;> rfl
  right_inv _ := rfl

/-- The common auxiliary chart keeps every distinguished coordinate intact. -/
def endpointAuxChart (e : EndpointDigitPairs C U L ≃ H × R) :
    EndpointDigitPairs C (J ⊕ U) L ≃ H × (EndpointDigitPairs C J L × R) where
  toFun x := ((e (endpointDigitSplit x).2).1, (endpointDigitSplit x).1,
    (e (endpointDigitSplit x).2).2)
  invFun x := endpointDigitSplit.symm (x.2.1, e.symm (x.1, x.2.2))
  left_inv x := by simp
  right_inv x := by simp

@[simp] theorem endpointAuxChart_apply (e : EndpointDigitPairs C U L ≃ H × R)
    (v : EndpointDigitPairs C (J ⊕ U) L) :
    endpointAuxChart e v = ((e (endpointDigitSplit v).2).1, (endpointDigitSplit v).1,
      (e (endpointDigitSplit v).2).2) := rfl

/-- At the selected query, retain its two distinguished column vectors and
place the other distinguished coordinates in a common order. -/
def endpointResidualQueryChart {m : ℕ} (j : Fin (m+1)) :
    EndpointDigitPairs C (Fin (m+1)) L × R ≃
      (((C → L) × (C → L)) × R) × EndpointDigitPairs C (Fin m) L where
  toFun x := (((fun c => x.1.1 c j, fun c => x.1.2 c j), x.2),
    fun c => j.removeNth (x.1.1 c), fun c => j.removeNth (x.1.2 c))
  invFun x := ((fun c => j.insertNth (x.1.1.1 c) (x.2.1 c),
    fun c => j.insertNth (x.1.1.2 c) (x.2.2 c)), x.1.2)
  left_inv x := by simp
  right_inv x := by simp

@[simp] theorem endpointResidualQueryChart_apply {m : ℕ} (j : Fin (m+1))
    (x : EndpointDigitPairs C (Fin (m+1)) L × R) :
    endpointResidualQueryChart j x =
      (((fun c => x.1.1 c j, fun c => x.1.2 c j), x.2),
        fun c i => x.1.1 c (j.succAbove i), fun c i => x.1.2 c (j.succAbove i)) := rfl

/-- Send the active coordinates to the physical space, leaving the spectator
coordinates in their common order. The two equivalences insert the same
distinguished coordinate and use the two paired bases on the auxiliary digits. -/
def endpointQueryPhysicalChart {m : ℕ} {E : Type*} (j : Fin (m+1))
    (p q : E ≃ L × (U → L)) :
    EndpointDigitPairs C (Fin (m+1) ⊕ U) L ≃
      ((C → E) × (C → E)) × EndpointDigitPairs C (Fin m) L :=
  endpointDigitSplit.trans ((endpointResidualQueryChart j).trans
    { toFun := fun x =>
        ((fun c => p.symm (x.1.1.1 c, x.1.2.1 c), fun c => q.symm (x.1.1.2 c, x.1.2.2 c)), x.2)
      invFun := fun x =>
        (((fun c => (p (x.1.1 c)).1, fun c => (q (x.1.2 c)).1),
          fun c => (p (x.1.1 c)).2, fun c => (q (x.1.2 c)).2), x.2)
      left_inv := by intro; simp
      right_inv := by intro; simp })

@[simp] theorem endpointQueryPhysicalChart_apply {m : ℕ} {E : Type*} (j : Fin (m+1))
    (p q : E ≃ L × (U → L)) (x : EndpointDigitPairs C (Fin (m+1) ⊕ U) L) :
    endpointQueryPhysicalChart j p q x =
      ((fun c => p.symm (x.1 c (.inl j), fun i => x.1 c (.inr i)),
        fun c => q.symm (x.2 c (.inl j), fun i => x.2 c (.inr i))),
        fun c i => x.1 c (.inl (j.succAbove i)), fun c i => x.2 c (.inl (j.succAbove i))) := rfl

/-- The exponent of the actual query is the sum of the common physical
pairings in the active column vectors. -/
theorem primeQueryExponent_physical {ℓ m : ℕ} {E : Type*} [Fintype C] [Fintype U]
    (j : Fin (m+1)) (p q : E ≃ ZMod ℓ × (U → ZMod ℓ)) (B : E → E → ZMod ℓ)
    (hpair : ∀ x y, B x y = (p x).1 * (q y).1 + ∑ i, (p x).2 i * (q y).2 i)
    (x : EndpointDigitPairs C (Fin (m+1) ⊕ U) (ZMod ℓ)) :
    primeQueryExponent x.1 x.2 j =
      ∑ c, B ((endpointQueryPhysicalChart j p q x).1.1 c)
        ((endpointQueryPhysicalChart j p q x).1.2 c) := by
  simp [primeQueryExponent, hpair]

section Additive

variable [AddCommGroup L] [AddCommGroup H] [AddCommGroup R]

/-- Extend an additive chart on the paired auxiliary array across all
distinguished digits. Its summation direction is independent of the query. -/
def endpointAuxAddChart (e : H × R ≃+ EndpointDigitPairs C U L) :
    H × (EndpointDigitPairs C J L × R) ≃+ EndpointDigitPairs C (J ⊕ U) L where
  toEquiv := (endpointAuxChart e.symm.toEquiv).symm
  map_add' x y := by
    apply endpointDigitSplit.injective
    apply Prod.ext
    · rfl
    · change e (x.1 + y.1, x.2.2 + y.2.2) = e (x.1, x.2.2) + e (y.1, y.2.2)
      exact map_add e (x.1, x.2.2) (y.1, y.2.2)

/-- Take the auxiliary splitting in each half of each column. The two halves
may use distinct coordinates on their summation and residual subspaces. -/
def endpointAuxPairedAddChart {H₁ H₂ R₁ R₂ : Type*} [AddCommGroup H₁] [AddCommGroup H₂]
    [AddCommGroup R₁] [AddCommGroup R₂] (p : H₁ × R₁ ≃+ (U → L)) (q : H₂ × R₂ ≃+ (U → L)) :
    (((C → H₁) × (C → H₂)) × ((C → R₁) × (C → R₂))) ≃+ EndpointDigitPairs C U L where
  toFun x := (fun c => p (x.1.1 c, x.2.1 c), fun c => q (x.1.2 c, x.2.2 c))
  invFun x := ((fun c => (p.symm (x.1 c)).1, fun c => (q.symm (x.2 c)).1),
    fun c => (p.symm (x.1 c)).2, fun c => (q.symm (x.2 c)).2)
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by
    apply Prod.ext
    · funext c
      exact map_add p (x.1.1 c, x.2.1 c) (y.1.1 c, y.2.1 c)
    · funext c
      exact map_add q (x.1.2 c, x.2.2 c) (y.1.2 c, y.2.2 c)

/-- Each partial coefficient of the full row is precisely the auxiliary
coefficient of its own distinguished-digit fiber. -/
theorem endpointAuxAddChart_fourier {K : Type*} [CommSemiring K] [Fintype H]
    (e : H × R ≃+ EndpointDigitPairs C U L) (χ : AddChar H K)
    (f : EndpointDigitPairs C (J ⊕ U) L → K) (d : EndpointDigitPairs C J L) (r : R) :
    endpointCosetFourier (endpointAuxAddChart e) χ f (d,r) =
      endpointCosetFourier e χ (fun v => f (endpointDigitSplit.symm (d,v))) r := rfl

open scoped Classical in
/-- The partial matrix is block diagonal across the distinguished digits,
even when the paired auxiliary coordinates in different halves use different bases. -/
theorem endpointAuxAddChart_matrix {K F : Type*} [CommSemiring K]
    (e : H × R ≃+ EndpointDigitPairs C U L) (χ : F → AddChar H K)
    (v : EndpointDigitPairs C (J ⊕ U) L) (o : F × (EndpointDigitPairs C J L × R)) :
    endpointCosetMatrix (endpointAuxAddChart e) χ o v =
      if (endpointDigitSplit v).1 = o.2.1 then
        endpointCosetMatrix e χ (o.1, o.2.2) (endpointDigitSplit v).2 else 0 := by
  classical
  have he : (endpointAuxAddChart (J := J) e).symm v =
      ((e.symm (endpointDigitSplit v).2).1, (endpointDigitSplit v).1,
        (e.symm (endpointDigitSplit v).2).2) := rfl
  rw [endpointCosetMatrix, Matrix.of_apply, he]
  rcases o with ⟨ω, d, r⟩
  simp only [Prod.mk.injEq, endpointCosetMatrix, Matrix.of_apply]
  split_ifs <;> simp_all

end Additive

section Chirp

variable {ℓ : ℕ} {K : Type*} [CommSemiring K] [Fintype C] [Fintype U]

/-- The selected digit contributes a diagonal depending only on the
distinguished spectator values of the auxiliary transform. -/
def endpointDistinguishedChirp (ψ : AddChar (ZMod ℓ) K) (a : ZMod ℓ) (j : J)
    (d : EndpointDigitPairs C J (ZMod ℓ)) : K := ψ (a * ∑ c, d.1 c j * d.2 c j)

/-- The initial and final auxiliary chirps use the same arrays for every query. -/
def endpointAuxChirp (ψ : AddChar (ZMod ℓ) K) (a : ZMod ℓ)
    (u : EndpointDigitPairs C U (ZMod ℓ)) : K := ψ (a * ∑ c, ∑ i, u.1 c i * u.2 c i)

/-- The ordinary query chirp separates into a distinguished factor and a
query-independent auxiliary factor. Use `a = -1 / power` at either endpoint. -/
theorem endpoint_query_chirp (ψ : AddChar (ZMod ℓ) K) (a : ZMod ℓ) (j : J)
    (x : EndpointDigitPairs C (J ⊕ U) (ZMod ℓ)) :
    ψ (a * primeQueryExponent x.1 x.2 j) =
      endpointDistinguishedChirp ψ a j (endpointDigitSplit x).1 *
      endpointAuxChirp ψ a (endpointDigitSplit x).2 := by
  rw [primeQueryExponent, Finset.sum_add_distrib, mul_add, AddChar.map_add_eq_mul]
  rfl

variable [AddCommGroup H] [AddCommGroup R] [Fintype H]

/-- Move the selected distinguished chirp past the partial transform. The
summed operator on each distinguished fiber depends on the power and auxiliary
chart alone, and therefore can be computed once for all query indices. -/
theorem endpointAuxFourier_query_chirp
    (e : H × R ≃+ EndpointDigitPairs C U (ZMod ℓ)) (χ : AddChar H K)
    (ψ : AddChar (ZMod ℓ) K) (a : ZMod ℓ) (j : J)
    (f : EndpointDigitPairs C (J ⊕ U) (ZMod ℓ) → K) (d : EndpointDigitPairs C J (ZMod ℓ)) (r : R) :
    endpointCosetFourier (endpointAuxAddChart e) χ
        (fun v => ψ (a * primeQueryExponent v.1 v.2 j) * f v) (d,r) =
      endpointDistinguishedChirp ψ a j d *
        endpointCosetFourier e χ (fun u => endpointAuxChirp ψ a u *
          f (endpointDigitSplit.symm (d,u))) r := by
  rw [endpointAuxAddChart_fourier]
  simp only [endpointCosetFourier, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  rw [endpoint_query_chirp]
  simp only [Equiv.apply_symm_apply]
  ac_rfl

/-- The endpoint used for every query, including its auxiliary chirp.
All distinguished coordinates pass through as spectators. -/
noncomputable def endpointSharedAuxMatrix {F : Type*}
    (e : H × R ≃+ EndpointDigitPairs C U (ZMod ℓ)) (χ : F → AddChar H K)
    (ψ : AddChar (ZMod ℓ) K) (a : ZMod ℓ) :
    Matrix (F × (EndpointDigitPairs C J (ZMod ℓ) × R)) (EndpointDigitPairs C (J ⊕ U) (ZMod ℓ)) K :=
  Matrix.of fun o v => endpointCosetMatrix (endpointAuxAddChart e) χ o v *
    endpointAuxChirp ψ a (endpointDigitSplit v).2

omit [Fintype H] in
/-- Entrywise factorization of the source endpoint. Transposition gives the
destination endpoint, placing the distinguished diagonal before the final
shared transposed transform. -/
theorem endpointSharedAuxMatrix_query {F : Type*}
    (e : H × R ≃+ EndpointDigitPairs C U (ZMod ℓ)) (χ : F → AddChar H K)
    (ψ : AddChar (ZMod ℓ) K) (a : ZMod ℓ) (j : J)
    (o : F × (EndpointDigitPairs C J (ZMod ℓ) × R)) (v : EndpointDigitPairs C (J ⊕ U) (ZMod ℓ)) :
    endpointCosetMatrix (endpointAuxAddChart e) χ o v * ψ (a * primeQueryExponent v.1 v.2 j) =
      endpointDistinguishedChirp ψ a j o.2.1 * endpointSharedAuxMatrix e χ ψ a o v := by
  classical
  rw [endpoint_query_chirp, endpointSharedAuxMatrix, Matrix.of_apply, endpointAuxAddChart_matrix]
  by_cases hd : (endpointDigitSplit v).1 = o.2.1
  · rw [hd, ite_eq_left rfl]
    ac_rfl
  · simp [hd]

end Chirp

end FiniteFourier
end LinearAlgebra
end OAI
