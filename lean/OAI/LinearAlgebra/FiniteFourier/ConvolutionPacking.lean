import OAI.LinearAlgebra.FiniteFourier.OpenConvolution
import Mathlib.RingTheory.PowerBasis
import Mathlib.RingTheory.AlgebraTower

/-! # Packing ordinary convolution into a cyclic jet algebra

The three indices enumerate powers of a cyclotomic generator, the truncated
jet variable, and the cyclic variable. Inputs use only the lower half of each
range. Products of occupied monomials stay inside the basis, and coordinates
of equal mixed-radix address are added to recover the ordinary convolution.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

/-- The number of occupied input positions along an axis of length `k`. -/
def halfRadix (k : ℕ) : ℕ := (k + 1) / 2

private lemma halfRadix_pos {k : ℕ} (hk : 0 < k) : 0 < halfRadix k := by unfold halfRadix; omega

private lemma halfRadix_le (k : ℕ) : halfRadix k ≤ k := by unfold halfRadix; omega

/-- The lower halves have room for the prescribed input length. -/
theorem halfRadix_capacity {n e r N : ℕ} (hcap : 8*n ≤ e*r*N) :
    n ≤ halfRadix e * halfRadix r * halfRadix N := by
  have h (k : ℕ) : k ≤ 2*halfRadix k := by unfold halfRadix; omega
  have h₁ := Nat.mul_le_mul (Nat.mul_le_mul (h e) (h r)) (h N)
  nlinarith only [hcap,h₁]

private abbrev Address (e r N : ℕ) := Fin e × Fin r × Fin N

/-- The ordinary output index is the weighted sum of the three basis indices. -/
def packingAddress (e r : ℕ) {e' r' N' : ℕ} (v : Fin e' × Fin r' × Fin N') : ℕ :=
  v.1.val + halfRadix e * v.2.1.val + (halfRadix e * halfRadix r) * v.2.2.val

private def unpackDigits {n e r N : ℕ} (he : 0 < e) (hr : 0 < r)
    (hcap : n ≤ halfRadix e * halfRadix r * halfRadix N) (i : Fin n) :
    Address (halfRadix e) (halfRadix r) (halfRadix N) :=
  ⟨⟨i.val % halfRadix e, Nat.mod_lt _ (halfRadix_pos he)⟩,
   ⟨(i.val / halfRadix e) % halfRadix r, Nat.mod_lt _ (halfRadix_pos hr)⟩,
   ⟨(i.val / halfRadix e) / halfRadix r, by
     rw [Nat.div_lt_iff_lt_mul (halfRadix_pos hr), Nat.div_lt_iff_lt_mul (halfRadix_pos he)]
     exact i.isLt.trans_le ((hcap).trans_eq (by ring))⟩⟩

private lemma packingAddress_unpackDigits {n e r N : ℕ} (he : 0 < e) (hr : 0 < r)
    (hcap : n ≤ halfRadix e * halfRadix r * halfRadix N) (i : Fin n) :
    packingAddress e r (unpackDigits he hr hcap i) = i.val := by
  dsimp [packingAddress, unpackDigits]
  rw [Nat.mul_assoc, Nat.add_assoc, ← Nat.mul_add, Nat.mod_add_div, Nat.mod_add_div]

private def widenDigits {e r N : ℕ} (v : Address (halfRadix e) (halfRadix r) (halfRadix N)) :
    Address e r N :=
  ⟨Fin.castLE (halfRadix_le e) v.1, Fin.castLE (halfRadix_le r) v.2.1, Fin.castLE (halfRadix_le N) v.2.2⟩

private def addHalfDigits {k : ℕ} (a b : Fin (halfRadix k)) : Fin k :=
  ⟨a.val+b.val, by have ha := a.isLt; have hb := b.isLt; unfold halfRadix at *; omega⟩

private def addDigits {e r N : ℕ} (v w : Address (halfRadix e) (halfRadix r) (halfRadix N)) :
    Address e r N := ⟨addHalfDigits v.1 w.1, addHalfDigits v.2.1 w.2.1, addHalfDigits v.2.2 w.2.2⟩

private lemma packingAddress_addDigits {e r N : ℕ}
    (v w : Address (halfRadix e) (halfRadix r) (halfRadix N)) :
    packingAddress e r (addDigits v w) = packingAddress e r v + packingAddress e r w := by
  dsimp [packingAddress, addDigits, addHalfDigits]
  ring

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {n e r N : ℕ}

/-- Inject an ordinary input index into the lower halves of the three axes. -/
def packingInputPosition (he : 0 < e) (hr : 0 < r) (hcap : 8*n ≤ e*r*N) :
    Fin n ↪ (Fin e × Fin r × Fin N) where
  toFun i := widenDigits (unpackDigits he hr (halfRadix_capacity hcap) i)
  inj' i j h := by
    have hh := congrArg (packingAddress e r) h
    change packingAddress e r (unpackDigits he hr (halfRadix_capacity hcap) i) = packingAddress e r (unpackDigits he hr (halfRadix_capacity hcap) j) at hh
    simpa only [packingAddress_unpackDigits, Fin.val_inj] using hh

/-- The shared input packing in the three power coordinates. -/
def packConvolutionInput (b : Module.Basis (Fin e × Fin r × Fin N) R A)
    (he : 0 < e) (hr : 0 < r) (hcap : 8*n ≤ e*r*N) (x : Fin n → R) : A :=
  ∑ i, x i • b (packingInputPosition he hr hcap i)

/-- Gather every coefficient at a given ordinary output index, including carry
collisions between different full-size basis indices. -/
def gatherConvolutionOutput (b : Module.Basis (Fin e × Fin r × Fin N) R A) (k : ℕ) : A →ₗ[R] R :=
  ∑ p : Address e r N, if packingAddress e r p = k then b.coord p else 0

private theorem gather_basis (b : Module.Basis (Fin e × Fin r × Fin N) R A) (k : ℕ) (p : Address e r N) :
    gatherConvolutionOutput b k (b p) = if packingAddress e r p = k then 1 else 0 := by
  classical
  unfold gatherConvolutionOutput
  rw [LinearMap.sum_apply, Finset.sum_eq_single p]
  · split <;> simp_all [Module.Basis.coord_apply]
  · intro j _ hj
    split <;> simp_all [Module.Basis.coord_apply]
  · simp

/-- On three power bases the only multiplications performed during packing
remain below every relation. This applies directly to the cyclotomic, jet,
and cyclic powers, even when their unused high coordinates satisfy relations. -/
theorem gather_packed_product (b : Module.Basis (Fin e × Fin r × Fin N) R A)
    (u v w : A) (hb : ∀ i, b i = u^i.1.val * v^i.2.1.val * w^i.2.2.val)
    (he : 0 < e) (hr : 0 < r) (hcap : 8*n ≤ e*r*N) (x y : Fin n → R) (k : Fin (2*n-1)) :
    gatherConvolutionOutput b k
      (packConvolutionInput b he hr hcap x * packConvolutionInput b he hr hcap y) =
      openConv R n x y k := by
  classical
  let digits := unpackDigits he hr (halfRadix_capacity hcap)
  have hprod (i j : Fin n) : b (widenDigits (digits i)) * b (widenDigits (digits j)) =
      b (addDigits (digits i) (digits j)) := by
    simp only [hb, widenDigits, addDigits, addHalfDigits, Fin.val_castLE, pow_add]
    ring
  unfold packConvolutionInput openConv
  rw [Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_mul_smul_comm, map_smul, smul_eq_mul]
  change x i * y j * (gatherConvolutionOutput b k) (b (widenDigits (digits i)) * b (widenDigits (digits j))) = _
  rw [hprod, gather_basis, packingAddress_addDigits, packingAddress_unpackDigits,
    packingAddress_unpackDigits]
  split <;> simp_all

section Tower

variable {S J : Type*} [CommRing S] [CommRing J] [Nontrivial S] [Nontrivial J] [Algebra R S]
  [Algebra S J] [Algebra S A] [Algebra J A] [IsScalarTower R S A] [IsScalarTower S J A]

/-- In a tower of monogenic algebras the three standard power bases give
exactly the monomials required by the packing theorem. -/
theorem gather_packed_powerBasis (b : PowerBasis R S) (c : PowerBasis S J)
    (d : PowerBasis J A) (hcap : 8*n ≤ b.dim*c.dim*d.dim)
    (x y : Fin n → R) (k : Fin (2*n-1)) :
    let basis := b.basis.smulTower (c.basis.smulTower d.basis)
    gatherConvolutionOutput basis k
      (packConvolutionInput basis b.dim_pos c.dim_pos hcap x *
       packConvolutionInput basis b.dim_pos c.dim_pos hcap y) = openConv R n x y k := by
  apply gather_packed_product _ (algebraMap S A b.gen) (algebraMap J A c.gen) d.gen
  intro i
  simp only [Module.Basis.smulTower_apply, PowerBasis.basis_eq_pow, Algebra.smul_def, map_pow]
  ring

end Tower

end

end FiniteFourier
end LinearAlgebra
end OAI
