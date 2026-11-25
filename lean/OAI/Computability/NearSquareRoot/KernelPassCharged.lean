import OAI.Computability.NearSquareRoot.KernelPassPartial

/-! # The binary common kernel on a charged rectangle

A fixed reference chart puts the two active halves and the spectators into
common coordinates. Each incidence changes to or from that chart freely.
In the common chart two quadratic signs enclose a partial Walsh transform
on exactly twice the common dimension.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.Charged

open OAI.LinearAlgebra.FiniteFourier Matrix Finset KernelNormalization SynchronizedPair
noncomputable section

abbrev F := ZMod 2
abbrev Common (V T : Type*) := PrimeCommonAddress (Fin 1) V T
variable {V T : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup T] [Module F T] {A D : ℕ}

private def paired (p q : V ≃ₗ[F] Bits D) :
    ((Fin 1 → V) × (Fin 1 → V)) ≃ₗ[F] Bits (D+D) :=
  (((LinearEquiv.funUnique (Fin 1) F V).trans p).prodCongr
    ((LinearEquiv.funUnique (Fin 1) F V).trans q)).trans (splitBits D D).symm

private def inputChart (p q : V ≃ₗ[F] Bits D) : Common V T ≃ₗ[F] Bits (D+D) × T :=
  (paired p q).prodCongr (LinearEquiv.refl F T)

private def outputChart (p q : V ≃ₗ[F] Bits D) : Common V T ≃ₗ[F] Bits (D+D) × T :=
  ((LinearEquiv.prodComm F _ _).trans (paired q p)).prodCongr (LinearEquiv.refl F T)

private theorem dot_charts (p q : V ≃ₗ[F] Bits D) (o i : Common V T) :
    ((outputChart p q) o).1 ⬝ᵥ ((inputChart p q) i).1 =
      (p (i.1.1 0) ⬝ᵥ q (o.1.2 0)) + (p (o.1.1 0) ⬝ᵥ q (i.1.2 0)) := by
  change Fin.append (q (o.1.2 0)) (p (o.1.1 0)) ⬝ᵥ
    Fin.append (p (i.1.1 0)) (q (i.1.2 0)) = _
  rw [dotProduct, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, dotProduct]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- The quadratic phase at either endpoint of the transform. -/
def chirp (B : LinearMap.BilinForm F V) (x : Common V T) : F :=
  -(B (x.1.1 0) (x.1.2 0))

/-- Common-coordinate transfer, allowing independently charted labels. -/
def transfer (B : LinearMap.BilinForm F V) (D : ℕ)
    (ey ex : Bits A ≃ₗ[F] Common V T) : Local A :=
  (primeCommonKernel (C := Fin 1) binaryRoot B 1 D).submatrix ey ex

/-- A charged kernel with different input and output charts uses exactly
two normalized families of child axes and two zero-cost chirps. -/
theorem realizes_transfer [FiniteDimensional F T] (B : LinearMap.BilinForm F V)
    (p q : V ≃ₗ[F] Bits D) (hpq : ∀ x y, B x y = p x ⬝ᵥ q y)
    (ey ex : Bits A ≃ₗ[F] Common V T) : Realizes (2*D) (transfer B D ey ex) := by
  classical
  let out := ey.trans (outputChart p q)
  let inp := ex.trans (inputChart p q)
  let χy (y : Bits A) := chirp B (ey y)
  let χx (x : Bits A) := chirp B (ex x)
  have real := ((Realizes.sign χy).mul (Realizes.partialChart out inp)).mul (Realizes.sign χx)
  simp only [Nat.zero_add, Nat.add_zero] at real
  rw [two_mul]
  convert real using 1
  ext y x
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  change (primeCommonKernel (C := Fin 1) binaryRoot B 1 D) (ey y) (ex x) =
    character (χy y) * partialChart out inp y x * character (χx x)
  rw [primeCommonKernel]
  simp only [Fintype.card_unique, invOf_eq_inv, Nat.cast_ofNat, inv_one,
    Units.val_one, one_mul, Finset.univ_unique, Finset.sum_singleton]
  have dot := dot_charts p q (ey y) (ex x)
  rw [← hpq, ← hpq] at dot
  have normal : (w : ℂ)^(D+D) = (2 : ℂ)⁻¹ ^ D := by
    rw [← two_mul, even_child_normalization]
  change (if (ex x).2 = (ey y).2 then _ else _) = _
  by_cases he : (ex x).2 = (ey y).2
  · rw [ite_eq_left he]
    unfold partialChart
    rw [ite_eq_left (show (out y).2 = (inp x).2 from he.symm), normal]
    change _ = character (χy y) * (_ * character (((outputChart p q) (ey y)).1 ⬝ᵥ
      ((inputChart p q) (ex x)).1)) * character (χx x)
    rw [dot]
    have step : B ((ex x).1.1 0 - (ey y).1.1 0) ((ey y).1.2 0 - (ex x).1.2 0) =
        χy y + (B ((ex x).1.1 0) ((ey y).1.2 0) + B ((ey y).1.1 0) ((ex x).1.2 0)) + χx x := by
      simp only [map_sub, LinearMap.sub_apply, χy, χx, chirp]
      abel
    change _ * digitPhase binaryRoot (B ((ex x).1.1 0 - (ey y).1.1 0) ((ey y).1.2 0 - (ex x).1.2 0)) = _
    rw [step]
    simp only [character, AddChar.map_add_eq_mul]
    ring
  · rw [ite_eq_right he]
    unfold partialChart
    rw [ite_eq_right (show (out y).2 ≠ (inp x).2 from Ne.symm he)]
    simp

/-- Move source label coordinates into the reference chart. -/
def source (ref ex : Bits A ≃ₗ[F] Common V T) : Local A :=
  pushAddress (ex.trans ref.symm)

/-- Move the reference chart back to destination label coordinates. -/
def target (ref ey : Bits A ≃ₗ[F] Common V T) : Local A :=
  pushAddress (ref.trans ey.symm)

theorem realizes_source (ref ex : Bits A ≃ₗ[F] Common V T) : Realizes 0 (source ref ex) :=
  Realizes.permutation _

theorem realizes_target (ref ey : Bits A ≃ₗ[F] Common V T) : Realizes 0 (target ref ey) :=
  Realizes.permutation _

/-- Every rectangle containing the same ordered pair gives the same transfer,
even when the chosen common reference chart varies from rectangle to rectangle. -/
theorem factor (B : LinearMap.BilinForm F V) (D : ℕ) (ref ey ex : Bits A ≃ₗ[F] Common V T) :
    target ref ey * transfer B D ref ref * source ref ex = transfer B D ey ex := by
  classical
  ext y x
  change (∑ u, (∑ v, (if y = (ref.trans ey.symm) v then (1 : ℂ) else 0) *
    transfer B D ref ref v u) * (if u = (ex.trans ref.symm) x then 1 else 0)) = _
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    ite_mul, one_mul, zero_mul]
  have test (v : Bits A) : y = ey.symm (ref v) ↔ v = ref.symm (ey y) := by
    rw [LinearEquiv.eq_symm_apply, LinearEquiv.eq_symm_apply, eq_comm]
  simp only [transfer, Matrix.submatrix_apply, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, test, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

end
end KernelPass.Charged

end NearSquareRoot
end Computability
end OAI
