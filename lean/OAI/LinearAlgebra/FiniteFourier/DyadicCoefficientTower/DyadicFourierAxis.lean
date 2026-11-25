import OAI.LinearAlgebra.FiniteFourier.DyadicFourierWord
import OAI.LinearAlgebra.FiniteFourier.DyadicCoefficientsPacking

/-! # Fourier words on the dyadic list and its jet extensions -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace DyadicCoefficientTower

variable {η : ℝ} {n B a : ℕ} {D : DyadicAxisPacking GaussianRationals η n B} {L : Finset ℕ}
  (T : DyadicCoefficientTower D L) {R : Type*} [CommRing R]

/-- A common dyadic order supplies the short binary transforms for every
unit-separated axis of width at most `B`, in the order or in any of its jets. -/
theorem fourierWord (f : T.Order →+* R) (ha : 0 < a) (haB : a ≤ B)
    (hs : ∀ s : R, ∃ t : R, IsUnit t ∧ IsUnit (s-t)) {q : R} (hq : IsUnit q)
    (hsep : Pairwise fun i j : Fin a ↦ IsUnit (q^i.val - q^j.val))
    {A : Matrix (Fin a) (Fin a) R} (hA : A = dftMatrix a q ∨ A = (dftMatrix a q)⁻¹) :
    OccupiedWord (Fin (13*a)) (6400*(1+Nat.clog 2 (2+B))) A := by
  apply protectedFourier_word_up_to (Or.inl (rfl : 2 = 2)) ha haB _ hs hq hsep
    (by simpa only [geometricMatrix_eq_dftMatrix] using hA)
  intro j hj
  obtain ⟨hb,u,_,hu,hsep'⟩ := T.transform_nodes (D.binaryPower_dvd hj) f
  exact ⟨hb,u,hu,fun i k hik ↦ hsep' i k hik⟩

/-- The original chosen primitive coordinate supplies both transform directions. -/
theorem transformWord (f : T.Order →+* R) (haB : a ≤ B) (ha : a ∣ D.rootOrder)
    (hs : ∀ s : R, ∃ t : R, IsUnit t ∧ IsUnit (s-t))
    (A : Matrix (Fin a) (Fin a) R)
    (hA : let F := dftMatrix a (f (AdjoinRoot.root T.modulus)^(D.rootOrder/a))
          A = F ∨ A = F⁻¹) :
    OccupiedWord (Fin (13*a)) (6400*(1+Nat.clog 2 (2+B))) A := by
  obtain ⟨_,u,he,_,hp⟩ := T.transform_nodes ha f
  apply T.fourierWord f (Nat.pos_of_dvd_of_pos ha D.rootOrder_pos) haB hs u.isUnit
    (fun i j hij ↦ hp i j hij)
  simpa only [he] using hA

end DyadicCoefficientTower

end FiniteFourier
end LinearAlgebra
end OAI
