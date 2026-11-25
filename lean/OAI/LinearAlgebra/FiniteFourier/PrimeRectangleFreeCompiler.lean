import OAI.LinearAlgebra.FiniteFourier.PrimeRectangleEndpointFactor
import OAI.LinearAlgebra.FiniteFourier.PrimeRoutedPieces
import OAI.LinearAlgebra.FiniteFourier.PrimeRoutedUniform

/-! # Compiling the free part of an ordinary routed pencil

A free rectangle uses one transform at each incident label and clock row.
The same transforms serve all distinguished slots of the query.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

open scoped Classical

private theorem freeRectangle_uniform {K : Type*} [CommSemiring K] {ℓ : ℕ} {ζ : K}
    {L W J : Type} [Fintype L] [Fintype W] [Fintype J]
    (X : ℕ → Type) [∀ f, Fintype (X f)] (F : ℕ → ℕ)
    (S T : Set L) (z : K) (B : J → Matrix W W K)
    (H : (f : ℕ) → J → L → L → Matrix (X f) (X f) K)
    (post : (f : ℕ) → T → Matrix (X f) (X f) K)
    (pre : (f : ℕ) → S → Matrix (X f) (X f) K)
    (co ci D : ℕ) (ho : co ≤ D) (hi : ci ≤ D)
    (hpost : ∀ f t, PrimeTemplateProgram ℓ f (F f) ζ (post f t) 0 co)
    (hpre : ∀ f s, PrimeTemplateProgram ℓ f (F f) ζ (pre f s) 0 ci)
    (hfac : ∀ f j (t : T) (s : S), ∃ M : Matrix (X f) (X f) K,
      RealizableAtMost M 0 ∧ H f j t s = post f t * M * pre f s) :
    LinearRowTemplate ℓ F ζ X
      (fun f => routedRectangleMatrix S T z (∑ j, routedPencilTerm (B j) (H f j)))
      (Fintype.card W * (Fintype.card T + Fintype.card S) * D) := by
  refine ⟨freeRectangleOverhead (Fintype.card S) (Fintype.card T) (Fintype.card W)
    (Fintype.card J) 0 0 0, fun f _ => ?_⟩
  choose M hm hM using hfac f
  have p := routedFreeRectangle_program S T z B (H f) (post f) M (pre f) hM 0 0 0
    (hpost f) (fun _ => Nat.zero_le _) (fun j t s => by simpa using hm j t s)
    (hpre f) (fun _ => Nat.zero_le _)
  obtain ⟨n, hn, prog⟩ := p
  refine ⟨n, hn, _, ?_, prog⟩
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.mul_assoc, Nat.add_mul]
  exact Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_left _ ho) (Nat.mul_le_mul_left _ hi))

namespace BitRoutingGeometry

variable {ℓ L b : ℕ} [Fact ℓ.Prime] (G : BitRoutingGeometry ℓ L b)
variable {K : Type*} {W : Type} [CommRing K] [Invertible (ℓ : K)] {ζ : K}

private theorem freeRectangle_empty (hζ : IsPrimitiveRoot ζ ℓ) (R : FreeBitRectangle ℓ L b)
    (z : K) (B : Fin 0 → Matrix W W K) (a : (ZMod ℓ)ˣ) (n : ℕ) :
    LinearRowTemplate ℓ (G.axisFibers 0) ζ (G.RowAddress 0)
      (fun f => routedRectangleMatrix (bitSources R.val) (bitTargets R.val) z
        (∑ j, routedPencilTerm (B j) (G.transfer hζ f a j))) n := by
  refine ⟨0, fun f _ => ⟨0, Nat.zero_le _, 0, Nat.zero_le _, .localCircuit ?_⟩⟩
  exact ⟨0, le_rfl, ⟨.nil, fun _ => .zero⟩, by
    ext o i
    simp [Circuit.matrix, Circuit.eval, Readout.eval, routedRectangleMatrix]⟩

/-- Share the two physical endpoint programs across all distinguished slots of a free rectangle. -/
theorem freeRectangle_template [Fintype W] {m : ℕ} (hζ : IsPrimitiveRoot ζ ℓ)
    (R : FreeBitRectangle ℓ L b) (z : K) (B : Fin m → Matrix W W K) (a : (ZMod ℓ)ˣ) :
    LinearRowTemplate ℓ (G.axisFibers m) ζ (G.RowAddress m)
      (fun f => routedRectangleMatrix (bitSources R.val) (bitTargets R.val) z
        (∑ j, routedPencilTerm (B j) (G.transfer hζ f a j)))
      (Fintype.card W * (Fintype.card (bitTargets R.val) + Fintype.card (bitSources R.val)) *
        (2 * G.D)) := by
  by_cases hm : m = 0
  · subst m
    exact G.freeRectangle_empty hζ R z B a _
  let post (f : ℕ) (t : bitTargets R.val) := primeTargetEndpoint (J := Fin m) (f := f) hζ a
    (G.targetSlice R.val t.property false) (G.targetSlice R.val t.property true)
  let pre (f : ℕ) (s : bitSources R.val) := primeSourceEndpoint (J := Fin m) (f := f) hζ a
    (G.sourceSlice R.val R.property s.property false) (G.sourceSlice R.val R.property s.property true)
  have hd := G.dim_pos
  have hA : 0 < 2 * (Fintype.card (Fin m) + Fintype.card (Fin (G.D - 1))) := by simp; omega
  have hdim : m + (G.D - 1) = m + G.D - 1 := by omega
  have hr (H : Submodule (ZMod ℓ) G.Space) : Module.finrank (ZMod ℓ) H ≤ G.D := by
    simpa using H.finrank_le
  apply freeRectangle_uniform (G.RowAddress m) (G.axisFibers m) _ _ z B
    (fun f j => G.transfer hζ f a j) post pre
    (2 * Module.finrank (ZMod ℓ) ((G.targetSpan R.val).orthogonalBilin G.form))
    (2 * Module.finrank (ZMod ℓ) (G.targetSpan R.val)) (2 * G.D)
    (Nat.mul_le_mul_left 2 (hr _)) (Nat.mul_le_mul_left 2 (hr _))
  · intro f t
    simpa only [axisFibers, Fintype.card_fin, hdim] using primeTargetEndpoint_program
      (J := Fin m) (f := f) hζ a
      (G.targetSlice R.val t.property false) (G.targetSlice R.val t.property true) hA
  · intro f s
    simpa only [axisFibers, Fintype.card_fin, hdim] using primeSourceEndpoint_program
      (J := Fin m) (f := f) hζ a
      (G.sourceSlice R.val R.property s.property false) (G.sourceSlice R.val R.property s.property true) hA
  · intro f j t s
    exact G.free_endpoint_factor (f := f) hζ a R.val R.property s.property t.property j

end BitRoutingGeometry
end

end

end FiniteFourier
end LinearAlgebra
end OAI
