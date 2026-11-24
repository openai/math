import OAI.Computability.VPVNP.StarTensor

/-!
# Packing tensors into a dyadic star

In the star case of Theorem 2.4, a tensor of local dimensions `2^(h*w j)`
fits into the contraction of a star of local dimensions `2^(r*w j)` after
taking `r / h` copies. Coordinate inclusion pads the entries by zero, and
coordinate selection recovers the original tensor power.
-/

namespace OAI
namespace Computability
namespace VPVNP

universe u v w

namespace WireTensor

variable {k : Type u} [CommSemiring k]

private theorem exists_padded_array {J : Type v} [Fintype J]
    (T : Tensor.{u,v,w} k J) (I : J → Type v) [b : ∀ j, Fintype (I j)]
    (e : ∀ j, T.Basis j ↪ I j) :
    ∃ A : Array k I, Restricts T (.mk I b A) ∧ Restricts (.mk I b A) T := by
  classical
  let L (j : J) (b : I j) (a : T.Basis j) : k := if b = e j a then 1 else 0
  refine ⟨applyLocal L T.coeff, ⟨L, rfl⟩, ?_⟩
  refine ⟨_, (applyLocal_pullback (fun j ↦ e j) (applyLocal L T.coeff)).trans ?_⟩
  funext a
  simp [applyLocal, L, Fintype.prod_boole, ← funext_iff, ite_mul]

/-- Pad a tensor by zero along local basis embeddings and realize the padded
array by a single covector at the center. Both local restrictions are exact. -/
theorem exists_star_contraction_of_embeddings {J : Type v} [Fintype J]
    (T : Tensor.{u,v,w} k J) (I : J → Type v) [∀ j, Fintype (I j)]
    (e : ∀ j, T.Basis j ↪ I j) :
    ∃ ξ, Restricts T (contractCenter (starTensor I) ξ) ∧
      Restricts (contractCenter (starTensor I) ξ) T := by
  obtain ⟨A, hA⟩ := exists_padded_array T I e
  exact ⟨A, by simpa only [contractCenter_starTensor] using hA⟩

private theorem packed_card_le {J : Type} (T : Tensor.{u,0,0} k J)
    (w : J → ℕ) (h r : ℕ) (dims : ∀ j, Fintype.card (T.Basis j) = 2 ^ (h * w j))
    (j : J) : Fintype.card ((tensorPowerFin (r / h) T).Basis j) ≤ 2 ^ (r * w j) := by
  change Fintype.card (Fin (r / h) → T.Basis j) ≤ _
  simp only [Fintype.card_fun, Fintype.card_fin, dims, ← pow_mul]
  apply Nat.pow_le_pow_right (by decide)
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    Nat.mul_le_mul_right (w j) (Nat.div_mul_le_self r h)

/-- At each party, the floor number of copies has enough local coordinates
in the dyadic star. This includes zero star multiplicity and zero widths. -/
theorem exists_dyadic_star_packing {J : Type} [Fintype J] (T : Tensor.{u,0,0} k J)
    (w : J → ℕ) (h r : ℕ) (dims : ∀ j, Fintype.card (T.Basis j) = 2 ^ (h * w j)) :
    ∃ ξ, Restricts (tensorPowerFin (r / h) T)
        (contractCenter (starTensor (fun j ↦ Fin (2 ^ (r * w j)))) ξ) ∧
      Restricts (contractCenter (starTensor (fun j ↦ Fin (2 ^ (r * w j)))) ξ)
        (tensorPowerFin (r / h) T) := by
  classical
  apply exists_star_contraction_of_embeddings
  intro j
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  simpa only [Fintype.card_fin] using packed_card_le T w h r dims j

/-- Contract the power of the width-profile star itself to a zero padding
of the packed tensor power, using a joint covector on all center indices. -/
theorem exists_starPowerFin_packing {J : Type} [Fintype J] (T : Tensor.{u,0,0} k J)
    (w : J → ℕ) (h r : ℕ) (dims : ∀ j, Fintype.card (T.Basis j) = 2 ^ (h * w j)) :
    ∃ ξ, Restricts (tensorPowerFin (r / h) T)
        (contractCenter (tensorPowerFin r (starTensor (fun j ↦ Fin (2 ^ w j)))) ξ) ∧
      Restricts (contractCenter (tensorPowerFin r (starTensor (fun j ↦ Fin (2 ^ w j)))) ξ)
        (tensorPowerFin (r / h) T) := by
  classical
  let I (j : J) := Fin r → Fin (2 ^ w j)
  have e (j : J) : (tensorPowerFin (r / h) T).Basis j ↪ I j := by
    apply Classical.choice
    apply Function.Embedding.nonempty_of_card_le
    simpa only [I, Fintype.card_fun, Fintype.card_fin, ← pow_mul, mul_comm (w j) r] using
      packed_card_le T w h r dims j
  obtain ⟨A, hA⟩ := exists_padded_array (tensorPowerFin (r / h) T) I e
  obtain ⟨ξ, hξ⟩ := contractCenter_starPowerFin (fun j ↦ Fin (2 ^ w j)) r A
  refine ⟨ξ, ?_⟩
  cases hξ
  exact hA

end WireTensor

end VPVNP
end Computability
end OAI
