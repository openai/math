import OAI.Computability.VPVNP.StarExtension
import OAI.Computability.VPVNP.PlacedTensor
import OAI.Computability.VPVNP.CubeStar
import OAI.Computability.VPVNP.SplitWires
import OAI.Computability.VPVNP.WireCATZero

/-!
# Extracting a tensor witness on equally wide terminals

In (4.4), the height and the old tensor are chosen before the circuit
lengths. The star width is the number of terminal legs at each party.
Reindexing the profile witness gives one coefficient table on the
terminals, with dimension `2 ^ b` at each of them and no other legs.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireTensor

variable {k : Type*} [Field k] {J R : Type} [Fintype J] [Fintype R]

open scoped Classical in
/-- The number of terminal legs grouped at the given party. -/
noncomputable def terminalMultiplicity (p : R → J) (j : J) : ℕ :=
  Fintype.card {r : R // p r = j}

private def terminalFiberEquiv (p : R → J) (j : J) (D : Type) :
    ((r : R) → j = p r → D) ≃ ({r : R // p r = j} → D) where
  toFun z r := z r.val r.property.symm
  invFun z r hr := z ⟨r, hr.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem sum_terminalMultiplicity (p : R → J) (f : J → ℝ) :
    ∑ j, (terminalMultiplicity p j : ℝ) * f j = ∑ r, f (p r) := by
  classical
  rw [← Fintype.sum_fiberwise p (fun r ↦ f (p r))]
  apply Finset.sum_congr rfl
  intro j _
  have h (i : {r : R // p r = j}) : f (p i.val) = f j := congrArg f i.property
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, terminalMultiplicity]

namespace SpectralPoint

variable (F : SpectralPoint k J)

/-- Reindex the coordinates of a width-profile witness as one equal-sized
leg per terminal. At a party with no terminal there is one coordinate. -/
theorem starWitness_eq_placed (p : R → J) (W : StarWitness k (terminalMultiplicity p)) :
    ∃ A : (R → Fin (2 ^ W.height)) → k, A ≠ 0 ∧
      F.value (placedTensor p (fun _ ↦ Fin (2 ^ W.height)) A) = F.value W.tensor := by
  classical
  let D := Fin (2 ^ W.height)
  let e (j : J) : ((r : R) → j = p r → D) ≃ Fin (2 ^ (W.height * terminalMultiplicity p j)) :=
    (terminalFiberEquiv p j D).trans (Fintype.equivFinOfCardEq (by
      rw [Fintype.card_fun, Fintype.card_fin, ← pow_mul]
      rfl))
  let regroup := placedAssignmentEquiv p (fun _ ↦ D)
  let A (x : R → D) : k := W.coeff (fun j ↦ e j (regroup x j))
  have hcoeff (x : (j : J) → (r : R) → j = p r → D) :
      A (regroup.symm x) = W.coeff (fun j ↦ e j (x j)) := by
    simp only [A, Equiv.apply_symm_apply]
  refine ⟨A, ?_, (F.value_eq_of_mutual (restricts_of_reindex e hcoeff)).symm⟩
  intro hz
  apply W.nonzero
  funext x
  let y := fun j ↦ (e j).symm (x j)
  have h := hcoeff y
  rw [hz] at h
  change (0 : k) = W.coeff (fun j ↦ e j ((e j).symm (x j))) at h
  change W.coeff x = (0 : k)
  simpa only [Equiv.apply_symm_apply] using h.symm

/-- A strict lower bound valid for every extending center selects a concrete
height and terminal coefficient table over the original field. -/
theorem exists_terminalStar_witness [Nonempty J] (p : R → J) (threshold : ℝ)
    (hlower : ∀ H : SpectralPoint k (Option J), (∀ T, H.value (embedOld T) = F.value T) →
      threshold < ∑ r, H.wireDistance none (some (p r))) :
    ∃ (b : ℕ) (_ : 0 < b) (A : (R → Fin (2 ^ b)) → k), A ≠ 0 ∧
      threshold < Real.logb 2 (F.value (placedTensor p (fun _ ↦ Fin (2 ^ b)) A)) / b := by
  obtain ⟨H, hExt, hEq⟩ := F.exists_starRate_extension (terminalMultiplicity p)
  have hRate := hlower H hExt
  rw [← sum_terminalMultiplicity p (fun j ↦ H.wireDistance none (some j)), hEq] at hRate
  obtain ⟨v, ⟨W, rfl⟩, hlt, _⟩ := (F.starRate_isLUB _).exists_between hRate
  obtain ⟨A, hA, heq⟩ := F.starWitness_eq_placed p W
  exact ⟨W.height, W.positive, A, hA, heq ▸ hlt⟩

open scoped symmDiff

/-- Equation (4.4) from CAT(0) embeddings of the extending spectral points.
The selected tensor has one explicit equal-sized basis at each marked
singleton corner. The height and the table are independent of later powers. -/
theorem exists_cubeStar_witness_of_embeddings [Nonempty J] {n : ℕ} (corner : Finset (Fin n) → J)
    {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε)
    (hcorner : ∀ A B, F.wireDistance (corner A) (corner B) ^ 2 = σ ^ 2 * (A ∆ B).card)
    (embedding : ∀ H : SpectralPoint k (Option J), (∀ T, H.value (embedOld T) = F.value T) →
      ∃ (X : Type) (_ : MetricSpace X) (_ : SpectralGeometry.HasCATZeroSegments X)
        (e : Option J → X), ∀ a b, dist (e a) (e b) = H.wireDistance a b) :
    ∃ (b : ℕ) (_ : 0 < b) (A : (Fin n → Fin (2 ^ b)) → k), A ≠ 0 ∧
      SpectralGeometry.starLength n - ε <
        Real.logb 2 (F.value (placedTensor (fun i ↦ corner {i}) (fun _ ↦ Fin (2 ^ b)) A)) /
          (σ * b) := by
  have hlower (H : SpectralPoint k (Option J)) (hH : ∀ T, H.value (embedOld T) = F.value T) :
      σ * (SpectralGeometry.starLength n - ε) < ∑ i : Fin n, H.wireDistance none (some (corner {i})) := by
    obtain ⟨X, hX, hcat, e, he⟩ := embedding H hH
    let f (A : Finset (Fin n)) := e (some (corner A))
    have hf (A B : Finset (Fin n)) : dist (f A) (f B) ^ 2 = σ ^ 2 * (A ∆ B).card := by
      rw [show dist (f A) (f B) = _ from he _ _, F.wireDistance_extension H hH, hcorner]
    have h := SpectralGeometry.cube_star_lower hcat f hσ.le hf (e none)
    simp only [f, he] at h
    exact (mul_lt_mul_of_pos_left (sub_lt_self _ hε) hσ).trans_le h
  obtain ⟨b, hb, A, hA, hlt⟩ := F.exists_terminalStar_witness (fun i ↦ corner {i}) _ hlower
  refine ⟨b, hb, A, hA, (lt_div_iff₀ (mul_pos hσ (Nat.cast_pos.mpr hb))).mpr ?_⟩
  simpa only [mul_left_comm, mul_comm, mul_assoc] using (lt_div_iff₀ (Nat.cast_pos.mpr hb)).mp hlt

/-- Equation (4.4) for a cube realized by a spectral wire metric. The
CAT(0) completion of the attaining extension supplies the star bound. -/
theorem exists_cubeStar_witness [Nonempty J] {n : ℕ} (corner : Finset (Fin n) → J)
    {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε)
    (hcorner : ∀ A B, F.wireDistance (corner A) (corner B) ^ 2 = σ ^ 2 * (A ∆ B).card) :
    ∃ (b : ℕ) (_ : 0 < b) (A : (Fin n → Fin (2 ^ b)) → k), A ≠ 0 ∧
      SpectralGeometry.starLength n - ε <
        Real.logb 2 (F.value (placedTensor (fun i ↦ corner {i}) (fun _ ↦ Fin (2 ^ b)) A)) /
          (σ * b) :=
  F.exists_cubeStar_witness_of_embeddings corner hσ hε hcorner (fun H _ ↦ H.catZero_embedding)

end SpectralPoint
end WireTensor

end VPVNP
end Computability
end OAI
