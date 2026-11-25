import OAI.Computability.BorderVNP.ShortenDenseEpoch
import OAI.Computability.BorderVNP.ShortenDenseSiteHistory

/-!
# Site potential and exact flat tensor on the publicly sorted histories

Calibrate the number of rounds before selecting their finite catalogs, and
the common fan-in after the catalogs and final motion multiplier are fixed.
The conclusion applies to any specified family of valid final site motions
on these very terminal networks. It can therefore use the motions computed
by the public rounding circuit.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized

open Crossing Epoch Epoch.Round Cover Shortening Adaptive Packing Catalog Filter
open scoped Classical Topology
attribute [local instance] portFintype

universe u

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {I : Type} [Fintype I]

/-- The site-to-site quantitative calibration on the dense public program.
Its width coefficient and initial move budget precede the height. Its error,
potential weight and fan-in follow the finite per-stage and final motion
constants. The bound uses the actual leaf maximum on the given input tuple. -/
theorem site_calibration (e : PaidIdentity K D m) (hm : 0 < m) :
    ∃ ν > (0:ℝ), ∃ H > (0:ℝ), ∀ L A : ℝ, 0 ≤ L → 0 ≤ A →
    ∃ b : ℕ, 0 < b ∧ ∀ {δ : ℝ} (hδ : 0 < δ) (B : Fin b → Type) [∀ i, Fintype (B i)]
      (u v : Fin b → ℝ) (Cout : ℝ), (∀ i, 0 ≤ u i) → (∀ i, 0 ≤ v i) → 0 ≤ Cout →
    ∃ weight > (0:ℝ), ∃ E > (0:ℝ), ∀ᶠ k : ℕ in atTop, ∃ hk : 0 < k,
    ∀ {P : Type} [Fintype P] {bits : P → ℕ} {states : ℕ → Type u} (depth : ℕ → ℕ)
      (view : ∀ j, states j → PlacedPack D (Port k P j) (width bits k j) K I (depth j))
      (F : Program (B := B) e view) (V : ℝ), 0 ≤ V →
      (∀ i : Fin b, (Fintype.card (I → Deck (depth (i.val+1)+1)) : ℝ) ≤ V) →
      (∀ i c, Nonempty (Stage.Measurements (F.stage i c) hk H ν (u i) (v i))) →
      ∀ (flat : Fin (k^b) → states 0) (sites : ∀ i, InitialSites (view 0 (flat i)) L hδ)
        {d cap : ℕ} (out : ∀ i : F.Hist flat, SiteOutput (F.terminal flat i) d L A Cout cap),
        (∀ i, (out i).routes.potential weight / (k : ℝ)^b ≤
          maximumLeaf hk id (fun j => (sites j).routes.potential weight)/2 + E*V) ∧
        ∀ x : Ports (fun z : Fin (k^b) × P => bits z.2),
          (parallelPacks (fun i => (sites i).pack)).tensor x =
            ∑ i : F.Hist flat, (flattenPack b (F.terminal flat i).pack).tensor x := by
  obtain ⟨ν,hν,H,hH,cal⟩ := exists_physical_epoch (I := I) e hm
  refine ⟨ν,hν,H,hH,?_⟩
  intro L A hL hA
  obtain ⟨b,hb,coeff⟩ := cal L A hL hA
  refine ⟨b,hb,?_⟩
  intro δ hδ B finite u v Cout hu hv hout
  obtain ⟨weight,hw,E,hE,late⟩ := coeff B u v (Fintype.card (Hop I L δ)) Cout hu hv (Nat.cast_nonneg _) hout
  refine ⟨weight,hw,E,hE,?_⟩
  filter_upwards [late] with k hk
  obtain ⟨hk,bound⟩ := hk
  refine ⟨hk,?_⟩
  intro P fp bits states depth view F V hV tiles measured flat sites d cap out
  let M := maximumLeaf hk id (fun j => (sites j).routes.potential weight)
  have hM : 0 ≤ M := by
    let i : Fin (k^b) := ⟨0,pow_pos hk _⟩
    obtain ⟨hn,hx⟩ := (sites i).routes.nonneg_width_concentration
    exact (add_nonneg hn (mul_nonneg hw.le hx)).trans (leaf_le_maximum hk id (fun j => (sites j).routes.potential weight) i)
  have initial (i : Fin (k^b)) : (view 0 (flat i)).length ≤ M*L ∧ (view 0 (flat i)).concentration ≤
      M*(Fintype.card (Hop I L δ)/weight) := by
    rw [(sites i).realizes]
    exact ((sites i).routes.initial_placed_bounds hδ hL hw (leaf_le_maximum hk id (fun j => (sites j).routes.potential weight) i)).2
  have est := bound depth view F M V hM hV tiles measured (leavesEquiv k (states 0) b flat)
    (allLeaves_of_flat _ b flat initial)
  refine ⟨?_,fun x => (input_tensor (fun j => view 0 (flat j)) sites x).trans (F.terminal_tensor flat x)⟩
  intro i
  apply le_trans _ (est i)
  apply div_le_div_of_nonneg_right _ (by positivity)
  unfold SiteRoutes.potential
  exact (add_le_add (out i).width_le (mul_le_mul_of_nonneg_left (out i).concentration_le hw.le)).trans_eq
    (by rw [mul_assoc]; rfl)

end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
