import OAI.Computability.VPVNP.SplitWireExtension
import OAI.Computability.VPVNP.WireGeodesic
import OAI.Computability.VPVNP.MidpointUnion
import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Equiv.List

/-!
# The countable union of finite spectral midpoint extensions

For Corollary 2.5, retain the original parties and index the new parties by
their creation times. A pair is scheduled at arbitrarily late stages, so a
stage at which both parties already exist adds their midpoint. Old distances
are preserved at every subsequent stage. Every finite list therefore has
its full distance matrix in one finite spectrum.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireTensor

universe u

private def TowerStage (J : Type) : ℕ → Type
  | 0 => J
  | n + 1 => Option (TowerStage J n)

@[instance_reducible] private def stageFintype {J : Type} [Fintype J] : (n : ℕ) → Fintype (TowerStage J n)
  | 0 => inferInstanceAs (Fintype J)
  | n + 1 => @instFintypeOption _ (stageFintype n)

private theorem stageNontrivial {J : Type} [Nontrivial J] : (n : ℕ) → Nontrivial (TowerStage J n)
  | 0 => inferInstanceAs (Nontrivial J)
  | n + 1 => by
    let : Nontrivial (TowerStage J n) := stageNontrivial n
    exact inferInstanceAs (Nontrivial (Option (TowerStage J n)))

attribute [local instance] stageFintype stageNontrivial

variable {J : Type}

/-- A party named by its creation time first exists at the next stage. -/
private def birth : J ⊕ ℕ → ℕ
  | .inl _ => 0
  | .inr m => m + 1

open scoped Classical in
private noncomputable def representative [Inhabited J] : (n : ℕ) → J ⊕ ℕ → TowerStage J n
  | 0, x => x.elim (fun j : J ↦ j) (fun _ ↦ (default : J))
  | n + 1, x => if x = Sum.inr n then none else some (representative n x)

private theorem representative_old [Inhabited J] {x : J ⊕ ℕ} {n : ℕ} (hx : birth x ≤ n) :
    representative (n + 1) x = some (representative n x) := by
  have hne : x ≠ Sum.inr n := by rintro rfl; simp [birth] at hx
  simp [representative, hne]
  rfl

private theorem representative_new [Inhabited J] (n : ℕ) :
    representative (J := J) (n + 1) (.inr n) = none := by
  simp [representative]
  rfl

/-- The left unpairing coordinate encodes the pair and the right coordinate
can be chosen arbitrarily large. -/
private def scheduled [Encodable J] [Inhabited J] (n : ℕ) : (J ⊕ ℕ) × (J ⊕ ℕ) :=
  (Encodable.decode (α := (J ⊕ ℕ) × (J ⊕ ℕ)) n.unpair.1).getD (.inl default, .inl default)

private theorem scheduled_late [Encodable J] [Inhabited J] (x y : J ⊕ ℕ) :
    ∃ n, birth x ≤ n ∧ birth y ≤ n ∧ scheduled n = (x, y) := by
  let m := max (birth x) (birth y)
  let n := Nat.pair (Encodable.encode (x,y)) m
  exact ⟨n, (le_max_left _ _).trans (Nat.right_le_pair _ m),
    (le_max_right _ _).trans (Nat.right_le_pair _ m), by simp [scheduled, n]⟩

variable {k : Type u} [Field k] [Fintype J] [Inhabited J] [Encodable J]

private noncomputable def extendAt {A : Type} [Fintype A] (G : SpectralPoint k A) (a b : A) :
    SpectralPoint k (Option A) :=
  (G.exists_split_extension a b (div_nonneg (G.wireDistance_nonneg _ _) (by norm_num))
    (div_nonneg (G.wireDistance_nonneg _ _) (by norm_num)) (add_halves _)).choose

private theorem extendAt_spec {A : Type} [Fintype A] (G : SpectralPoint k A) (a b : A) :
    (∀ T, (extendAt G a b).value (embedOld T) = G.value T) ∧
    (extendAt G a b).wireDistance (some a) none = G.wireDistance a b / 2 ∧
    (extendAt G a b).wireDistance none (some b) = G.wireDistance a b / 2 :=
  (G.exists_split_extension a b (div_nonneg (G.wireDistance_nonneg _ _) (by norm_num))
    (div_nonneg (G.wireDistance_nonneg _ _) (by norm_num)) (add_halves _)).choose_spec

private noncomputable def stagePoint (F : SpectralPoint k J) :
    (n : ℕ) → SpectralPoint k (TowerStage J n)
  | 0 => F
  | n + 1 => extendAt (stagePoint F n) (representative n (scheduled n).1) (representative n (scheduled n).2)

private noncomputable def stageDist (F : SpectralPoint k J) (n : ℕ) (x y : J ⊕ ℕ) : ℝ :=
  (stagePoint F n).wireDistance (representative n x) (representative n y)

private theorem stageDist_stable (F : SpectralPoint k J) (n : ℕ) (x y : J ⊕ ℕ)
    (hx : birth x ≤ n) (hy : birth y ≤ n) : stageDist F (n+1) x y = stageDist F n x y := by
  simp only [stageDist, representative_old hx, representative_old hy]
  exact (stagePoint F n).wireDistance_extension _ (extendAt_spec _ _ _).1 _ _

private theorem stage_midpoint (F : SpectralPoint k J) (x y : J ⊕ ℕ) :
    ∃ n, birth x ≤ n ∧ birth y ≤ n ∧
      stageDist F (n+1) x (.inr n) = stageDist F n x y / 2 ∧
      stageDist F (n+1) (.inr n) y = stageDist F n x y / 2 := by
  obtain ⟨n, hx, hy, hpair⟩ := scheduled_late x y
  refine ⟨n, hx, hy, ?_⟩
  simp only [stageDist, representative_old hx, representative_old hy, representative_new, stagePoint, hpair]
  exact (extendAt_spec _ _ _).2

end WireTensor


namespace WireTensor.SpectralPoint

universe u

attribute [local instance] stageFintype stageNontrivial

open VPVNP.SpectralGeometry VPVNP.WireGeometry

variable {k : Type u} [Field k] {J : Type} [Fintype J] [Nontrivial J]

/-- The finite spectral pseudometric extends to a countable pseudometric
space with a midpoint for each pair. Each finite configuration of the new
space occurs, with scale one, in a finite spectral point. -/
theorem exists_midpoint_tower (F : SpectralPoint k J) :
    ∃ M : PseudoMetricSpace (J ⊕ ℕ),
      (∀ a b : J, @dist (J ⊕ ℕ) M.toDist (.inl a) (.inl b) = F.wireDistance a b) ∧
      @RealizableConfigurations k _ _ M ∧ ∀ a b, ∃ z, @AtFraction _ M a b (1 / 2) z := by
  classical
  let : Encodable J := Fintype.toEncodable J
  let : Inhabited J := Classical.inhabited_of_nonempty inferInstance
  let M := unionPseudoMetric birth (stageDist F) (stageDist_stable F)
    (fun n _ ↦ (stagePoint F n).wireDistance_self _)
    (fun n _ _ ↦ (stagePoint F n).wireDistance_comm _ _)
    (fun n _ _ _ ↦ (stagePoint F n).wireDistance_triangle _ _ _)
  refine ⟨M, fun _ _ ↦ rfl, ?_, ?_⟩
  · intro m f
    obtain ⟨n, _, hn⟩ := unionDist_finite_stage (stageDist_stable F) f
    exact ⟨{ Parties := TowerStage J n, spectrum := stagePoint F n, scale := 1,
             scale_pos := zero_lt_one, label := fun i ↦ representative n (f i),
             distances := fun i j ↦ (hn i j).trans (one_mul _).symm }⟩
  · intro x y
    obtain ⟨n, hx, hy, hl, hr⟩ := stage_midpoint F x y
    refine ⟨.inr n, ?_⟩
    have hn : birth (J := J) (.inr n) ≤ n + 1 := le_rfl
    change unionDist birth (stageDist F) x (.inr n) = (1 / 2) * unionDist birth (stageDist F) x y ∧
      unionDist birth (stageDist F) (.inr n) y = (1 - 1 / 2) * unionDist birth (stageDist F) x y
    rw [unionDist_eq_stage (stageDist_stable F) hx hy,
      unionDist_eq_stage (stageDist_stable F) (Nat.le_succ_of_le hx) hn,
      unionDist_eq_stage (stageDist_stable F) hn (Nat.le_succ_of_le hy), hl, hr]
    constructor <;> ring

end WireTensor.SpectralPoint

end VPVNP
end Computability
end OAI
