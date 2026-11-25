import OAI.Computability.BorderVNP.PackedHistoryDenseProgram
import OAI.Computability.BorderVNP.ShortenDenseMeasurements
import OAI.Computability.BorderVNP.ShortenAdaptiveInputs

/-!
# The quantitative epoch for stable-order input sorting and physical storage

These are the actual histories of the publicly ordered allocator. Both
coordinates are taken on its true output networks, and the error term
uses the concentrations of those histories' K predecessor networks.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized

open Crossing Cover Filter Topology Shortening Adaptive PlacedStep
open scoped Classical

universe u

variable {D m b k : ℕ} [NeZero D] {K : Type*} [Field K] {I P : Type} [Fintype I] {bits : P → ℕ}
variable {A : ℕ → Type u} {B : Fin b → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
variable {e : PaidIdentity K D m} {view : ∀ j, A j → PlacedPack D (Port k P j) (width bits k j) K I (depth j)}

namespace Program

variable (F : Program (B := B) e view)

/-- Physical length and concentration on the exact normalized histories. -/
noncomputable def batch : Batch k :=
  F.system.batch (fun j p => (view j p).length) (fun j p => (view j p).concentration)

/-- Each measured sorted child tuple and its actual saved histogram satisfy
the stage inequalities on the same node used in the tensor expansion. -/
theorem stageBounds {hk : 0 < k} {r V : ℝ} {C : Fin b → ℝ}
    (rows : ∀ (i : Fin b) (c : Fin k → A i.val) (q : (F.stage i c).Index e),
      let W := (∑ j, (view i.val (c j)).length) / k
      let X := childMaximum (fun j => view i.val (c j)) hk
      ((F.stage i c).result e q).length / k ≤ r*W + C i * (Real.sqrt k)⁻¹ * X + C i * V ∧
      ((F.stage i c).result e q).concentration / k ≤ C i * (W + (Real.sqrt k)⁻¹ * X)) :
    F.batch.StageBounds hk r V C := by
  intro i z
  let c := fun j => (F.system.layer i.val).state (z.1 j)
  let q : (F.stage i c).Index e := z.2.2
  change (view (i.val+1) (F.advance i c q)).length / k ≤ _ ∧
    (view (i.val+1) (F.advance i c q)).concentration / k ≤ _
  rw [F.length i c q,F.concentration i c q]
  exact rows i c q

end Program

/-- The normalized length and concentration of every actual adaptive history.
The initial coefficients L and A are independent of the number of rounds.
The measurements are on the chosen input motions, before any matching or
profile expansion, and the bound is on the installed output networks. -/
theorem exists_physical_epoch (e : PaidIdentity K D m) (hm : 0 < m) :
    ∃ ν : ℝ, 0 < ν ∧ ∃ h : ℝ, 0 < h ∧ ∀ (L A : ℝ), 0 ≤ L → 0 ≤ A → ∃ b : ℕ, 0 < b ∧
    ∀ (B : Fin b → Type) [∀ i, Fintype (B i)] (u v : Fin b → ℝ) (Cin Cout : ℝ),
    (∀ i, 0 ≤ u i) → (∀ i, 0 ≤ v i) → 0 ≤ Cin → 0 ≤ Cout →
    ∃ weight : ℝ, 0 < weight ∧ ∃ E : ℝ, 0 < E ∧ ∀ᶠ k : ℕ in atTop, ∃ hk : 0 < k,
    ∀ {P : Type} {bits : P → ℕ} {states : ℕ → Type u} (depth : ℕ → ℕ)
      (view : ∀ n, states n → PlacedPack D (Port k P n) (width bits k n) K I (depth n))
      (F : Program (B := B) e view) (M V : ℝ), 0 ≤ M → 0 ≤ V →
      (∀ i : Fin b, (Fintype.card (I → Deck (depth (i.val+1)+1)) : ℝ) ≤ V) →
      (∀ i c, Nonempty (Stage.Measurements (F.stage i c) hk h ν (u i) (v i))) →
      ∀ a : Leaves k (states 0) b,
      allLeaves (fun z => (view 0 z).length ≤ M * L ∧ (view 0 z).concentration ≤ M * (Cin/weight)) b a →
      ∀ q : (F.system.histories b le_rfl a).Index,
        let p := view b ((F.system.layer b).state ((F.system.histories b le_rfl a).term q))
        (A*p.length + weight*Cout*p.concentration) / (k : ℝ)^b ≤ M/2 + E*V := by
  obtain ⟨ν,hν,h,hh,calibrate⟩ := Stage.measured_rows (I := I) e hm
  refine ⟨ν,hν,h,hh,?_⟩
  intro L A hL hA
  obtain ⟨b,hb,bound⟩ := exists_epoch_of_stage_bounds hν hL hA
  refine ⟨b,hb,?_⟩
  intro B _ u v Cin Cout hu hv hin hout
  choose C hC rows using fun i : Fin b => calibrate (B i) (u i) (v i) (hu i) (hv i)
  obtain ⟨weight,hw,E,hE,late⟩ := bound C Cin Cout hC hin hout
  refine ⟨weight,hw,E,hE,?_⟩
  filter_upwards [late] with k atK
  obtain ⟨hk,atK⟩ := atK
  refine ⟨hk,?_⟩
  intro P bits states depth view F M V hM hV htiles measure a ha q
  let W := fun n x => (view n x).length
  let X := fun n x => (view n x).concentration
  let test := fun z : states 0 => W 0 z ≤ M*L ∧ X 0 z ≤ M*(Cin/weight)
  let T := F.system.batchFrom W X test
  have stage := F.stageBounds (hk := hk) (C := C) (V := V)
    (r := max 0 (1-(ν/2)/2)) (fun i c q => rows i hk (fun j => view i.val (c j))
      (F.stage i c) (measure i c).some V (htiles i) q)
  have restricted := F.system.stageBounds_batchFrom W X test stage
  let t := (F.system.histories b le_rfl a).term q
  let node : T.Packs b := ⟨t,F.system.fromInputs_histories test b le_rfl a ha q⟩
  exact atK T M V hM hV (fun j _ z => (view j ((F.system.layer j).state z.val)).nonneg)
    restricted (fun z => z.property) node

end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
