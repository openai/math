import OAI.Computability.BorderVNP.PackedOuterBirthCases
import OAI.Computability.BorderVNP.PackedOuterCompilerRows
import OAI.Computability.BorderVNP.PackedOuterSignFree
import OAI.Computability.BorderVNP.PackedProgramBoxRoster
import OAI.Computability.BorderVNP.FiniteSewnFieldSchema

/-! # Guard invariants after replay and the final exterior incidence stage -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Machine

open Crossing Cover BorderVNP.Epoch.Round Shortening Shortening.Adaptive Packing Packing.Inherited
open Diagonal.ExternalSew Diagonal.CellEntries PublicCapacity
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

universe u
variable {D m start T : ℕ} [NeZero D] {F : Type} [Field F] {P : Type} [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity F D m} {S : Normalized.SiteSchedule e} {shape : ℕ → Shape}
    {W : ℕ → Type} [∀ t, Fintype (W t)] {good : ∀ t, State S start P bits shape W t → Prop}
    {deep : S.floor+1+S.drop*T ≤ start} {V : ℕ → ℕ → Type} [∀ t i, Fintype (V t i)] {w : ℕ → ℕ → ℕ}
    (M : Machine.{0,u} deep good V w) (rows : ∀ t ht, (M t ht).F.SiteRows) (number : e.Entry → ℕ)
    (bottom : Admissible good 0) (base : Site.Programs bottom.val.pack.layout)
    (q : (packHistory bottom M.epoch T).Index)

omit [NeZero D] in
private theorem fresh_relative (p : Site) (h : FreshBoxes e number p) : p.RelativeBoxes := by
  intro fs mem f hf off
  rcases h with empty | ⟨a,v,eq⟩
  · simp [empty] at mem
  · rw [eq] at mem
    obtain rfl := List.mem_singleton.mp mem
    obtain rfl := List.mem_singleton.mp hf
    rfl

/-- Sparse boxes, guard locality, sign and row schema hold at each true
retained, paid and relay vertex after the exterior rows have been appended. -/
theorem terminal_sewn_guard {L U : ℕ} (hL : tableLimit e ≤ L) (hu : ∀ z, number z ≤ U)
    (h : ∀ v, (base v).birth.Local ∧ (base v).birth.RelativeBoxes ∧
      (base v).program.CompilerFields e L U ∧ (base v).program.SignFree)
    (v : (flattenPack T ((packHistory bottom M.epoch T).term q).val.pack).layout.Site)
    (width : ℕ) (intervals : List SewnField.Interval) :
    let lineage := M.terminalPrivatePrograms rows number bottom base q v
    let p := SewnField.stage lineage.program width intervals
    lineage.birth.Local ∧ p.Schema ∧ p.RelativeBoxes ∧ p.SignFree := by
  intro lineage p
  have birth : lineage.birth.Local ∧ lineage.birth.RelativeBoxes := by
    rcases M.terminalPrivateBirthInfo rows number bottom base q v with ⟨⟨i,u⟩,rfl⟩ | fresh
    · dsimp only [lineage]
      rw [M.terminalPrivatePrograms_birth rows number bottom base q i u]
      exact ⟨(h u).1,(h u).2.1⟩
    · exact ⟨fresh.1,fresh_relative number _ fresh.2⟩
  have relative : lineage.program.RelativeBoxes := by
    unfold Site.RelativeBoxes
    rw [lineage.boxes_eq_birth]
    exact birth.2
  have fields := M.historyPrivatePrograms_compilerFields rows number bottom base hL hu
    (fun u => (h u).2.2.1) T le_rfl q v
  exact ⟨birth.1,SewnField.stage_schema _ _ _ fields.1.1,SewnField.stage_relativeBoxes _ _ _ relative,
    M.terminalPrivatePrograms_signFree rows number bottom base q (fun u => (h u).2.2.2) v⟩

end PackedHistoryCircuit.Normalized.EnrichedOuter.Machine

end BorderVNP
end Computability
end OAI
