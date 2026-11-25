import OAI.Computability.BorderVNP.PackedFrozenSelectedCarry
import OAI.Computability.BorderVNP.PackedHistoryScheduleBudget

/-! # Rekeying every inherited record at the real subdivision boundary -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.ProgramSchemas

open Crossing Cover BorderVNP.Epoch Shortening Shortening.PublicCapacity Diagonal Filter TeamScales
open PackedHistoryCircuit PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} (S : Normalized.SiteSchedule e)

/-- Reserving additional physical sites only increases the cost of this concrete padded sort. -/
theorem lookupCost_mono_slots {a b : ℕ} (h : a≤b) (queries d w : ℕ) :
    lookupCost a queries d w ≤ lookupCost b queries d w := by
  let x := Nat.clog 2 (a+queries)
  let y := Nat.clog 2 (b+queries)
  have hxy : x≤y := Nat.clog_mono_right 2 (Nat.add_le_add_right h queries)
  unfold lookupCost
  change 2^x * _ ≤ 2^y * _
  gcongr

/-- For the actual old format at any outer level, all owner queries in the
input subdivision fit a fixed quartic logarithm per reserved source row.
The entire outer fan is included, even when the intermediate format has
accumulated many retired record slots. -/
theorem eventually_subdivision_carry {a x : ℕ} (scale : EpochScales S a x) (C₀ : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r →
      let start := CoverScale.initialDepth (Cube D) r n
      let V := CoverScale.sites (Cube D) start
      let w := 60*logWidth r n
      ∀ base : Format, Fintype.card base.Rows ≤ C₀*physicalRows (bottom (D:=D) start) →
      S.floor+1+S.drop*(epochs scale.τ n) ≤ start →
      ∀ t < epochs scale.τ n,
        let shape := boundaryShape S start t
        let fmt := epoch S start w base t
        EnrichedOuter.fan S * lookupCost shape.sites (Fintype.card fmt.Rows) w w ≤ rowWork C V (logWidth r n) 4 shape := by
  obtain ⟨C,hC⟩ := eventually_carry_cost S scale C₀
  let F := S.fanIn * (2*interiors S+1)
  refine ⟨EnrichedOuter.fan S*C*F,?_⟩
  filter_upwards [hC] with n bound
  intro r hr start V w base small deep t ht shape fmt
  let first : Fin S.rounds := ⟨0,S.rounds_pos⟩
  let sub := shape.subdivide (interiors S)
  let request := Fintype.card fmt.Rows
  have req : request ≤ priorSlots S start (Fintype.card base.Rows) t first.val := by
    change Fintype.card (epoch S start w base t).Rows ≤
      epochSlots S.fanIn S.rounds (subdividedSlots S start) (freshSlots S start) (Fintype.card base.Rows) t+subdividedSlots S start t
    rw [epoch_slots S start w base deep ht.le]
    exact Nat.le_add_right _ _
  have join := bound r hr (Fintype.card base.Rows) small t ht first request req
  change 1+S.fanIn*lookupCost sub.sites request w w ≤ rowWork C V (logWidth r n) 4 (sub.parallel S.fanIn) at join
  have monotone := lookupCost_mono_slots (Nat.le_add_right shape.sites (interiors S * shape.edges)) request w w
  have one : lookupCost shape.sites request w w ≤ rowWork C V (logWidth r n) 4 (sub.parallel S.fanIn) :=
    monotone.trans ((Nat.le_mul_of_pos_left _ S.positiveFanIn).trans ((Nat.le_add_left _ 1).trans join))
  have subvol : (sub.parallel S.fanIn).volume V ≤ F*shape.volume V :=
    ((sub.parallel_volume S.positiveFanIn V).trans (Nat.mul_le_mul_left _ (shape.subdivide_volume _ _))).trans_eq
      (Nat.mul_assoc _ _ _).symm
  calc
    _ ≤ EnrichedOuter.fan S*(C*((sub.parallel S.fanIn).volume V)*(logWidth r n)^4) :=
      Nat.mul_le_mul_left _ one
    _ ≤ EnrichedOuter.fan S*(C*(F*shape.volume V)*(logWidth r n)^4) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ subvol))
    _ = _ := by unfold rowWork; ring

end Packing.Inherited.FrozenTape.ProgramSchemas

end BorderVNP
end Computability
end OAI
