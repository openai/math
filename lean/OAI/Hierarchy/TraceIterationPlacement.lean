import OAI.Hierarchy.TraceArchivePlacement
import OAI.ThreeFlat.Diagonal.TraceIterationLimits
import OAI.Hierarchy.TraceRetainedBounds
import OAI.Hierarchy.TraceDescriptorScan

namespace OAI
/-! # Relocating the native repeated-stage verifier inside a fixed trace sector -/

noncomputable section
namespace Hierarchy.TraceAdmission
open ThreeFlat Diagonal Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM TraceDistribution NavigationDirectory NavigationPass Filter
open scoped Classical BigOperators

variable {F : Type} [Field F] (B : Block F)

theorem sector_placement_room {w : ℕ} (hw : 1≤w) :
    let J := 2^(32*w)
    8*(2^w)^4 ≤ J ∧ 16*J+8*(2^w)^4 < 2^(64*w) := by
  let J := 2^(32*w)
  change 8*(2^w)^4≤J ∧ 16*J+8*(2^w)^4<2^(64*w)
  have small : 8*(2^w)^4≤J := calc
    _ = 2^(3+w*4) := by rw [pow_add,pow_mul]; norm_num
    _ ≤ J := Nat.pow_le_pow_right (by decide) (by omega)
  have top : 17*J<2^(64*w) := calc
    _ ≤ 2^5*J := Nat.mul_le_mul_right _ (by decide)
    _ = 2^(5+32*w) := (pow_add ..).symm
    _ < _ := Nat.pow_lt_pow_right (by decide) (by omega)
  exact ⟨small,by omega⟩

/-- The true schedule and packed histogram at the chosen archive addresses fit
for all sufficiently large trace widths. The terminal edge count is arbitrary,
since it changes header values and leaves the directory length fixed. -/
theorem eventual_iteration_limits {u s : ℕ→ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop, ∀ (_fits : B.blockCharge*s w≤u w+1-w/2) (a : Archive)
      (β edges : ℕ) (cur : Word (64*w)) (_alpha : a.K=B.alphabetCap)
      (_atBase : ArchivePlacement a β w) (_pointer : cur.val=a.control),
      let k:=u w+1-w/2
      let steps:=(B.repeat (s w)).directory (k-(B.repeat (s w)).charge) k
      a.TraceLimits (2^w) cur steps edges (2^(3*w/5)) := by
  filter_upwards [eventual_stage_headers B scale,eventual_stage_heap B scale,
    eventual_record_length B scale,eventually_ge_atTop 7] with w headers heap record hw
  intro fits a β edges cur alpha atBase pointer k steps
  have hr : (a.directory steps edges (64*w)).length≤2^(3*w/5) := by
    rw [Archive.directory_length]
    exact headers _ _
  have bytes : (64*w)*a.histWords steps≤2^(3*w/5) := by
    simpa only [Archive.histWords,alpha,steps,k,stageCounts,Nat.mul_comm,Nat.mul_left_comm,
      Nat.mul_assoc] using record fits
  have words : a.histWords steps≤2^(3*w/5) :=
    (Nat.le_mul_of_pos_left _ (by omega : 0<64*w)).trans bytes
  have bounds := placement (β:=β) hw hr words (heap fits) bytes
  refine ⟨by rw [atBase.seed,atBase.header],?_,?_,?_,bounds.2.2.2.1,bytes⟩
  · simpa only [atBase.seed,atBase.dense] using bounds.1
  · simpa only [atBase.dense,atBase.heap] using bounds.2.1
  · simpa only [atBase.heap,pointer,atBase.control] using bounds.2.2.1

end Hierarchy.TraceAdmission

end
end OAI
