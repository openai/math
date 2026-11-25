import OAI.ThreeFlat.Diagonal.TraceNodeBankScale
import OAI.ThreeFlat.Diagonal.TraceArchiveSource
import OAI.Hierarchy.TraceSeedDirectories
import OAI.ThreeFlat.Diagonal.PhysicalSeedLayer

namespace OAI
/-! # Bounding the number of terminal rows in the physical archive -/
namespace Hierarchy.GridPhysicalAdmission
open ThreeFlat Diagonal PhysicalStage NavigationPass NavigationDirectory
open RAM RAM.NavigationNodeRows RAM.PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open TraceDistribution TraceAdmission TraceNodeHeaders NodePublication Filter
open scoped Classical Topology
noncomputable section
variable {F : Type} [Field F] [Fintype F] (B : Block F)

omit [Fintype F] in
/-- The geometric number of physical output rows is public before a selector is read. -/
theorem eventual_root_count {u s : ℕ→ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop, ∀ {k : ℕ} (_axis : k=u w+1-w/2) (_fits : B.blockCharge*s w≤k)
      (off slots cap static : ℕ),
      let a:=TraceSeedWriter.archive B w k off slots cap static
      let P:=B.repeat (s w)
      let ops:=P.directory (k-P.charge) k
      (TraceRecovery.lastLayer a.K ops a.cursor a.seedLayer).count≤2^(3*w/5) := by
  filter_upwards [record_room scale 1] with w volume
  intro k axis fits off slots cap static a P ops
  have charge : P.charge≤k := by rw [show P.charge=(B.repeat (s w)).charge from rfl,B.charge_repeat];exact fits
  have split : P.charge+(k-P.charge)=k := by omega
  have start : a.seedLayer.count=k*2^k := rfl
  obtain ⟨q,member,actual⟩:=TraceRecovery.lastLayer_mem a.K ops a.cursor a.seedLayer
  have upper:=program_site_count P a.K (k-P.charge) k a.cursor a.seedLayer (by rw [split,start]) q member
  rw [actual,split] at upper
  rw [←axis] at volume
  exact upper.trans <| (show k*2^k≤1+k*2^k by omega).trans <|
    ((Nat.le_mul_of_pos_left _ (by positivity : 0<1*(s w+1))).trans
      (Nat.le_mul_of_pos_right _ (by omega))).trans volume


end
end Hierarchy.GridPhysicalAdmission

end OAI
