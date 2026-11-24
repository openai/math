import OAI.Computability.VPVNP.CompressorBlockMetadataPackets
import OAI.Computability.VPVNP.CompressorCurrentGraphFrame

/-! # Current-graph and startup cells preserved by the DFS metadata -/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BlockMetadata

open BurstRAM Compression DescriptorSpace CurrentGraph

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
variable {w : ℕ} {base : Word w} {positions blocks t step : ℕ} {role : Role} {fields : Fields}
variable {m : Memory w} {oldSites : ℕ} {rs : List (Report w)}
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "i" => BlockPlanner.Script.levelsPerBlock (BlockProgram.script B)*t+step
local notation "old" => levelStart L i
local notation "new" => levelStart L (i+1)

theorem Published.graphFrame (P : Published B base positions blocks t step role fields m oldSites rs)
    (x : ℕ) (hx : graphCell L i x ∨ graphCell L (i+1) x ∨ startupCell L x) :
    after m (eventLog rs) x = m x := by
  have adv (j : ℕ) : levelStart L (j+1) = levelStart L j+levelWords L := by
    simp only [levelStart,Nat.succ_mul,Nat.add_assoc]
  have width : 66 ≤ levelWords L := by
    have sz : levelHeaderWords L=66 := rfl
    simp only [levelWords,sz]
    omega
  have next := adv i
  have tail : levelStart L (BlockPlanner.Script.levelsPerBlock (BlockProgram.script B)*t+(step+1))=new := by
    rw [← Nat.add_assoc]
  have ptr (l : ℕ) : incidenceStart L l = levelStart L l+66 := rfl
  have fields : (L).shape.scalarFields=54 := rfl
  rcases hx with h|h|⟨j,hj,rfl⟩
  · rcases h with h|h
    · apply P.outside <;> omega
    · rw [fields,ptr] at h
      apply P.outside <;> omega
  · rcases h with h|h
    · apply P.outside <;> omega
    · rw [fields,ptr] at h
      apply P.outside <;> omega
  · have floor := levelStart_mono L (Nat.zero_le i)
    by_cases zero : i=0
    · have here : old=levelStart L 0 := congrArg _ zero
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      apply P.outside <;> omega
    · have one : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr zero
      have top := levelStart_mono L one
      have first := adv 0
      change levelStart L 1 = levelStart L 0 + levelWords L at first
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      apply P.outside <;> omega

/-- The eight original cursor words survive every metadata publication,
including the first substep, whose input header is the first level. -/
theorem Published.cursorFrame (P : Published B base positions blocks t step role fields m oldSites rs)
    (x : ℕ) (hx : frameCell L x) : after m (eventLog rs) x = m x := by
  have floor := levelStart_mono L (Nat.zero_le i)
  have successor := levelStart_mono L (show i ≤ BlockPlanner.Script.levelsPerBlock (BlockProgram.script B)*t+(step+1) by omega)
  unfold frameCell at hx
  apply P.outside <;> omega

end CompressorRecords.BlockMetadata

end VPVNP
end Computability
end OAI
