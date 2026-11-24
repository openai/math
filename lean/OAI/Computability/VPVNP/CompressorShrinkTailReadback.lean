import OAI.Computability.VPVNP.CompressorShrinkScheduledTail

/-! # All DFS header words after the terminal shrinking group

The fourteen address publications preserve the preceding four term words.
The eighteen publications together preserve the twelve metadata words and
the two successor fields written by the first group.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkScheduledTail

open BurstRAM DescriptorSpace BlockPlanner PhaseRecipe Schedule Compression SourceOnline SourceTransport
open scoped Fin.CommRing

variable {w : ℕ} {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
variable {base : Word w} {positions blocks t cap : ℕ} {i : Fin S.steps}
variable {g : ℕ} {X : State (ShrinkBlockInputs.a i) (packingLaneBits (ShrinkBlockInputs.a i) g)} {m : Memory w}
local notation "prog" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (arity (Script.catalog prog)) base
local notation "pub" => Ports.data pt
local notation "first" => Script.levelsPerBlock prog * t
local notation "st" => (levelStart L (first) : Word w)
local notation "here" => levelStart L (first+i.val)
local notation "nextHead" => levelStart L (first+(i.val+1))

variable {ms ps : List (Packet (BlockProgram.script B) w)}
    (r : Result B base positions blocks t cap i X m ms ps)

include r

theorem Result.payload (j : Fin 12) :
    post m ps (here+15+j.val) =
      (BlockMetadata.fieldExprs (L).shape i.val B.recordLimit (slotDegree S) (BlockMetadata.shrinkFields B i) j).eval pub st m :=
  (r.metaCell _ (.inl (by have := j.isLt; omega))).trans (r.baseFields.payload j)

theorem Result.next_words :
    post m ps (nextHead+14) = m (here+14) + ((B.recordLimit+2 : ℕ) : Word w)*(ShrinkPreimages.oldCount X : Word w) ∧
      post m ps (nextHead+27) = (BlockMetadata.Role.shrink.code : Word w) := by
  have size : levelHeaderWords L = 66 := rfl
  have gap : here+66 ≤ nextHead := by
    rw [show first+(i.val+1)=(first+i.val)+1 by omega]
    simp only [levelStart,Nat.succ_mul,levelWords,size]
    omega
  exact ⟨(r.metaCell _ (.inr (by omega))).trans r.baseFields.successor,(r.metaCell _ (.inr (by omega))).trans r.baseFields.tag⟩

theorem Result.term_word (j : Fin 4) :
    post m ps (here+36+j.val) = (BlockHeadStability.shrinkTerms B i j).eval pub st (post m ms) := by
  rw [r.image]
  have keep := r.published.dataGroup.source.outside (here+36+j.val) (.inl (by have := j.isLt; omega))
  exact keep.trans (r.published.termGroup.source.stored j)

theorem Result.data_word (j : Fin 14) :
    post m ps (here+40+j.val) = (PublishedHeads.dataValues B i j).eval pub st (termImage B base positions blocks t i (post m ms)) := by
  rw [r.image]
  exact r.published.dataGroup.source.stored j

end CompressorRecords.ShrinkScheduledTail

end VPVNP
end Computability
end OAI
