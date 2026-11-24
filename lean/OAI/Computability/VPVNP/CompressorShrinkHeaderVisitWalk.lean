import OAI.Computability.VPVNP.CompressorShrinkHeaderGreedyWindow
import OAI.Computability.VPVNP.CompressorWindowPackets
import OAI.Computability.VPVNP.CompressorShrinkHistoryDirectory

/-! # Three chronological header packets for an actual shrinking level -/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkHeaderGreedyPackets

open BurstRAM Compression BlockPlanner DescriptorSpace BlockHeaderRun
open scoped Fin.CommRing

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k} (B : S.Templates)
  (f : B.Entry → R) (hf : B.IsSolution f) (i : Fin S.steps) {g : ℕ}
  (X : State (ShrinkBlockInputs.a i) (packingLaneBits (ShrinkBlockInputs.a i) g))
  (sel : SelectedScore.Selection B X) (tape : List Bool)
local notation "v" => PairSimulation.TraversalRows.shrinkLevel B f hf i X sel tape
local notation "script₀" => BlockProgram.script B
variable {w : ℕ} (base : Word w) (positions blocks t : ℕ)
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pub" => Schedule.Ports.data (Workspace.ports (Schedule.arity (BlockPlanner.Script.catalog script₀)) base)
local notation "st" => (levelStart L (BlockPlanner.Script.levelsPerBlock script₀*t) : Word w)

/-- Private-fuel bound for any of the three header calls, obtained from the lengths of both
scalar-row recipes and the descriptor-head publisher. -/
def headerClock := (Scalars.advanceRow (.terminal (ShrinkBlockInputs.a i))
    (.shrink (ShrinkBlockInputs.a i) (ShrinkBlockInputs.b i))).recipe.code.length +
  (Scalars.advanceRow (.shrink (ShrinkBlockInputs.a i) (ShrinkBlockInputs.b i))
    (.terminal (ShrinkBlockInputs.b i))).recipe.code.length +
  (DescriptorHeads.publisher (BlockProgram.geometry B)).recipe.code.length + 1

set_option maxHeartbeats 600000 in
theorem header_walk (old new : Fin (L).levels) (hOld : (script₀).levelsPerBlock*t+i.val=old.val)
    (hNew : (script₀).levelsPerBlock*t+(i.val+1)=new.val) (m : Memory w)
    (run : Substep v L old new (by change 6 ≤ 54; decide) m) (fit : endAddress L < 2^w)
    (entry : LevelFields.Entry L ((script₀).levelsPerBlock*t) pub st m)
    (head : BlockHeaderPlan.firstHeader.eval pub st m=header w L 0)
    (pitch : (pub 1-1).val < levelStart L old) (count : (pub 3).val < levelStart L old)
    (bound : ℕ) (enough : headerClock B i ≤ bound) :
    SourceWalk (Window.Raw (A:=script₀) L base t bound) (headers B i) m (reports v L old new m) := by
  let mid := inputMemory v L old m
  let next := outputMemory v L old new m
  let r₀ := scalarReport (inputRow v) (header w L old) (header w L old) m
  let r₁ := scalarReport (outputRow v) (header w L old) (header w L new) mid
  let r₂ := headReport L new next
  let q := headers B i
  have qlen : q.length=3 := rfl
  have hq₀ : 0 < q.length := by omega
  have hq₁ : 1 < q.length := by omega
  have hq₂ : 2 < q.length := by omega
  obtain ⟨h₀,h₁,h₂⟩ := HeaderPacket.substep v run fit ((script₀).levelsPerBlock*t) i.val hOld hNew pub st entry head pitch count
  have support (mem : Memory w) (j : Fin q.length) :
      HeaderOperands.Supported (Window.operandRegion script₀ L base) pub st mem q[j.val] :=
    HeaderOperands.substep _ _ _ _ _ _ _ (.inl rfl) (.inr (.inl rfl)) _ (List.getElem_mem ..)
  have c₀ : (inputRow v).recipe.code.length+1 ≤ bound := by
    change (inputRow v).recipe.code.length+(outputRow v).recipe.code.length+
      (DescriptorHeads.publisher (L).shape).recipe.code.length+1 ≤ bound at enough
    omega
  have c₁ : (outputRow v).recipe.code.length+1 ≤ bound := by
    change (inputRow v).recipe.code.length+(outputRow v).recipe.code.length+
      (DescriptorHeads.publisher (L).shape).recipe.code.length+1 ≤ bound at enough
    omega
  have c₂ : (DescriptorHeads.publisher (L).shape).recipe.code.length+1 ≤ bound := by
    change (inputRow v).recipe.code.length+(outputRow v).recipe.code.length+
      (DescriptorHeads.publisher (L).shape).recipe.code.length+1 ≤ bound at enough
    omega
  change SourceWalk _ [q[0],q[1],q[2]] m ([r₀]++([r₁]++[r₂]))
  refine SourceWalk.next (rs:=[r₀]) ⟨_,_,c₀,h₀,support m ⟨0,hq₀⟩⟩ ?_
  simp only [eventLog,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  refine SourceWalk.next (rs:=[r₁]) ⟨_,_,c₁,h₁,support mid ⟨1,hq₁⟩⟩ ?_
  simp only [eventLog,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  exact SourceWalk.singleton ⟨_,_,c₂,h₂,support next ⟨2,hq₂⟩⟩

end CompressorRecords.ShrinkHeaderGreedyPackets

end

end VPVNP
end Computability
end OAI
