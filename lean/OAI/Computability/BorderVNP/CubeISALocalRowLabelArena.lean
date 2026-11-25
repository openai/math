import OAI.Computability.BorderVNP.CubeISALocalRowLabelPrefix
import OAI.Computability.BorderVNP.CubeISALocalRowPinnedBoot

/-! # The label and interval passes in the pinned cube arena

The incoming sparse tables determine the actual cable, delivery and cell counts.
The arena supplies the remaining nine words of the chooser and interval frame
through the jointly overlaid processor literal. A single high-water bound covers
all of these words and both scratch spans.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LocalRow

open BorderVNP.Cube VPVNP.BurstRAM CubeHeaderInstall

/-- The chooser's contiguous scratch chain ends below the power table. -/
private theorem label_arena_order (a : CubeArena.Layout) :
    a.header.header ≤ a.publicBase ∧ a.publicBase ≤ a.heads ∧ a.heads ≤ a.nodes ∧
    a.nodes ≤ a.demands ∧ a.demands ≤ a.cableMean ∧ a.cableMean ≤ a.dataMean ∧
    a.dataMean ≤ a.widthBase ∧ a.alphabet ≤ a.widthBase ∧ a.widthBase ≤ a.ordinalBase ∧
    a.ordinalBase ≤ a.powerBase := by
  have first := (arenaExtents a).1
  unfold Inputs.packetBase at first
  dsimp only [CubeArena.Layout.publicBase,CubeArena.Layout.vertexBase,CubeArena.Layout.singleBank,
    CubeArena.Layout.heads,CubeArena.Layout.nodes,CubeArena.Layout.demands,CubeArena.Layout.cableMean,
    CubeArena.Layout.dataMean,CubeArena.Layout.widthBase,CubeArena.Layout.ordinalBase,CubeArena.Layout.powerBase]
  omega

/-- Recover the chooser and directed-interval room from the physical pin vector
and the counts in the published sparse frame. The only content-dependent bounds
are on the incoming sparse row names and their total encoded width. -/
theorem BootPins.labelPrefixFits {w : ℕ} {pub : Arg → Word w} {f : BroadcastFrame}
    {bits : List Bool} {m : Memory w} (a : CubeArena.Layout) (old : Fin 81 → Word w)
    (fresh profile gates outputs width off ell : ℕ)
    (pins : BootPins pub f (jointFields (a.extension old) fresh profile gates outputs width off ell
      a.header.d a.n a.header.blocks a.b a.h a.s) bits m) :
    let base := (pub 0).val
    let before := readings m
    let t := LabelIndex.layout base before
    LabelIndex.Endpoints t before → t.cableCount = a.cables → t.cells = a.cells →
    t.cables+t.cableCount*3 ≤ a.publicBase → t.deliveries+t.deliveryCount*7 ≤ a.publicBase →
    base+58 < a.header.header → 0 < a.header.d → a.stop < 2^w →
    LabelIndex.wordEnvelope a.alphabet (LabelIndex.inputWidth t before) < 2^w →
    LabelPrefixFits base w before := by
  intro base before t ep count cells cab del frame positive top env
  obtain ⟨header,labels,heads,nodes,demand,cable,data,alphabet,widths,ordinals⟩ := label_arena_order a
  have endPower := (arenaExtents a).2.2
  have field (k v : ℕ) (eq : a.operand k = some v) (le : v ≤ a.powerBase) : before (base+k) = v :=
    pins.arenaOperand a old fresh profile gates outputs width off ell eq (by omega)
  have p48 := field 48 _ (show a.operand 48 = some a.publicBase from rfl) (by omega)
  have p49 : t.heads = a.heads := field 49 _ rfl (by omega)
  have p50 : t.nodes = a.nodes := field 50 _ rfl (by omega)
  have p51 : t.data = a.demands := field 51 _ rfl (by omega)
  have p52 : t.cableMean = a.cableMean := field 52 _ rfl (by omega)
  have p53 : t.dataMean = a.dataMean := field 53 _ rfl (by omega)
  have p56 : t.labels = a.alphabet := field 56 _ rfl (by omega)
  have p57 : before (base+57) = a.widthBase := field 57 _ rfl (by omega)
  have p58 : before (base+58) = a.ordinalBase := field 58 _ rfl (by omega)
  have alloc : LabelIndex.Allocated t := by
    refine ⟨by omega,by omega,?_,?_,?_,?_⟩
    · rw [p49,cells,p50]; rfl
    · rw [p50,count,p51,Nat.mul_comm a.cables 8]; rfl
    · rw [p51,cells,p52]; rfl
    · rw [p52,p56,p53,← pow_two]; rfl
  refine ⟨ep,alloc,p56 ▸ pow_pos positive _,?_,?_,?_,?_,by change LabelIndex.wordEnvelope t.labels _ < _; rwa [p56],?_,?_,?_⟩
  · rwa [p48]
  · rw [p48]; omega
  · change before (base+48)+t.cells ≤ t.heads
    rw [p48,cells,p49]; rfl
  · change t.dataMean+t.labels ≤ 2^w
    rw [p53,p56]; exact (show a.widthBase ≤ 2^w by omega)
  · change before (base+48)+t.cells ≤ before (base+57)
    rw [p48,p57,cells]; exact (show a.heads ≤ a.widthBase by omega)
  · change before (base+57)+t.labels^2 ≤ before (base+58)
    rw [p57,p56,p58]; rfl
  · change before (base+58)+t.cableCount ≤ 2^w
    rw [p58,count]; exact (show a.powerBase ≤ 2^w by omega)

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI
