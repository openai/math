import OAI.Hierarchy.DescentSeedNativeStartup
import OAI.Hierarchy.DescentPriorResetArchive
import OAI.Hierarchy.DescentResetPriorRegisterRoom
import OAI.Hierarchy.DescentResetPublicCuts
import OAI.Hierarchy.DescentSeedTokenPrice
import OAI.Hierarchy.DescentSeedTokenStartup

namespace OAI
/-! # The published predecessor checkpoints precede the next date -/
namespace Hierarchy.DescentDatedAddressBook.PriorResetArchive
open DescentCompiler DescentInitialHost DescentSixParty DescentSixParty.Chronology DescentSIMDLookup
open DescentDatedSeedStartup DescentResetRetainedSetup DescentOperandStateBanks
noncomputable section
set_option quotPrecheck false

def Fits (p : PriorResetArchive) (L : DescentResetRetainedSetup.Layout) (limit : ℕ) : Prop:=
  L.priorMetaLimit p.seed p.nodeBase≤limit ∧ L.priorOperandLimit p.arguments≤limit

theorem Fits.before {p : PriorResetArchive} {L : DescentResetRetainedSetup.Layout} {a b : ℕ}
    (h : p.Fits L a) (grow : a≤b) : p.Fits L b:=⟨h.1.trans grow,h.2.trans grow⟩

variable {F : Type} [Field F] {c p : ℕ} (G : PoweredGadget F) (op : RotorSpec)
    (X : Catalyst.Approximation F c p) (R : ℕ) (l : DescentDatedSeedStartup.Layout)
    (k H groups payload Z : ℕ) (L : DescentResetRetainedSetup.Layout)
local notation "node" => DescentDatedSeedStartup.Input.nodeChart l k H groups
local notation "top" => DescentDatedSeedStartup.endAddress X l H groups k
local notation "finish" => (node).seedEnd top
local notation "init" => initial G op X R l k H groups payload Z
local notation "lanes" => DescentDatedSeedStartup.Primitive.paletteLanes G op l.seedWidth Z payload k

theorem initial_limits (metadataChart : L.previousChart=node) (args : L.previousArgs=3*l.groupsPerNode) :
    (init).Fits L (DescentDatedSeedStartup.Primitive.initialEnd X R l.seedWidth payload k H groups lanes finish) :=by
  have blocks := congrArg DescentDatedNodeMetadata.Chart.blocks metadataChart
  have rows : L.previousLayout.rows=H*chunks groups l.operandLanes:=congrArg DescentDatedNodeMetadata.Chart.rows metadataChart
  have first : (init).Fits L finish:=by
    constructor
    · change L.previousChart.seedEnd top≤(node).seedEnd top
      rw [metadataChart]
    · have endInput:=DescentDatedSeedStartup.fences X l H groups k
      have old : L.priorOperandLimit (init).arguments = DescentDatedSeedStartup.directoryBase X l H groups k:=by
        change _=Seed.Physical.endAddress X _ _ _ _ _ _
        unfold DescentResetRetainedSetup.Layout.priorOperandLimit Seed.Physical.endAddress
        change L.blocks=2^k at blocks
        rw [args,blocks,rows]
        rfl
      rw [old]
      exact endInput.2.2.trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..))
  apply first.before
  unfold DescentDatedSeedStartup.Primitive.initialEnd
  rw [DescentSeedTokenTransposition.address_affine]
  apply le_trans _ (Nat.le_add_right ..)
  unfold DescentPackedSeed.Primitive.Source.finish DescentPackedSeed.Primitive.Source.raw
  omega

variable {P : Type} (v : PhysicalOrdinary F P)

theorem ordinary_limits (b : ℕ) (metadataChart : L.previousChart=v.nodeChart) (nodes : v.metadata.chart=v.nodeChart)
    (spanBits : v.metadata.spanBits=v.resolver.size+2) (shape : v.operandBook=v.finalChart)
    (args : L.previousArgs=v.resolver.operands) :
    (ordinary v b).Fits L (v.returnedEnd b):=by
  have blocks : L.blocks=v.resolver.blocks:=congrArg DescentDatedNodeMetadata.Chart.blocks metadataChart
  have rows : L.previousLayout.rows=v.resolver.rows:=congrArg DescentDatedNodeMetadata.Chart.rows metadataChart
  have ends : L.priorMetaLimit false (ordinary v b).nodeBase = v.metaEnd b:=by
    change L.previousChart.endAddress (v.nodeBankBase b)=v.metadata.ordinaryEnd (v.metaStart b)
    unfold MetadataReturn.ordinaryEnd MetadataReturn.endAddress MetadataReturn.unpackEnd MetadataReturn.headerEnd
    rw [metadataChart,nodes,spanBits]
    rfl
  have operandEnd : L.priorOperandLimit (ordinary v b).arguments=v.operandEnd b:=by
    unfold DescentResetRetainedSetup.Layout.priorOperandLimit PhysicalOrdinary.operandEnd
    rw [shape,args,blocks,rows]
    change _=v.finalChart.out (v.metaEnd b)+(7*v.resolver.operands*v.resolver.blocks)*v.resolver.rows+_
    simp only [Nat.mul_assoc]
    rfl
  have beginAt:v.metaEnd b≤v.operandEnd b:=by
    rw [PhysicalOrdinary.operandEnd,v.operandBook.affine]
    exact Nat.le_add_right ..
  have middle:v.operandEnd b≤v.primitiveEnd b:=(v.primitive_spent (v.operandEnd b)).2
  have last:v.primitiveEnd b≤v.returnedEnd b:=by
    exact ((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)
  change L.priorMetaLimit false (ordinary v b).nodeBase≤_ ∧ L.priorOperandLimit (ordinary v b).arguments≤_
  rw [ends,operandEnd]
  exact ⟨(beginAt.trans middle).trans last,middle.trans last⟩

theorem reset_limits (out : ResetOutput) (b : ℕ) (metadataChart : L.previousChart=out.metadata.chart)
    (blocks : L.blocks=out.receiver.blocks) (rows : L.previousLayout.rows=out.receiver.hosts*chunks out.receiver.groups out.receiver.lanes)
    (args : L.previousArgs=out.argumentSlots) : (reset out b).Fits L (out.metadataEnd b):=by
  constructor
  · change L.previousChart.endAddress (out.metadata.headerEnd (out.primitiveEnd b))≤_
    rw [metadataChart]
    exact le_rfl
  · have upper : L.priorOperandLimit (reset out b).arguments=out.finalEnd b:=by
      unfold DescentResetRetainedSetup.Layout.priorOperandLimit ResetOutput.finalEnd DescentResetNodeBooks.endAddress
      rw [args,blocks,rows]
      simp only [DescentResetNodeBooks.rows,DescentResetNodeBooks.rounded,ResetOutput.nodeNames,Nat.mul_assoc]
      rfl
    rw [upper]
    exact (out.cuts b).metadata

end
end Hierarchy.DescentDatedAddressBook.PriorResetArchive

end OAI
