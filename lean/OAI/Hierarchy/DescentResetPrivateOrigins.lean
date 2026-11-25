import OAI.Hierarchy.DescentPrivateCandidateShelf
import OAI.Hierarchy.DescentPackedInstalledPrivate

namespace OAI
/-! # Private endpoint records from the two physically reached fallback panels -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open scoped Classical
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "placement" => B.reset.placement
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "groups" => S.groupCount (i+1)
local notation "Host" => Stage.Host (Fin groups) B.next.V k
local notation "digits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "sel" => selected placement (Z).graph (Z).positive (Z).pay (Z).circuit
local notation "dev" => DescentMixedRouter.device (Z).graph (Z).positive (Z).unit
  (placement).contact (placement).input (placement).site (placement).owner (placement).align (D:=d)
local notation "height" => GroupStage.depthBound D n f g
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))


local notation "pool" => DescentDenseHostOrder.roster (Z).graph ((Z).k-(T).commonDepth) height



local notation "nLeaf" => 2^(S.groupWidth k tail i+k-(T).commonDepth)*(2*input.placement.cap)
local notation "slotOrder" => DescentResetCableSlots.privateWire placement height (T).bookHeight
  (Z).graph (Z).positive (Z).pay (Z).circuit d

/-- Prefix leaf counts on each sign come from that sign's attained old arrivals. -/
def privatePanelCatalog : Bool→(Z).Fallback→DescentPackedFallbackTree.Panel height nLeaf := by
  rcases input with @⟨V,vFin,vDec,phase,ready,rfl,rfl,history,degree,order,vertex,edgeName,siteName⟩
  rcases B with ⟨count,rfl,oldFit,oldOrder,orderEq,reset,terminals,age,depth,keyWidth,tickets,unit,dimension,
    tapeWidth,graph,frame,roster,raw,rawGeometry,rawHub,rawValid,grain,wire,atoms,branch,capBound⟩
  exact GroupStage.leafPanel phase S ready (S.resetInputDigits ctl.base ctl.radix i)
    (order.trans Fin.valEmbedding) reset terminals frame

private theorem leaf_panel_row (s : Bool) (t : (Z).Fallback) (e : (dev (sel s (.inr t))).Edge) :
    (Z).expand T vertexCode (.inr t)
      (DescentPackedPrivateMenu.values (Z).graph ((Z).k-(T).commonDepth) height nLeaf (Z).layerBits C (Z).width s
        (slotOrder (s,.inr t) e).val ((Z).fallbackKey T s t (privatePanelCatalog B s t)))=
      (Z).actualRecord T vertexCode ((Z).privateWireAt T s (.inr t) e) := by
  rcases input with @⟨V,vFin,vDec,phase,ready,rfl,rfl,history,degree,order,vertex,edgeName,siteName⟩
  rcases B with ⟨count,rfl,oldFit,oldOrder,orderEq,reset,terminals,age,depth,keyWidth,tickets,unit,dimension,
    tapeWidth,graph,frame,roster,raw,rawGeometry,rawHub,rawValid,grain,wire,atoms,branch,capBound⟩
  exact GroupStage.tree_row phase S ready (S.resetInputDigits ctl.base ctl.radix i)
    (order.trans Fin.valEmbedding) reset terminals frame (frame.host.symm.toEmbedding.trans vertex) s t e

/-- Closing the private record reading needs just the five emitted digits.
The real rotor or the selected side's retained leaf table gives both endpoints. -/
theorem private_installed_of_values (unit : 0<(Z).unit) (s : Bool) (ticket : (Z).RootTicket T)
    (old : Fin (Fintype.card input.V)) (block : Block (T).commonDepth) (slot : Fin capacity)
    (p : PrivateOccurrence B) (raw : Fin 5→ℕ)
    (numbers : raw=DescentPackedPrivateMenu.values (Z).graph ((Z).k-(T).commonDepth) height nLeaf
      (Z).layerBits C (Z).width s slot.val ((Z).rootsOf T vertexCode unit s (privatePanelCatalog B s) ticket old block))
    (atSlot : privateRawAt B old block s ticket slot p) :
    (Z).expand T vertexCode p.1.2 raw=(Z).actualRecord T vertexCode (privateWire B p) := by
  obtain ⟨⟨side,root⟩,e⟩:=p
  obtain ⟨seen,loc,key⟩:=atSlot
  change side=s at seen
  subst side
  have host : vertexCode ((Z).rootVertex T root)=old :=congrArg Prod.fst loc
  have blk : (Z).rootBlock T root=block:=congrArg (fun z=>z.2.1) loc
  have tag : (Z).rootTicket T root=ticket:=congrArg (fun z=>z.2.2) loc
  change slotOrder (s,root) e=slot at key
  subst old
  subst block
  subst ticket
  subst slot
  rw [numbers,(Z).rootsOf_read T vertexCode unit s (privatePanelCatalog B s) root]
  cases root with
  | inl a=>exact (Z).rotor_row T vertexCode unit nLeaf s a e
  | inr t=>exact leaf_panel_row B s t e

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
