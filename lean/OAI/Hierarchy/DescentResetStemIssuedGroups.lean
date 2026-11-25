import OAI.Hierarchy.DescentResetStemRead
import OAI.Hierarchy.DescentResetSharedGroupPacking

namespace OAI
/-! # Physical source-group and source-block words of each retained reset stem -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSharedCableNames
open DescentIssuedFallbackPanel DescentGL DescentSIMDLookup DescentSharedCableNames.Stage
open DescentResetCableSlots DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open DescentResetStemCompactOrder
open private Hierarchy.DescentSixParty.ClosedReset.Window.grain_at from OAI.Hierarchy.DescentResetStemRead
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



local notation "rawRank" => ((Z).rawHostRank T vertexCode).trans Fin.valEmbedding
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=groups)) rawRank) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "same" => funext (fun e=>((Z).allWidths e).symm)
local notation "wires" => installedWireNames (old) (T).home (placement).input (T).hub same (Z).bank (Z).tables
local notation "key" => DescentOrderedReset.grains W B.count B.order


local notation "A" => input.placement
local notation "digitsIn" => S.resetInputDigits ctl.base ctl.radix i
local notation "c" => (T).commonDepth
local notation "m" => S.groupWidth k tail i+k
local notation "before" => input.order.trans Fin.valEmbedding
local notation "fits" => B.frame.enough.trans (Nat.sub_le ..)


local notation "Slot" => Fin (2^(m-c))×Fin (2*(A).cap)

open DescentResetFieldAssembler DescentResetWindowResidentSources
local notation "R" => blocks B
local notation "rank" => (Z).rawHostRank T vertexCode
local notation "shapeId" => (Z).codeHost T vertexCode
local notation "lab" => DescentRelativeContacts.shortName c
local notation "End" => (old).graph.Edge

local notation "center" u => (receiverRoot B u)
local notation "actor" u => B.frame.host.symm (center u).1
local notation "rack" u => (center u).2
local notation "site" s j => endSite A s (beforeStem B j)

/-- A single shared source-plane address, independent of the receiver host. -/
def oldCell (x : Block k) (lo : Block (m-c)) (g₀ : Fin groups) : Block m :=
  join fits ((digits).symm (g₀,x)) lo

theorem oldCell_read (u : Host) (s : Bool) (slot : Slot) (j : End)
    (found : oldStemAt B u s slot=some j) :
    digitsIn ((rearrange B.frame.basis).symm (oldCell B u.2 slot.1 u.1.1)) =
      (((A).pos (W.graph.src (beforeStem B j).1)).1,(A).block (W.graph.src (beforeStem B j).1)) := by
  let e:=beforeStem B j
  have hit:=(atSlot_iff A before S input.valid s _ slot.2 e).mp ((Hierarchy.DescentSixParty.ClosedReset.Window.grain_at B u s slot j).mp found)
  have cell:=(port_fst A s e).symm.trans (congrArg Prod.fst hit)
  have pair:=congrArg (fun h : Stage.Host (Fin (S.groupCount i)) input.V k=>(h.1.1,h.2)) cell
  change (((A).pos (endSite A s e)).1,(A).block (endSite A s e))=
    digitsIn ((rearrange B.frame.basis).symm (oldCell B u.2 slot.1 u.1.1)) at pair
  refine pair.symm.trans ?_
  cases s with
  | false=>rfl
  | true=>
    obtain ⟨t,_,eqn⟩:=Finset.mem_map.mp ((A).peers e.1).2
    have groupEq := congrArg (fun p : Fin (S.groupCount i) × input.V => p.1) eqn
    change ((A).pos (W.graph.dst e.1)).1=((A).pos (W.graph.src e.1)).1 at groupEq
    exact Prod.ext groupEq ((A).same e.1).symm

theorem cell_group (u : Host) (s : Bool) (slot : Slot) (j : End)
    (found : oldStemAt B u s slot=some j) :
    compress (groupDomain digitsIn B.frame.basis fits () ((digits).symm (u.1.1,u.2)))
      (digitsIn ((rearrange B.frame.basis).symm (oldCell B u.2 slot.1 u.1.1))).1.val =
    compress (groupDomain digitsIn B.frame.basis fits (actor u) (rack u))
      (((A).pos (W.graph.src (beforeStem B j).1)).1.val) := by
  rw [oldCell_read B u s slot j found]
  rfl

theorem cell_fine (u : Host) (s : Bool) (slot : Slot) (j : End)
    (found : oldStemAt B u s slot=some j) :
    ((rearrange B.frame.basis).symm (oldCell B u.2 slot.1 u.1.1)).val%2^k =
      ((A).block (W.graph.src (beforeStem B j).1)).val :=
  congrArg (fun p : Fin (S.groupCount i)×Block k=>p.2.val) (oldCell_read B u s slot j found)
end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
