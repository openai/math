import OAI.Hierarchy.DescentClosedLocalRoster
import OAI.Hierarchy.DescentPhysicalFallbackPanel

namespace OAI
/-! # The original signed half-stem array at either endpoint of a reset cable -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentIssuedFallbackPanel DescentGL DescentSIMDLookup DescentSharedCableNames.Stage
open DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks DescentSharedCableNames
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

def beforeStem : (old).graph.Edge↪Grain A :=
  (Equiv.sigmaCongrRight fun e=>finCongr (congrFun B.count_eq e)).toEmbedding

theorem beforeStem_end (s : Bool) (j : (old).graph.Edge) :
    endSite A s (beforeStem B j)=ends (old).graph s j := by cases s <;> rfl

theorem stem_cell (u : Host) (s : Bool) (j : (old).graph.Edge)
    (atCell : (blocks B).src (stemParent B (s,j))=u ∨ (blocks B).dst (stemParent B (s,j))=u) :
    let e:=beforeStem B j
    ((A).pos (endSite A s e)).2=B.frame.host.symm (receiverRoot B u).1 ∧
    group c (rearrange B.frame.basis (oldBlock digitsIn (Stage.home A (endSite A s e))))=(receiverRoot B u).2.val := by
  obtain ⟨left,right⟩:=stem_receiver_root B s j
  have sameRoot : receiverRoot B u=(((T).code ((T).home (ends (old).graph s j))).1,
      (Z).rootBlock T (.inr ((T).home (ends (old).graph s j)))) := by
    rcases atCell with atLeft|atRight
    · rw [←atLeft];exact left
    · rw [←atRight];exact right
  dsimp only
  rw [sameRoot,beforeStem_end]
  constructor
  · apply B.frame.host.injective
    rw [Equiv.apply_symm_apply]
    exact (B.frame.homeHost _).symm
  · exact (B.frame.homeHigh _).symm

/-- A half-stem is recovered at *either* post-reset endpoint by its old
physical polarity and the previous signed slot of its measured low coordinate. -/
def stems_chart (u : Host) : Part (blocks B) u (stemParent B)↪Fin (2*(2^(m-c)*(2*(A).cap))) := by
  let oldAddress:=fun s e=>localAddress («c»:=c) A before S input.valid digitsIn B.frame.basis s (beforeStem B e)
  let encode:=fun x : Bool×(old).graph.Edge=>finProdFinEquiv (finTwoEquiv.symm x.1,finProdFinEquiv (oldAddress x.1 x.2))
  refine ⟨fun x=>encode x.val,?_⟩
  rintro ⟨⟨s,x⟩,ax⟩ ⟨⟨t,y⟩,ay⟩ equalCode
  have pairEq:=finProdFinEquiv.injective equalCode
  have polar : s=t := finTwoEquiv.symm.injective (congrArg Prod.fst pairEq)
  subst t
  have place : oldAddress s x=oldAddress s y:=finProdFinEquiv.injective (congrArg Prod.snd pairEq)
  let v:=B.frame.host.symm (receiverRoot B u).1
  let hi:=(receiverRoot B u).2
  let eligible:=fun e : Grain A=>((A).pos (endSite A s e)).2=v ∧
    group c (rearrange B.frame.basis (oldBlock digitsIn (Stage.home A (endSite A s e))))=hi.val
  have read (j : (old).graph.Edge) (hp : (blocks B).src (stemParent B (s,j))=u ∨ (blocks B).dst (stemParent B (s,j))=u) :
      panel A before S input.valid digitsIn B.frame.basis fits s v hi eligible (oldAddress s j)=some (beforeStem B j) :=
    panel_at A before S input.valid digitsIn B.frame.basis fits s v hi eligible (fun _ valid=>valid)
      (beforeStem B j) (stem_cell B u s j hp)
  have physical:=read x ax.2
  rw [place,read y ay.2] at physical
  exact Subtype.ext (congrArg (Prod.mk s) ((beforeStem B).injective (Option.some.inj physical.symm)))

def rawRoster (u : Host) {b : ℕ} (contacts : Part (blocks B) u (contactParent B)↪Fin b) :=
  rawLocalRoster B u (stems_chart B u) contacts

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
