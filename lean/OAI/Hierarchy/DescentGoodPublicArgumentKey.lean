import OAI.Hierarchy.DescentGoodOccupiedTap
import OAI.Hierarchy.DescentMountedTapOccupancy

namespace OAI
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentKernelHistory DescentBundleHistory DescentLocalArchiveOrder DescentCompiler DescentColonies
open DescentResetTrunks DescentRotor DescentResetGates DescentChosenRouter DescentRouterBank
open DescentResetAttachments DescentNamedContact DescentPrimitivePalette Chronology Computability.BorderVNP.Crossing
open DescentStageEdgeReceipt ThreeFlat.Routing
open scoped Classical
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1150000
open private transportCircuit from OAI.Hierarchy.DescentInstalledNames
variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
variable {q ε : ℝ} {S : AtomSchedule} {k i z D wire hist n h C f g cut tail : ℕ} {G : PoweredGadget F}
    {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset cap ctl) (hp : 0<p) (one : 1≤R) (pos : 0<B.reset.unit) (whole : p∣B.reset.unit)
    (wide : max 1 (max B.reset.width (C*B.reset.width))≤R) (a : Archive W) (sh : WorldShape p R a.bit)
local notation "split_" => sh.granular B.count (z*G.b) B.fit hp (B.unit ▸ pos) (B.unit ▸ whole)
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "unit" => B.reset.unit/p
local notation "splitEq" => ((Nat.div_mul_cancel whole).symm : B.reset.unit=unit*p)
local notation "installed" => reentryWorldShape split_ B.reset B.terminals birth _ hp splitEq (resetMenu B) one wide
local notation "next_" => (resetArchive B p hp whole a).bit
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans cap.vertex
local notation "dense" => (B.reset.rawHostRank B.terminals vertexCode).trans Fin.valEmbedding
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=S.groupCount (i+1))) dense) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite



open DescentResetFreshWires DescentResetLocalNodes DescentOrderedWords
local notation "before_" => BitDescription.granular W B.count (z*G.b) B.fit a.bit
local notation "pre_" => (before_).batchedReset B.reset B.terminals birth unit p hp splitEq (resetMenu B)
local notation "middle_" x:arg => NodeOrder.followNames B.reblock pre_ x
local notation "where_" x:arg => resetOrigin B hp whole a x

open DescentLaneGates

open DescentPhysicalSplit DescentBundleHistory DescentResetPublicOperandBook DescentRotorOperandQueryROM.Shape
variable (side : Bool) (root : B.reset.placement.Good)
local notation "R_" => B.reset.placement
local notation "bits_" => B.reset.width
local notation "sizedHardware" => (splitEq ▸ B.reset.circuit :
  Hardware (K:=F) (C₀:=C) (u:=unit*p) R_ B.reset.graph B.reset.positive B.reset.pay)
local notation "itemEnum" => @Subtype.fintype _ (fun e => (R_).owner side ((R_).contact e) = Sum.inl root)
  (fun _ => Classical.propDecidable _) inferInstance
local instance (priority := high) publicArgumentCellEnum : Fintype (Cells B.reset.placement side root) := itemEnum
local notation "base" => (transportCircuit (b:=itemEnum) (G:=B.reset.graph) (hw:=B.reset.positive) (pay:=B.reset.pay) (sizedHardware side root))
local notation "layers_" => selectedRotorLayers R_ B.reset.graph B.reset.positive B.reset.pay sizedHardware side root
local notation "H₀" => Physical.host B.reset.graph.arcs d layers_ C bits_ (unit*p)
local notation "sizedChoice" => selected R_ B.reset.graph B.reset.positive B.reset.pay sizedHardware side (.inl root)
local notation "trueDevice" => DescentMixedRouter.device B.reset.graph B.reset.positive (unit*p)
  (R_).contact (R_).input (R_).site (R_).owner (R_).align (D:=d) sizedChoice
local notation "sizedSite" => DescentCommonPalette.rotorSiteEquiv B.reset.graph d layers_ C bits_ (unit*p)
local notation "installedSite" => DescentCommonPalette.rotorSiteEquiv B.reset.graph d
  (selectedRotorLayers R_ B.reset.graph B.reset.positive B.reset.pay B.reset.circuit side root) C bits_ B.reset.unit
local notation "src_" => (fun e : Cells R_ side root=>(DescentChosenRouter.head R_ side root) (DescentRouterSlots.root (R_).contact
  (R_).input (R_).site (R_).owner side (.inl root) (R_).align e))
local notation "dst_" => (fun e : Cells R_ side root=>(DescentChosenRouter.tail R_ side root) (DescentRouterSlots.link (R_).contact (R_).owner side (.inl root) e))
local notation "key_" => (Function.Embedding.subtype (fun e=>(R_).owner side ((R_).contact e)=.inl root)).trans birth
local notation "addr_" => DescentRotor.Ordered.orderedAddress key_ src_ dst_ B.reset.positive
variable {field query lanes nodes args : ℕ}
local notation "cfg" => publicOperandConfig B field query lanes unit unit nodes args p
local notation "physicalProgram" => DescentBatchedRotor.program (K:=F) (C₀:=C) d unit p hp (R_).contact (R_).input (R_).site (R_).owner (R_).align
  side (.inl root) B.reset.graph (DescentChosenRouter.head R_ side root) (DescentChosenRouter.tail R_ side root) base birth
local notation "physicalOrder" => DescentBatchedNodeOrder.deviceOrder (K:=F) (C₀:=C) (s:=side) (w:=.inl root) B.reset.graph B.reset.positive unit p hp
  (R_).contact (R_).input (R_).site (R_).owner (R_).align birth d (.good (DescentChosenRouter.head R_ side root)
    (DescentChosenRouter.tail R_ side root) B.reset.pay (base))
local notation "progAt" actor:arg => physicalProgram (sizedSite actor)
local notation:max "ordAt" actor:arg node:arg => physicalOrder (sizedSite actor) node
local notation "mountedSite" v:arg => (⟨(side,.inl root),installedSite v⟩ : B.reset.bank.Site)
local notation "mountedNode" v:arg z:arg => (mountedGoodNode R_ B.reset.graph B.reset.positive B.reset.pay B.reset.circuit birth
  d unit p hp splitEq side root v).symm z
local notation "shapeBook" => DescentDenseHostOrder.roster B.reset.graph (cfg).residual (cfg).maxDepth
local notation "physicalPublic" => (cfg).rotor.PublicArgument (K:=F) (mult:=C) (hw:=B.reset.positive) (pay:=B.reset.pay) B.reset.graph d p hp (R_).contact (R_).input (R_).site (R_).owner
  (R_).align side (.inl root) (DescentChosenRouter.head R_ side root) (DescentChosenRouter.tail R_ side root) base birth

local notation:max "pub" actor:arg node:arg position:arg => physicalPublic (sizedSite actor) node position

/-- Transport a dependent pair back to the original site enumeration. -/
private theorem originalArgumentPair {A V : Type} (e : A ≃ V) (N : V→Type)
    (a : A) (z : N (e a)) (b : V) (t : N b)
    (same : (⟨e a,z⟩ : Sigma N)=⟨b,t⟩) :
    (⟨a,z⟩ : Σa,N (e a))=⟨e.symm b,Eq.ndrec (motive:=N) t (e.apply_symm_apply b).symm⟩ := by
  apply Sigma.ext (((e.symm_apply_apply a).symm).trans (congrArg e.symm (congrArg Sigma.fst same)))
  exact (Sigma.mk.inj same).2.trans (eqRec_heq (φ:=N) (e.apply_symm_apply b).symm t).symm

/-- The physical public case of the exhaustive argument decoder identifies its
own occupied tap and its true incoming or outgoing socket. -/
theorem good_public_argument_key (actor : (DescentCommonPalette.rotor B.reset.graph).Site)
    (z₀ : (progAt actor).Node) (arg : ℕ) (external : pub actor z₀ arg) (x : (cfg).Data B.reset.n)
    (rows : GoodTapRows (p:=p) (field:=field) (query:=query) (lanes:=lanes) (nodes:=nodes) (args:=args) (grain:=p)
      B side root x)
    (active : ((cfg).oldConfig.header ((cfg).basic x) 0).val≠0)
    (shape : ↥shapeBook) (depth : (((cfg).reg x) 1).val=(B.reset.goodLabel B.terminals root).val.1+1)
    (safe : (((cfg).reg x) 2).val%2=0)
    (ranked : (((cfg).reg x) 3).val=(DescentDenseHostOrder.localRank B.reset.graph (cfg).residual (cfg).maxDepth shape).val)
    (located : shape.val=.good side ((),(B.reset.goodLabel B.terminals root).val.2) actor)
    (y : NodeOrder.All next_) (origin : where_ y=.inr (.inr ⟨mountedSite actor,mountedNode actor z₀⟩)) :
    ∃host number word count pin,∃out : PublicSocket B host unit word pin number,
      (cfg).mixed B.reset.graph (ordAt actor z₀).val arg x=some (number,word,count,pin) ∧
      keyCable installed (middle_ y) arg=some (out.face.val.1,word) ∧
      (if out.face.val.2 then (coarse).graph.dst out.face.val.1 else (coarse).graph.src out.face.val.1)=(hop).symm y.1 :=by
  obtain ⟨v,j,t,target,pin,lane,within,nodeAt,socket,onGate,entry,mouth⟩:=external
  let req : Mouth B.reset.n := ⟨pin,target,t.1.val,t.2.1.val,t.2.2.val,within.val⟩
  let serial := (ordAt actor z₀).val
  have actualLayers:=sized_layer_count R_ B.reset.graph B.reset.positive B.reset.pay B.reset.circuit unit p splitEq side root
  have decoded : (cfg).rotor.publicTap B.reset.graph C layers_ p serial arg actor=some req :=
    (congrArg ((cfg).rotor.publicTap B.reset.graph C layers_ p serial arg)
      ((sizedSite).symm_apply_apply actor).symm).trans mouth
  have control := (cfg).rotor.public_selector_at B.reset.graph C p serial arg ((cfg).reg x) side
    (B.reset.goodLabel B.terminals root) actor shape req depth safe ranked located
    ((congrArg (fun count => (cfg).rotor.publicTap B.reset.graph C count p serial arg actor)
      (rows.layers.trans actualLayers)).trans decoded)
  let family := fun b : (trueDevice).Site => (physicalProgram b).Node
  have pair := originalArgumentPair sizedSite family actor z₀ ⟨v,.inr j⟩ (.inr t) nodeAt
  let mounted : (Σa,(progAt a).Node) → NodeOrder.Global (B.reset.laneRecipe birth unit p hp splitEq) :=
    fun q => ⟨mountedSite q.1,mountedNode q.1 q.2⟩
  have originAt := origin.trans (congrArg (fun q => Sum.inr (Sum.inr (mounted q))) pair)
  obtain ⟨firstItem,selected,covered⟩:=mounted_live_tap R_ B.reset.graph B.reset.positive B.reset.pay B.reset.circuit
    birth d unit p hp splitEq side root v j target pin socket t lane within onGate
  have atOffset := (congrArg (fun k => (cfg).rotor.public_selector B.reset.graph C p serial k ((cfg).reg x))
    entry.symm).trans control
  obtain ⟨host,number,output,value,key,ending⟩:=good_tap_socket_key
    (field:=field) (query:=query) (lanes:=lanes) (nodes:=nodes) (args:=args) (grain:=p)
    B hp one pos whole wide a sh side root v j pin target socket t y originAt within.val
    firstItem selected covered x rows serial active atOffset
  exact ⟨host,number,_,_,pin,output,(congrArg (fun k => (cfg).mixed B.reset.graph serial k x) entry).trans value,
    (congrArg (keyCable installed (middle_ y)) entry).trans key,ending⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
