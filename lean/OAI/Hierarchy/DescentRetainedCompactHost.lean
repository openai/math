import OAI.Hierarchy.DescentPrimaryTokenCoordinates
import OAI.Hierarchy.DescentReachedOriginalNumericFields
import OAI.Hierarchy.DescentRetainedHomeMoverRead
import OAI.Hierarchy.DescentRetainedPhysicalTarget
import OAI.Hierarchy.DescentPhysicalBankPrimitive

namespace OAI
/-! # Predecessor coordinates on every primary row of the actual reset -/
namespace Hierarchy.DescentPrimitivePalette
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentLocalArchiveOrder DescentCompiler DescentRotor
open DescentResetLocalNodes DescentNamedContact
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist p : ℕ}
  {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (b : ClosedReset cap ctl) (hp : 0<p) (whole : p∣b.reset.unit) (a : Archive W) (earlier : Local a.bit)
set_option quotPrecheck false
local notation "split" => BitDescription.granular W b.count (z*G.b) b.fit a.bit
local notation "key" => DescentOrderedReset.grains W b.count b.order
local notation "fit" => (Nat.div_mul_cancel whole).symm
local notation "m" => b.reset.unit/p
local notation "pre" => (split).batchedReset b.reset b.terminals key m p hp fit (resetMenu b)
local notation "prog" => b.reset.laneRecipe key m p hp fit
local notation "next" => (resetArchive b p hp whole a).bit
local notation "names" => resetOrigin b hp whole a
local notation "oldId" => cap.placement.site cap.vertex cap.valid.coordinates
local notation "who" => (fun t=>(b.reset.homeTicket b.terminals oldId t).trans Fin.valEmbedding)
local notation "prior" => (fun v=>(earlier v).toEmbedding.trans Fin.valEmbedding)
local notation "fresh" => b.reset.laneNodeOrder key m p hp fit
local notation "order" => DescentLocalArchiveOrder.reset b p hp whole a earlier


open DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage DescentResetActorClass DescentCommonHost
open Reached.NodeCells DescentColonies
open scoped Classical Fin.CommRing
local notation "Y" => b.next
local notation "H" => S.hostSize (i+1)
local notation "Groups" => S.groupCount (i+1)
local notation "prevRank" => (Y).vertex.trans (Fin.castLEEmb (Y).valid.host)
local notation "census" precision => Census.count (Y).placement (Equiv.refl _) prevRank precision
local notation "cell" => whereAt Y next order
local notation "res" => b.reset.k-b.terminals.commonDepth
local notation "cls" rack => (ClosedReset.Window.paidActorAt b rack).elim 0 (fun u=>indexed b.reset.graph res u.val)
local notation "leftSite" u => b.reblock.destination ((b.reset.resetNames b.terminals).symm u)
local notation "original" => W.granular b.count (z*G.b) b.fit

open DescentPackedResetRotorRoles DescentResetMetadataInputs DescentBundleHistory
variable (layout : DescentPrimitiveBirth.Layout)
local notation:max "rootSite" wing:arg g:arg v:arg => (⟨(wing,.inl g),⟨v,.inl false⟩⟩:b.reset.bank.Site)

open DescentPrimitiveBirth DescentCommonHost DescentRotorRootPresence DescentSIMDLookup
open DescentPacking.PackedMatch.Local
local notation "Z" => b.reset
local notation "T" => b.terminals
local notation "rr" => (Z).placement
local notation "dim" => (T).commonDepth
local notation "oldDigits" => S.resetOutputDigits ctl.base ctl.radix b.age b.commonDepth
local notation "rootLow" g => ((Z).goodLabel T g).val.2
local notation:max "rootNode" side:arg g:arg v:arg op:arg => (⟨rootSite side g v,op⟩:NodeOrder.Global prog)

local notation:max "home" v:arg => (T).home v
local notation:max "rawHome" side:arg t:arg => ((Z).resetNames T).symm (.inl (side,t))
local notation:max "actor" t:arg => (Z).placed T (rawHome false t)
local notation:max "hostName" prev:arg => ((b.frame.host.symm.toEmbedding.trans cap.vertex).trans (Fin.castLEEmb prev))
local notation "ht" => GroupStage.depthBound D n f g

open DescentDenseHostOrder DescentDatedAddressBook.ActorSetup DescentRetainedHomeMover DescentRetainedTargetPlacement
variable (move:DescentRetainedHomeMover.Layout) (room:Fintype.card cap.V≤ move.transfer.hosts)
local notation "P₀" => move.placement
local notation "batch" => move.batch
local notation "pool" => (DescentDenseHostOrder.roster (Z).graph res ht).card
variable (sizes : (DescentDenseHostOrder.roster b.reset.graph (b.reset.k-b.terminals.commonDepth) (GroupStage.depthBound D n f g)).card=move.shapes)
local notation "used" => Fintype.card (Y).V
local notation:max "shape" act:arg => (((Z).hostFields T (hostName room) act).2.cast sizes)
local notation:max "carrier" act:arg => ((Z).hostFields T (hostName room) act).1
local notation "which" => fun t:Fin move.shapes=>targetBook ctl.board k ht (t.cast (sizes.symm.trans b.public_hub_slots))
local notation "rawName" => ClosedReset.Window.originalCompactName b move.transfer.hosts room
local notation "dir" => fun j:Fin used=>(rawName j).cast (congrArg (fun n=>move.transfer.hosts*n) sizes)
local notation:max "output" dat:arg => Chart.compact (P₀) batch (move.kept which) dir dat
variable (dat : Fin (move.batch.fields*move.shapes)→Fin move.transfer.hosts→Fin (move.groups*move.blocks)→Cell move.batch.bits)

private theorem cast_site {hosts oldTags newTags : ℕ} (size:oldTags=newTags) (old:Fin hosts) (tag:Fin oldTags) :
    (finProdFinEquiv (old,tag)).cast (congrArg (fun t=>hosts*t) size)=finProdFinEquiv (old,tag.cast size):=by
  subst newTags;rfl

theorem original_shape_host (act : (Y).V) :
    dir ((Y).vertex act)=finProdFinEquiv (carrier act,shape act):=by
  have actual:(Y).vertex act=(Z).denseHostRank T (hostName room) act:=
    Fin.ext (ClosedReset.Window.dense_physical b room act).symm
  have sparse := (congrArg (fun j : Fin used => rawName j) actual).trans
    (ClosedReset.Window.originalCompactName_read b move.transfer.hosts room act)
  exact (congrArg (fun row : Fin (move.transfer.hosts*pool) =>
    row.cast (congrArg (fun n=>move.transfer.hosts*n) sizes)) sparse).trans (cast_site sizes _ _)

theorem compact_unused (nx:Fin (batch).fields) (x:Fin move.blocks) (h:Fin move.newHosts) (g:Fin move.groups)
    (absent:used≤h.val) : output dat nx x h g=0:=by
  simp [Chart.compact,DescentResetDenseOperand.dense,Nat.not_lt.mpr absent]

theorem compact_original (nx:Fin (batch).fields) (x:Fin move.blocks) (h:Fin move.newHosts) (g:Fin move.groups)
    (act:(Y).V) (host:h.val=((Y).vertex act).val) :
    output dat nx x h g=
      if (primaryTarget (Z).graph res act.val).isSome then
        dat (finProdFinEquiv (nx,shape act)) (carrier act) (finProdFinEquiv (g,x)) else 0:=by
  have live:=host.trans_lt ((Y).vertex act).isLt
  have at_: (⟨h.val,live⟩:Fin used)=(Y).vertex act:=Fin.ext host
  have atDir : dir (⟨h.val,live⟩ : Fin used)=finProdFinEquiv (carrier act,shape act):=
    (congrArg (fun j : Fin used => dir j) at_).trans (original_shape_host b move room sizes act)
  have unpacked := (congrArg finProdFinEquiv.symm atDir).trans (finProdFinEquiv.symm_apply_apply (carrier act,shape act))
  let valueAt := fun point : Fin move.transfer.hosts × Fin move.shapes =>
    if (which point.2).isSome then dat (finProdFinEquiv (nx,point.2)) point.1 (finProdFinEquiv (g,x)) else 0
  simp only [Chart.compact,DescentResetDenseOperand.dense,dite_eq_left live]
  exact (congrArg valueAt unpacked).trans (congrArg (fun target : Option ℕ => if target.isSome then
    dat (finProdFinEquiv (nx,shape act)) (carrier act) (finProdFinEquiv (g,x)) else 0)
    (ClosedReset.Window.calendar_primary_target b room act))

theorem compact_primary (nx:Fin (batch).fields) (x:Fin move.blocks) (h:Fin move.newHosts) (g:Fin move.groups)
    (former:NodeOrder.All a.bit) (atom:NodeOrder.All next) (origin:names atom=.inl former)
    (host:h.val=((Y).vertex ((Y).placement.pos atom.1).2).val) :
    let act:=((Y).placement.pos atom.1).2
    output dat nx x h g=dat (finProdFinEquiv (nx,shape act))
      ((cap.vertex ((cap.placement.pos former.1).2)).castLE room) (finProdFinEquiv (g,x)):=by
  intro act
  have source:=physical_primary_fields b hp whole a room former atom origin
  have chosen:=ClosedReset.Window.calendar_primary_target b room act
  rw [compact_original b move room sizes dat nx x h g act host,←chosen,source.2,source.1]
  rfl

theorem compact_newborn (nx:Fin (batch).fields) (x:Fin move.blocks) (h:Fin move.newHosts) (g:Fin move.groups)
    (atom:NodeOrder.All next) (origin:∃j,names atom=.inr j)
    (host:h.val=((Y).vertex ((Y).placement.pos atom.1).2).val) : output dat nx x h g=0:=by
  let act:=((Y).placement.pos atom.1).2
  obtain ⟨j,eqn⟩:=origin
  have source:=physical_target_origin b hp whole a room atom
  rw [eqn] at source
  have chosen:=ClosedReset.Window.calendar_primary_target b room act
  rw [compact_original b move room sizes dat nx x h g act host,←chosen,source]
  rfl

end
end Hierarchy.DescentPrimitivePalette

end OAI
