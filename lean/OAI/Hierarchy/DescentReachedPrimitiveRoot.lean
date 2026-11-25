import OAI.Hierarchy.DescentPhysicalBankPrimitive
import OAI.Hierarchy.DescentPrimitiveRootRotation
import OAI.Hierarchy.DescentRecordedPublicBoard
import OAI.Hierarchy.DescentReachedOriginalNumericFields

namespace OAI
/-! # The selected primitive root at its occupied actor and original block -/
namespace Hierarchy.DescentPrimitivePalette
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentLocalArchiveOrder DescentCompiler DescentRotor
open DescentResetLocalNodes DescentNamedContact
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist p : ℕ}
  {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (b : ClosedReset cap ctl) (hp : 0<p) (whole : p∣b.reset.unit) (a : Archive W) (earlier : Local a.bit)
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
local notation:max "census" precision:arg => Census.count (Y).placement (Equiv.refl _) prevRank precision
local notation "cell" => whereAt Y next order
local notation "res" => b.reset.k-b.terminals.commonDepth
local notation:max "cls" rack:arg => (ClosedReset.Window.paidActorAt b rack).elim 0 (fun u=>indexed b.reset.graph res u.val)
local notation:max "leftSite" u:arg => b.reblock.destination ((b.reset.resetNames b.terminals).symm u)
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
local notation:max "rootLow" g:arg => ((Z).goodLabel T g).val.2
local notation:max "rootNode" side:arg g:arg v:arg op:arg => (⟨rootSite side g v,op⟩:NodeOrder.Global prog)

theorem physical_root_parts (side : Bool) (g : (rr).Good) (v : Fin (2^(Z).n))
    (op : (prog (rootSite side g v)).Node) (row : Fin (2*(2^res*2^(Z).n)))
    (issued : (originClass b hp whole a (.inr (.inr (rootNode side g v op)))).val=6+row.val) :
    rootParts res (Z).n row=(side,⟨rootLow g,(Nat.mod_lt _ (Nat.two_pow_pos _)).trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right ((rr).depth _) dim))⟩,v):=by
  let label:=(Z).goodLabel T g
  have low : label.val.2<2^res:=(Nat.mod_lt _ (Nat.two_pow_pos _)).trans_le
    (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right ((rr).depth _) dim))
  let x : Fin (2^res):=⟨label.val.2,low⟩
  let ordinal:=finProdFinEquiv (finTwoEquiv.symm side,finProdFinEquiv (x,v))
  have same : row=ordinal:=by
    apply Fin.ext
    change (DescentResetActorClass.rootIndex (Z).n res side label.val.2 v).val=6+row.val at issued
    simp only [DescentResetActorClass.rootIndex,Nat.mod_eq_of_lt low] at issued
    exact (Nat.add_left_cancel issued).symm
  rw [same]
  simp [rootParts,ordinal,x,label]

theorem physical_root_home (side : Bool) (g : (rr).Good) (v : Fin (2^(Z).n))
    (op : (prog (rootSite side g v)).Node) (atom : NodeOrder.All next)
    (origin : names atom=.inr (.inr (rootNode side g v op))) :
    DescentSharedCableNames.Stage.home (Y).placement atom.1=
      (((oldDigits ((Z).rootBlock T (.inl g))).1,
        (Z).placed T (((Z).resetNames T).symm (.inr (rootSite side g v)))),
       (oldDigits ((Z).rootBlock T (.inl g))).2):=by
  have where_:=reached_node_site b hp whole a atom
  rw [origin] at where_
  rw [←where_]
  let site := ((Z).resetNames T).symm (.inr (rootSite side g v))
  have coordinate : (Z).blockId T site=(Z).rootBlock T (.inl g):=by
    apply Fin.ext
    change DescentCommonHost.rawCoordinate (Z).placement (Z).graph dim (T).code (Z).positive (Z).pay (Z).circuit d
      (((Z).resetNames T) (((Z).resetNames T).symm (.inr (rootSite side g v)))) = _
    rw [Equiv.apply_symm_apply]
    rfl
  have home:=ClosedReset.Window.named_home b site
  rw [coordinate] at home
  exact home

open DescentDenseHostOrder DescentResetActorClass
local notation "former" => cap.vertex.trans (Fin.castLEEmb cap.valid.host)
local notation "ownerId" => b.frame.host.symm.toEmbedding.trans former
local notation "rawRoot" => ClosedReset.Window.originalCompactName b (S.hostSize i) cap.valid.host
local notation "address" => (Z).denseHostRank T ownerId
local notation:max "hostOf" v:arg => ((Y).placement.pos v).2
local notation:max "venue" side:arg g:arg v:arg => (Z).placed T (((Z).resetNames T).symm (.inr (rootSite side g v)))
local notation:max "high" g:arg => (Z).rootBlock T (.inl g)

/-- Both numerical coordinates address the unique predecessor owner and the selected high block. -/
theorem physical_root_coordinates {N : ℕ} (side : Bool) (g : (rr).Good) (v : Fin (2^(Z).n))
    (op : (prog (rootSite side g v)).Node) (atom : NodeOrder.All next)
    (slot : Fin N) (x : Block k) (h : Fin H) (group : Fin Groups)
    (found : cell x slot h group=some atom)
    (origin : names atom=.inr (.inr (rootNode side g v op))) :
    ∃member : h.val<Fintype.card (Y).V,
      (finProdFinEquiv.symm (rawRoot ⟨h.val,member⟩)).1=former (b.frame.host.symm g.val.1) ∧
        (finProdFinEquiv (group,x)).val=(high g).val:=by
  obtain ⟨u,act⟩:=atom
  have coor:=((whereAt_some Y next order x slot h group u act).mp found).1
  have home:=physical_root_home b hp whole a side g v op ⟨u,act⟩ origin
  have whereH : hostOf u=venue side g v:=congrArg (fun t=>t.1.2) home
  have rankH : (address (hostOf u)).val=h.val:=congrArg (fun t=>t.1.val) coor
  have valid : h.val<Fintype.card (Y).V:=rankH ▸ (address (hostOf u)).isLt
  refine ⟨valid,?_,?_⟩
  · have addressH : (⟨h.val,valid⟩:Fin (Fintype.card (Y).V))=address (hostOf u):=Fin.ext rankH.symm
    rw [addressH,ClosedReset.Window.originalCompactName_read,whereH]
    change (finProdFinEquiv.symm (finProdFinEquiv ((Z).hostFields T ownerId (venue side g v)))).1=_
    rw [Equiv.symm_apply_apply]
    let st : (Bool × (Z).Fallback) ⊕ (Z).bank.Site := .inr (rootSite side g v)
    have valAt : ((Z).placed T (((Z).resetNames T).symm st)).val =
        DescentCommonHost.rawName (Z).placement (Z).graph dim (T).code (Z).positive (Z).pay (Z).circuit d st :=
      congrArg (DescentCommonHost.rawName (Z).placement (Z).graph dim (T).code (Z).positive (Z).pay (Z).circuit d)
        (((Z).resetNames T).apply_symm_apply st)
    change ownerId (DescentDenseHostOrder.position (Z).graph ((Z).placed T (((Z).resetNames T).symm st)).val)=_
    rw [valAt]
    rfl
  · have groupAt : group=(oldDigits (high g)).1 :=
      (congrArg (fun t=>t.2.1) coor).symm.trans (congrArg (fun t=>t.1.1) home)
    have blockAt : x=(oldDigits (high g)).2 :=
      (congrArg (fun t=>t.2.2) coor).symm.trans (congrArg Prod.snd home)
    rw [groupAt,blockAt]
    change ((oldDigits).symm (oldDigits (high g))).val=(high g).val
    rw [Equiv.symm_apply_apply]

end
end Hierarchy.DescentPrimitivePalette

end OAI
