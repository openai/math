import OAI.Hierarchy.DescentResetArgumentAtSocket
import OAI.Hierarchy.DescentClosedResetSlotCount
import OAI.Hierarchy.DescentCalendarRelaySockets

namespace OAI
/-! # Reading a published socket from the original installed recipe key -/
namespace Hierarchy.DescentResetFreshWires
open DescentSixParty DescentKernelHistory DescentBundleHistory DescentOrderedWords
open Computability.BorderVNP.Crossing
noncomputable section
set_option quotPrecheck false
open scoped Fin.CommRing
variable {F P : Type} [Field F] {n p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F n P bits} {B : BitDescription W}

theorem keyCable_fit (shape : WorldShape p R B) (x : NodeOrder.All B) (j : ℕ)
    {e : W.graph.Edge} {word : ℕ} (issued : keyCable shape x j=some (e,word)) :
    (word+1)*p≤W.graph.width e :=by
  unfold keyCable at issued
  cases seen : ((shape.sites x.1).keys x.2)[j]? with
  | none=>simp [seen] at issued
  | some a=>
    rw [seen] at issued
    rcases a with ⟨a|pin,v,room⟩|priv
    · change some (a.val,v)=some (e,word) at issued
      obtain ⟨rfl,rfl⟩:=Prod.mk.inj (Option.some.inj issued)
      exact room
    · cases issued
    · cases issued
end
end Hierarchy.DescentResetFreshWires

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentKernelHistory DescentBundleHistory DescentLocalArchiveOrder DescentCompiler DescentColonies
open DescentResetTrunks DescentRotor DescentResetGates DescentChosenRouter DescentRouterBank
open DescentResetAttachments DescentNamedContact DescentPrimitivePalette Chronology Computability.BorderVNP.Crossing
open DescentStageEdgeReceipt ThreeFlat.Routing
open scoped Classical
noncomputable section
set_option quotPrecheck false
open scoped Fin.CommRing
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
local notation "after_" => WorldShape.follow hp pos whole B.reblock B.cuts installed
local notation "next_" => (resetArchive B p hp whole a).bit
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "world" => B.reset.orderedOrdinary B.terminals birth
local notation "cnt" => fun e=>(coarse).graph.width e/B.reset.unit
local notation "geo" => B.reset.counts_fit B.terminals
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans cap.vertex
local notation "dense" => (B.reset.rawHostRank B.terminals vertexCode).trans Fin.valEmbedding
local notation "tape" => B.reset.nativeResetEdges B.terminals vertexCode birth
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=S.groupCount (i+1))) dense) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "sparse" => DescentResetLocalOrder.allCode B.raw ((tape).order.trans Fin.valEmbedding) S B.valid rawSite
local notation "edgeName" => DescentPhysicalOrder.rename sparse

open DescentSharedCableNames DescentParallelBase DescentNextSignedWindow DescentOperandStateBanks
local notation "A₁" => B.next.placement
local notation "ord₁" => B.next.order.trans Fin.valEmbedding
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation:max "present" x:arg => (installed).sites ((hop).symm x.1)
local notation:max "result" rank:arg pin:arg args:arg x:arg j:arg => Reached.argumentPointer B.next next_ rank after_ hp pin args x j

local notation "before_" => BitDescription.granular W B.count (z*G.b) B.fit a.bit
local notation "pre_" => (before_).batchedReset B.reset B.terminals birth unit p hp splitEq (resetMenu B)
local notation:max "middle_" x:arg => NodeOrder.followNames B.reblock pre_ x
open DescentSIMDLookup DescentOperandCandidateLookup DescentDatedAddressBook.ResetOutput DescentResetOperandComponents
local notation:max "pubCfg" b:arg q:arg l:arg bat:arg nd:arg ar:arg gr:arg => publicOperandConfig B b q l bat unit nd ar gr
theorem PublicSocket.keyed_header {b query lanes batches nodes «arguments» grain size H₀ G₀ candidates coeff signed : ℕ}
    {host : Host} {word number : ℕ} {tag : Bool} (socket : PublicSocket B host unit word tag number)
    (arg : Fin «arguments») (node : Fin nodes) (row : (pubCfg b query lanes batches nodes «arguments» grain).Data B.reset.n)
    (width : max ((A₁).degree+1) ((A₁).cap+1)≤2^signed) (card : candidates=totalLocal B)
    (room : 2*candidates<2^query) (location : Fin H₀→Fin G₀→Option Host)
    (q₀ : Fin H₀→Fin G₀→Option (Fin (2*candidates))) (rh : Fin H₀) (rg : Fin G₀)
    (siteAt : location rh rg=some host) (rank : Local next_) (pin : P→ℕ) (arity : ℕ)
    (y : NodeOrder.All next_) (j : ℕ)
    (read : DescentResetFreshWires.keyCable installed (middle_ y) j=some (socket.face.val.1,word))
    (endAt : (if socket.face.val.2 then (coarse).graph.dst socket.face.val.1 else (coarse).graph.src socket.face.val.1)=(hop).symm y.1)
    (f₀ : Fin 4) :
    let cfg:=pubCfg b query lanes batches nodes «arguments» grain
    let at_:=finProdFinEquiv (arg,node)
    let f₁:=f₀.castLE (by decide : 4≤7)
    code room (q₀ rh rg)=cfg.column B.reset.graph query none at_ row →
    cfg.mixed B.reset.graph node.val arg.val row=some (number,word,size,tag) →
    (result rank pin arity y j).header f₀<2^coeff →
    (cfg.column B.reset.graph coeff (some f₁) at_ row).val+
      (selected q₀ (fun col h v=>nativeCandidateField signed coeff f₁ ((location h v).bind (fun peer=>
        candidateRows B (fieldNames B) peer (col.cast (congrArg (2*·) card))))) rh rg).val=
      (result rank pin arity y j).header f₀ :=by
  intro cfg at_ f₁ issued mixed small
  let source:=faceCable B y.1 host socket.face endAt
  have fits:=(DescentResetFreshWires.keyCable_fit installed (middle_ y) j read)
  have key:=DescentResetFreshWires.keyCable_read installed (middle_ y) j source word fits read
  have atNumber : cfg.column B.reset.graph query none at_ row=(number:ℕ) :=by
    have columnQuery (conf : DescentResetPublicOperandBook.Config) (arg' : Fin conf.args)
        (node' : Fin conf.nodes) (row' : conf.Data B.reset.n)
        (hit : conf.mixed B.reset.graph node'.val arg'.val row'=some (number,word,size,tag)) :
        conf.column B.reset.graph query none (finProdFinEquiv (arg',node')) row'=(number:ℕ) := by
      simp only [DescentResetPublicOperandBook.Config.column,Equiv.symm_apply_apply,hit]
    exact columnQuery cfg arg node row mixed
  have atWord:=public_produced B.reset.graph cfg arg node row number word size coeff tag mixed f₁
  exact PublicSocket.header B hp one pos whole wide a sh socket arg node row width card room location q₀ rh rg siteAt
    rank pin arity y j source rfl fits key endAt f₀ issued atNumber atWord small

open DescentResetFreshWires
local notation "old_" => W.granular B.count (z*G.b) B.fit
local notation:max "land_" e:arg => B.terminals.home ((old_).graph.dst e)
local notation:max "relayEdge" e:arg a:arg => if a<unit then trunkParent B (land_ e) else stemParent B (true,e)
local notation:max "relayWord" e:arg a:arg => if a<unit then earlierIncoming B e*unit+a else a-unit

/-- The earlier two-dimensional address equals the argument number on the final
shape. The edge changes exactly once, at the start of the second full word. -/
theorem relay_flat_key (y : NodeOrder.All next_) (e : (old_).graph.Edge)
    (birthAt : resetOrigin B hp whole a y=.inr (.inl e)) (slot : Fin (2*unit)) :
    keyCable installed (middle_ y) slot.val=some (relayEdge e slot.val,relayWord e slot.val) :=by
  obtain ⟨⟨face,j⟩,rfl⟩:=finProdFinEquiv.surjective slot
  have raw:=relay_installed_word B hp one pos whole wide a sh y e birthAt face j
  dsimp only at raw
  fin_cases face
  · simpa [finProdFinEquiv_apply_val,j.isLt] using raw
  · have later : ¬j.val+unit<unit:=by omega
    have later' : ¬unit+j.val<unit:=by omega
    simpa [finProdFinEquiv_apply_val,j.isLt,later,later',Nat.add_comm] using raw


end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
