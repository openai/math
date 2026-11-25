import OAI.Hierarchy.DescentResetEmittedFirstCable
import OAI.Hierarchy.DescentResetRegisteredFacePointer

namespace OAI
/-! A selected socket's physical header equals the archived pointer at its original flat recipe index. -/
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

theorem argument_at_socket (rank : Local next_) (pin : P→ℕ) (args : ℕ) (x : NodeOrder.All next_) (j : ℕ)
    (host : Host) (face : Roster.Face A₁ ord₁ (blocks B) host) (word : ℕ)
    (source : Incident (coarse).graph ((hop).symm x.1))
    (edgeAt : face.val.1=source.val) (fits : (word+1)*p≤(coarse).graph.width source.val)
    (inside : word/unit<(blocks B).count face.val.1)
    (read : ((present x).keys x.2)[j]?=some (.inl ⟨.inl source,word,fits⟩))
    (endAt : (if face.val.2 then (coarse).graph.dst source.val else (coarse).graph.src source.val)=(hop).symm x.1) :
    let u:=referencedUnit B host face unit word inside
    let child:=Stage.live A₁ ord₁ S B.next.valid (fieldNames B) host (GrainPorts.port A₁ ord₁ (blocks B) host u)
    Pointer.cable child.neighbor.val (child.wire.val-child.within.val)
      (if face.val.1∈(coarse).core then word%unit else word) = result rank pin args x j:=by
  have enough : (word+1)*p≤(coarse).graph.width face.val.1:=edgeAt.symm ▸ fits
  have home : (if face.val.2 then (coarse).graph.dst face.val.1 else (coarse).graph.src face.val.1)=(hop).symm x.1:=by
    simpa only [edgeAt] using endAt
  have same : faceCable B x.1 host face home=source:=Subtype.ext edgeAt
  have entry : ((present x).keys x.2)[j]?=some (.inl ⟨.inl (faceCable B x.1 host face home),word,enough⟩) :=by
    simpa only [same] using read
  exact (registered_face_pointer B hp one pos whole wide a sh rank pin args x j host face word enough inside home entry).symm

/-- A decoder may report either marker on a single unsplit subword. -/
theorem argument_at_tagged_socket (rank : Local next_) (pin : P→ℕ) (args : ℕ) (x : NodeOrder.All next_) (j : ℕ)
    (host : Host) (face : Roster.Face A₁ ord₁ (blocks B) host) (word : ℕ) (tag : Bool)
    (source : Incident (coarse).graph ((hop).symm x.1))
    (edgeAt : face.val.1=source.val) (fits : (word+1)*p≤(coarse).graph.width source.val)
    (inside : word/unit<(blocks B).count face.val.1)
    (read : ((present x).keys x.2)[j]?=some (.inl ⟨.inl source,word,fits⟩))
    (endAt : (if face.val.2 then (coarse).graph.dst source.val else (coarse).graph.src source.val)=(hop).symm x.1)
    (marker : decide (face.val.1∈(coarse).core)=tag ∨ word<unit) :
    let u:=referencedUnit B host face unit word inside
    let child:=Stage.live A₁ ord₁ S B.next.valid (fieldNames B) host (GrainPorts.port A₁ ord₁ (blocks B) host u)
    Pointer.cable child.neighbor.val (child.wire.val-child.within.val)
      (if tag then word%unit else word) = result rank pin args x j:=by
  have actual:=argument_at_socket B hp one pos whole wide a sh rank pin args x j host face word source
    edgeAt fits inside read endAt
  dsimp only at actual ⊢
  rcases marker with cert|small
  · subst tag
    simpa using actual
  · rw [Nat.mod_eq_of_lt small] at actual ⊢
    simpa using actual

open DescentSIMDLookup DescentOperandCandidateLookup DescentDatedAddressBook.ResetOutput DescentResetOperandComponents
local notation:max "pubCfg" b:arg q:arg l:arg bat:arg nd:arg ar:arg gr:arg => publicOperandConfig B b q l bat unit nd ar gr
/-- The public lookup and the selected original signed candidate at an occupied
argument give the exact four fields of its archived pointer. -/
theorem PublicSocket.header {b query lanes batches nodes «arguments» grain size H₀ G₀ candidates coeff signed : ℕ}
    {host : Host} {word number : ℕ} {tag : Bool} (socket : PublicSocket B host unit word tag number)
    (arg : Fin «arguments») (node : Fin nodes) (row : (pubCfg b query lanes batches nodes «arguments» grain).Data B.reset.n)
    (width : max ((A₁).degree+1) ((A₁).cap+1)≤2^signed) (card : candidates=totalLocal B)
    (room : 2*candidates<2^query) (location : Fin H₀→Fin G₀→Option Host)
    (q₀ : Fin H₀→Fin G₀→Option (Fin (2*candidates))) (rh : Fin H₀) (rg : Fin G₀)
    (siteAt : location rh rg=some host) (rank : Local next_) (pin : P→ℕ) (arity : ℕ)
    (y : NodeOrder.All next_) (j : ℕ) (source : Incident (coarse).graph ((hop).symm y.1))
    (faceAt : socket.face.val.1=source.val) (fits : (word+1)*p≤(coarse).graph.width source.val)
    (read : ((present y).keys y.2)[j]?=some (.inl ⟨.inl source,word,fits⟩))
    (endAt : (if socket.face.val.2 then (coarse).graph.dst source.val else (coarse).graph.src source.val)=(hop).symm y.1)
    (f₀ : Fin 4) :
    let cfg:=pubCfg b query lanes batches nodes «arguments» grain
    let at_:=finProdFinEquiv (arg,node)
    let f₁:=f₀.castLE (by decide : 4≤7)
    code room (q₀ rh rg)=cfg.column B.reset.graph query none at_ row →
    cfg.column B.reset.graph query none at_ row=(number:ℕ) →
    cfg.column B.reset.graph coeff (some f₁) at_ row=((produced tag unit word ⟨0,1,size⟩ f₁:ℕ):Cell coeff) →
    (result rank pin arity y j).header f₀<2^coeff →
    (cfg.column B.reset.graph coeff (some f₁) at_ row).val+
      (selected q₀ (fun col h v=>nativeCandidateField signed coeff f₁ ((location h v).bind (fun peer=>
        candidateRows B (fieldNames B) peer (col.cast (congrArg (2*·) card))))) rh rg).val=
      (result rank pin arity y j).header f₀ :=by
  intro cfg at_ f₁ issued key value small
  have original:=argument_at_tagged_socket B hp one pos whole wide a sh rank pin arity y j host socket.face word tag
    source faceAt fits socket.inside read endAt socket.mark
  have endpoint:=PublicSocket.observed B socket (fieldNames B) arg node row size f₁ width card room location q₀ rh rg siteAt issued key value
  dsimp only at original endpoint
  rw [original] at endpoint
  have headerEq : (result rank pin arity y j).fields ⟨0,1,size⟩ f₁ = (result rank pin arity y j).header f₀ := by
    simp only [Pointer.fields,f₁,Fin.val_castLE,dite_eq_left f₀.isLt]
  exact (endpoint (lt_of_eq_of_lt headerEq small)).trans headerEq

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
