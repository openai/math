import OAI.Hierarchy.TaggedWirePacketInstall
import OAI.Hierarchy.TaggedWirePacketPost
import OAI.Hierarchy.TaggedWirePacketSiteFields

namespace OAI
/-! # The literal hidden-state factor using the local public header and both private packet banks -/

noncomputable section
open scoped Fin.CommRing
set_option quotPrecheck false
namespace Hierarchy.WireTelescope.ChosenPackets.RowRouting
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open ThreeFlat Diagonal.MotifOuterTerms Routing Tagged AdaptiveProbe TurnShelf CalendarTape
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical

variable {F V : Type} [Field F] [Fintype V] {S N H copies count p e W : ℕ}
    {row : Row F S H copies} {phys : Fin N→Chord S}

/-- A view of numerical row/slot/field coordinates. No separate global
table is generated for an individual packet: every accessed cell in this
view comes from the one batched, site-local CPU output. -/
def headerView {slots : ℕ} (cell : Fin 5→Fin S×Fin slots→Word W) : Memory W := fun k=>
  if h:k<5*(S*slots) then
    let q : Fin 5×Fin (S*slots):=finProdFinEquiv.symm ⟨k,h⟩
    cell q.1 (finProdFinEquiv.symm q.2)
  else 0

theorem header_at {slots : ℕ} (cell : Fin 5→Fin S×Fin slots→Word W)
    (s : Fin S) (t : Fin slots) (f : Fin 5) : headerView cell (addr 0 s t f)=cell f (s,t) := by
  let i:=ProtocolRAMTurnShelf.index f (s,t)
  have eq : addr 0 s t f=i.val := by simp [i,addr,ProtocolRAMTurnShelf.index_val]
  rw [eq]
  unfold headerView
  rw [dite_eq_left i.isLt]
  change cell (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm (finProdFinEquiv.symm i).2)=_
  simp only [i,ProtocolRAMTurnShelf.index,Equiv.symm_apply_apply]

variable (R : RowRouting row phys) (c : Histogram (Fin H) copies) (s : Fin S)
local notation "roles" => Fintype.card R.Roles
local notation "old" => Installs.starts (source:=R.source) R.order
local notation "run" => R.install.steps R.order
local notation "w" => Installs.numbered R.order (R.bits c)
local notation "mass" => routeLoad run w
local notation "ids" => NativeSlot.edge run R.ordinal
local notation "before" => fun (i : Fin roles) (b : Bool)=>(halfCode i b).val
local notation "after" => PostCode.after ids roles

theorem canonical_install (short : ∀i,(run i).length≤2) (turns : Fin count≃Positions run)
    (ctl : Fin (roles*3)×Control p e→V) (post : Aperture p e→V) (v : V→Bool)
    (out : State (R.post c) s) (room : roles*2+(R.occurrences+1)*2≤2^p)
    (oldFit : ∀i,w i≤2^e) (newFit : ∀i,mass i≤2^e)
    (control : let cols:=PacketTurns.fields old phys run w R.ordinal before after short turns
      let pu:=PacketTurns.put old phys run w R.ordinal before after short turns
      ∀t f,v (ctl (t,f))=(ProtocolRAMTurnShelf.entry (W:=W) cols pu (projection f).1 (s,t)).val.testBit (projection f).2)
    (state : ∀a,v (post (postPlace R c s room newFit a))=siteBits (R.post c) s out a)
    (fit : let cols:=PacketTurns.fields old phys run w R.ordinal before after short turns
      ∀u : ProtocolRAMTurnShelf.Live cols,∀f : Fin 5,cols u.val (f.castLE (by decide))<2^W) :
    ∀y,TypedWiring.value (installNet F ctl (packetData roles (2^e) post))
        (Sum.elim v (packedMiddle c s (middlePlace R c s (2^e) oldFit) y))=
      Installs.transport (R.shape c) rfl (R.install.operator R.order (R.bits c) R.ordinal) s y out := by
  let cols:=PacketTurns.fields old phys run w R.ordinal before after short turns
  let pu:=PacketTurns.put old phys run w R.ordinal before after short turns
  let cell:=ProtocolRAMTurnShelf.entry (W:=W) cols pu
  exact installed_eval R c s short turns before after ctl (packetData roles (2^e) post)
    (middlePlace R c s _ oldFit) (fun a=>post (postPlace R c s room newFit a)) v out 0 (headerView cell)
    (fun t f=>by rw [header_at];exact control t f) state (fun f a=>header_at cell _ _ _) fit
    (fun i b=>(halfCode i b).isLt.trans_le ((Nat.le_add_right _ _).trans room))
    (fun i b=>(PostCode.after_lt ids roles i b).trans_le room) oldFit newFit
    (packetData_old R c s _ oldFit post) (packetData_paid R c s post _ room newFit)

/-- Pad the physical outgoing party state using the first occurrence of each
true paid row. The public circuit never receives a global paid-row word. -/
def postBits (room : roles*2+(R.occurrences+1)*2≤2^p) (fits : ∀i,mass i≤2^e)
    (out : State (R.post c) s) : Aperture p e→Bool :=
  Function.extend (postPlace R c s room fits) (siteBits (R.post c) s out) (fun _=>false)

@[simp] theorem postBits_read (room : roles*2+(R.occurrences+1)*2≤2^p) (fits : ∀i,mass i≤2^e)
    (out : State (R.post c) s) (i : SiteBit (R.post c) s) :
    postBits R c s room fits out (postPlace R c s room fits i)=siteBits (R.post c) s out i :=
  (postPlace R c s room fits).injective.extend_apply ..

/-- The selector's emitted field at each public party is evaluated on its real
candidate row. The only private values are the two physical party states. -/
theorem candidate_install {L : ℕ} (short : ∀i,(run i).length≤2) (turns : Fin count≃Positions run)
    (ctl : Fin (roles*3)×Control p e→V) (post : Aperture p e→V) (v : V→Bool) (out : State (R.post c) s)
    (room : roles*2+(R.occurrences+1)*2≤2^p) (oldFit : ∀i,w i≤2^e) (newFit : ∀i,mass i≤2^e)
    (o : PacketTurns.Operands fun i=>(run i).length) (mem : Memory W) (rowArg : Word W)
    (party : Fin L→Expr) (partyId : Fin L) (located : (party partyId).eval mem rowArg=(s.val : Word W))
    (read : PacketTurns.Reads old phys run w o mem rowArg) (sites : S≤2^W) (links : N≤2^W)
    (live : ∀i,w i<2^W)
    (cpu : ∀t f,v (ctl (t,f))=
      (((o.siteFields R.ordinal party partyId (finProdFinEquiv (t,(projection f).1))).eval mem rowArg).val.testBit
        (projection f).2))
    (external : ∀a,v (post a)=postBits R c s room newFit out a)
    (fit : let cols:=PacketTurns.fields old phys run w R.ordinal before after short turns
      ∀u : ProtocolRAMTurnShelf.Live cols,∀f : Fin 5,cols u.val (f.castLE (by decide))<2^W) :
    ∀y,TypedWiring.value (installNet F ctl (packetData roles (2^e) post))
        (Sum.elim v (packedMiddle c s (middlePlace R c s (2^e) oldFit) y))=
      Installs.transport (R.shape c) rfl (R.install.operator R.order (R.bits c) R.ordinal) s y out := by
  apply canonical_install R c s short turns ctl post v out room oldFit newFit
  · dsimp only
    intro t f
    rw [cpu]
    exact congrArg (fun z : Word W=>z.val.testBit (projection f).2)
      (PacketTurns.field_eval old phys run w R.ordinal short turns o mem rowArg (party partyId) s located
        read sites links live t (projection f).1)
  · intro a
    rw [external,postBits_read]
  · exact fit

end Hierarchy.WireTelescope.ChosenPackets.RowRouting

end
end OAI
