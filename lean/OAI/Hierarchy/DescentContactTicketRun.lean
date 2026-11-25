import OAI.Hierarchy.DescentContactSenderTicket
import OAI.Hierarchy.DescentSenderRootStencil

namespace OAI
/-! # Single-pass issue of the public contact's true portable sender ticket -/
namespace Hierarchy.DescentContactTicketRun
open DescentResetLocalRoster DescentSIMDLookup DescentPackedZip DescentPackedFallbackTree.Image DescentIssuedGoodHeaders
open DescentPacking.PackedMatch.Local.Gather DescentSharedCableNames DescentSenderRootStencil
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {H G M w field : ℕ}

def inputs (x : Fin 5→Cell field) : Fin 3→Cell field := ![x 0,x 1,x 2]

def payload (Ht r Y : ℕ) (x : Fin 5→Cell field) :=
  DescentContactSenderTicket.join Ht r Y (DescentSenderRootStencil.owner r Y (inputs x)).val (x 3).val (x 4).val

theorem vacant (Ht r Y : ℕ) (x : Fin 5→Cell field) (empty : (x 0).val=0) : payload Ht r Y x=0 := by
  simp [payload,DescentSenderRootStencil.owner,inputs,empty,DescentContactSenderTicket.join]

theorem signed_present {D cap : ℕ} (z : DescentSharedCableNames.Stage.Live D cap) :
    (DescentSignedCableCodec.encode (some z)).val≠0 := by
  intro zero
  have eqn : DescentSignedCableCodec.encode (some z)=DescentSignedCableCodec.encode none :=
    (Fin.ext zero).trans DescentSignedCableCodec.empty.symm
  have same:=congrArg (DescentSignedCableCodec.decode D cap) eqn
  simp at same

theorem issue (Ht r Y : ℕ)
    (tables : Fin 5→Tables) (reads : Fin 5→Expr) (menu : DescentSIMDLookup.Banks) (mid : ℕ) (out : Bank)
    (x : Fin H→Fin G→Fin 5→Cell field) (pos : 0<M)
    (mem : Memory w) (bounds : Bounds (w:=w) (d:=field) (M:=M) tables reads mid)
    (constants : ∀j,Static (tables j) (setField (d:=field) j) M mem)
    (source : ∀j,Source (reads j) (fun a g=>x a g j) M mem) (room : mid+H*chunks G M<2^w)
    (fit : DescentSIMDLookup.Fits menu (field*5) (Packed.bits (DescentIssuedContactShape.bound Ht r Y)) M H G w out.base)
    (rom : resident (payload Ht r Y ∘ (encode field 5).symm) menu H G M mem)
    (dictLow : menu.dictionary.base+2^((field*5)*M)≤ mid) (maskLow : menu.mask.base+H*chunks G M≤ mid)
    (wire : menu.source.base=mid) (ceiling : ℕ) (outputOK : out.Fits w ceiling) (outputRoom : H*chunks G M≤out.size) :
    let act:=assembly tables reads
    let rows:=H*chunks G M
    let dst:=imageBank H G M out.base menu (image mid rows act mem)
    ((scan w mid rows act).seq (DescentSIMDLookup.program menu out.base H G M w)).Exec mem dst
      ((4+rows*(2*act.work+4))+(4+44*rows)) ∧
    Source (.lookup out .row) (fun a g=>payload Ht r Y (x a g)) M dst ∧
    ∀addr,(addr< mid ∨ mid+rows≤addr)→(addr<out.base ∨ out.base+rows≤addr)→dst addr=mem addr := by
  obtain ⟨run,whole,_,frame⟩:=gathered_words (payload Ht r Y) tables reads menu mid out.base
    x pos mem bounds constants source room fit rom dictLow maskLow wire
  exact ⟨run,source_column out ceiling outputOK _ _ outputRoom whole,frame⟩

end
end Hierarchy.DescentContactTicketRun

namespace Hierarchy.DescentSixParty.GroupStage
open DescentCompiler DescentIssuedFallbackPanel DescentGroupPeerOrder DescentSharedCableNames.Stage DescentGL DescentColonies
open DescentChosenRouter DescentResetAttachments DescentRelativeContacts DescentFallbackShapeTable DescentCanonicalPorts
open DescentRotorWindowScore DescentPackedTicketChronology DescentSIMDLookup DescentPacking
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃J×Block k)
local notation "Wold" => W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)) (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frm : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u : W.graph.Site =>(A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
local notation "c" => T.commonDepth
local notation "r" => (Z.k-c)
local notation "Y" => (2^Z.n:ℕ)
local notation "R" => Z.placement
local notation "E" => Grain A
local notation "endAt" => DescentIssuedFallbackPanel.endSite (W:=W) A
local notation "use" => useRotor (R).b (R).depth (R).L (R).keys (R).hub (R).old
local notation "headAt" => base (R).b (R).depth (R).L (R).keys (R).hub (R).old
local notation "wireWord" => peerShapeWord A S ready digits Z T frm


open DescentSenderRootStencil
local notation "wireAt" => fun s e=>wireWord s (home A (endAt s e))
local notation "expt" => exceptionalCell A S ready digits Z T frm

open DescentContactTicketRun DescentContactSenderTicket
theorem paid_sender_payload {field : ℕ} (s : Bool) (p : {e : E // use e}) (x : Fin 5→Cell field)
    (live : (x 0).val≠0) (atOwn : (x 1).val=wireAt s p.val) (atPeer : (x 2).val=wireAt (!s) p.val)
    (observed : (x 3).val=(R).reservedColumn c T.columns.host T.columns.near T.columns.size s ((R).ticket p)) :
    (DescentContactTicketRun.payload Ht r Y x).val=
      (DescentResetLocalRoster.rootId r Y (.inl (Z.goodLabel T (headAt p s)))).val*(Y+2^Ht)+
        Z.contactSlotWord T s (.inl ((R).ticket p))+1 := by
  have own:=paid_stencil_root A S ready digits Z T frm s p (inputs x) live atOwn atPeer
  have atRow:=observed.trans (T.columns.read s ((R).ticket p)).symm
  rw [DescentContactTicketRun.payload,own,atRow]
  apply join_good

theorem fallback_sender_payload {field : ℕ} (s : Bool) (e : E) (t : Z.Fallback)
    (miss : ¬use e) (here : falls A S ready Z s t e) (x : Fin 5→Cell field)
    (live : (x 0).val≠0) (atOwn : (x 1).val=wireAt s e) (atPeer : (x 2).val=wireAt (!s) e)
    (arrived : (x 3).val=DescentTreePrefixIntervals.start Ht
      (((R).fallbackBook s t).codes ⟨(R).contact e,here⟩)) (height : (x 4).val=((R).fallbackBook s t).height) :
    (DescentContactTicketRun.payload Ht r Y x).val=
      (DescentResetLocalRoster.rootId r Y (Z.rootTicket T (.inr t))).val*(Y+2^Ht)+
        (Y+(DescentResetCableSlots.leaf (R) Ht T.bookHeight s t ⟨(R).contact e,here⟩).val)+1 := by
  have own:=fallback_stencil_root A S ready digits Z T frm s e t miss here (inputs x) live atOwn atPeer
  rw [DescentContactTicketRun.payload,own,arrived,height]
  exact join_fallback Ht r Y (Z.fallLabel T t,(T.code t).2.2) _ _ (T.bookHeight s t)

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
