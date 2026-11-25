import OAI.Hierarchy.DescentReservedSocketPanel

namespace OAI
/-! # Bounded raw reset peer markers from both reached old signed tickets -/
namespace Hierarchy.DescentReservedPeerMarker
open DescentReservedSocketPanel DescentResetPublicParentWord DescentResetLocalRoster DescentResetParentCodec
open DescentDenseHostOrder DescentSIMDLookup DescentPackedZip DescentPackedFallbackTree.Image DescentIssuedGoodHeaders
open DescentPacking.PackedMatch.Local.Gather DescentSharedCableNames ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

/-- A probe represents one previous donor, one local socket, one side, and one raw source shape.
Its dynamic inputs are the two issued sender words, the ticket serial, span, both book heights,
and the old peer's port on the current host. -/
def mark {n ports : ℕ} (board : NonlinearExpanders.Graph n ports) (r Ht : ℕ) (s : Bool)
    (q : Root r (2^n)) (z : Fin (2^n+2^Ht)) (sourceShape : ℕ) (own remote serial span dOld dPeer oldPort : ℕ) : ℕ :=
  let other:=peer r (2^n) Ht q z.val own remote serial span
  let mine:=send ⟨0,r,2^n,0,0,0,0⟩ Ht q z
  let here:=outputShape board r Ht s mine dOld
  let there:=outputShape board r Ht (!s) other dPeer
  if other≠0 ∧ here=sourceShape+1 ∧ there≠0 then oldPort*(roster board r Ht).card+there else 0

def fieldAt {n ports b : ℕ} (board : NonlinearExpanders.Graph n ports) (r Ht width : ℕ) (s : Bool)
    (q : Root r (2^n)) (z : Fin (2^n+2^Ht)) (sourceShape : ℕ) (x : Fin 7→Cell b) : Cell width :=
  mark board r Ht s q z sourceShape (x 0).val (x 1).val (x 2).val (x 3).val (x 4).val (x 5).val (x 6).val

variable {H G M w b n ports : ℕ} (board : NonlinearExpanders.Graph n ports)
theorem issue (r Ht width src : ℕ) (s : Bool) (q : Root r (2^n)) (z : Fin (2^n+2^Ht))
    (tables : Fin 7→Tables) (reads : Fin 7→Expr) (menu : DescentSIMDLookup.Banks) (mid : ℕ) (out : Bank)
    (x : Fin H→Fin G→Fin 7→Cell b) (positive : 0<M)
    (mem : Memory w) (bounds : Bounds (w:=w) (d:=b) (M:=M) tables reads mid)
    (statics : ∀j,Static (tables j) (setField (d:=b) j) M mem)
    (inputs : ∀j,Source (reads j) (fun a g=>x a g j) M mem) (rangeOK : mid+H*chunks G M<2^w)
    (fit : DescentSIMDLookup.Fits menu (b*7) width M H G w out.base)
    (rom : resident (fieldAt board r Ht width s q z src ∘ (encode b 7).symm) menu H G M mem)
    (dictLow : menu.dictionary.base+2^((b*7)*M)≤ mid) (maskLow : menu.mask.base+H*chunks G M≤ mid)
    (wire : menu.source.base=mid) (ceiling : ℕ) (outputOK : out.Fits w ceiling) (extent : H*chunks G M≤out.size) :
    let act:=assembly tables reads
    let rows:=H*chunks G M
    let dst:=imageBank H G M out.base menu (image mid rows act mem)
    ((scan w mid rows act).seq (DescentSIMDLookup.program menu out.base H G M w)).Exec mem dst
      ((4+rows*(2*act.work+4))+(4+44*rows)) ∧
    Source (.lookup out .row) (fun a g=>fieldAt board r Ht width s q z src (x a g)) M dst ∧
    ∀addr,(addr< mid ∨ mid+rows≤addr)→(addr<out.base ∨ out.base+rows≤addr)→dst addr=mem addr := by
  obtain ⟨run,read,_,frame⟩:=gathered_words (fieldAt board r Ht width s q z src) tables reads menu
    mid out.base x positive mem bounds statics inputs rangeOK fit rom dictLow maskLow wire
  exact ⟨run,source_column out ceiling outputOK _ _ extent read,frame⟩

theorem mark_empty (r Ht shape serial span localDepth peerDepth oldPort remote : ℕ)
    (s : Bool) (q : Root r (2^n)) (z : Fin (2^n+2^Ht)) :
    mark board r Ht s q z shape 0 remote serial span localDepth peerDepth oldPort=0 := by
  simp [mark,DescentReservedSocketPanel.empty]

end
end Hierarchy.DescentReservedPeerMarker

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentResetPublicParentWord DescentDenseHostOrder DescentCommonHost
open DescentChosenRouter DescentRelativeContacts
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "R" => B.reset.placement
local notation "Ht" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "old" => (Z).orderedReentry T (DescentOrderedReset.grains W B.count B.order)
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "lab"=>fun t=>shortName (T).commonDepth ((T).code t)
local notation "sock"=>fun side c=>direct (Z).graph side (linkSocket (R) lab (T).commonDepth side c)

open DescentResetLocalRoster DescentReservedSocketPanel DescentReservedPeerMarker
local notation "Y" => 2^(Z).n
local notation "SHELF" => (DescentDenseHostOrder.roster (Z).graph r Ht).card
local notation "ownerRoot" => fun s c=>(Z).rootTicket T ((R).owner s c)
local notation "socket" => fun s c=>(⟨(Z).contactSlotWord T s c,(Z).contactSlotWord_lt T s c⟩ : Fin (Y+2^Ht))
local notation "joint" => (Z).senderJoint T
local notation "depth" => (Z).contactDepth
local notation "atEnd" => fun (s : Bool) c=>if s then (blocks B).dst (contactParent B c) else (blocks B).src (contactParent B c)

theorem structural_depth {t v : (R).Contact} (same : ∀s,(R).owner s v=(R).owner s t) (s : Bool) :
    depth s v=depth s t := by
  have hv := same false
  have ht := same true
  cases v with
  | inl v=>cases t with
    | inl t=>rfl
    | inr t=>cases hv
  | inr v=>cases t with
    | inl t=>cases hv
    | inr t=>
      have left : v.val.1=t.val.1:=Sum.inr.inj hv
      have right : v.val.2=t.val.2:=Sum.inr.inj ht
      have eqn : v=t:=Subtype.ext (Prod.ext left right)
      subst t;rfl

/-- All seven input fields here refer to one actual old donor. The row may refer to another
reserved socket. Its remote endpoint carries the same two book heights as this donor. -/
theorem marker_from_donor (s : Bool) (t v : (R).Contact) (serial span port : ℕ)
    (same : ∀a,(R).owner a v=(R).owner a t)
    (issued : peer r Y Ht (ownerRoot s v) (socket s v).val (joint s t) (joint (!s) t) serial span=joint (!s) v) :
    mark (Z).graph r Ht s (ownerRoot s v) (socket s v) (relativeShape B (atEnd s v)) (joint s t) (joint (!s) t)
      serial span (depth s t) (depth (!s) t) port=1+port*SHELF+relativeShape B (atEnd (!s) v) := by
  have present : joint (!s) v≠0:=by unfold ResetInput.senderJoint DescentResetPublicParentWord.send;omega
  have own : send ⟨0,r,Y,0,0,0,0⟩ Ht (ownerRoot s v) (socket s v)=joint s v:=rfl
  simp only [mark,issued,own,←structural_depth B same s,←structural_depth B same (!s),joint_endpoint B s v,joint_endpoint B (!s) v]
  simp [present,Nat.add_comm,Nat.add_assoc,Nat.add_left_comm]

theorem raw_contact_covered (s : Bool) (v : (R).Contact) :
    ∃e,let t:=(R).contact e;
        (∀a,(R).owner a t=(R).owner a v) ∧ ∀serial span port : ℕ,
        (∀i,t=.inl i→serial=i.2.val ∧ span=(R).span i.1)→
        mark (Z).graph r Ht s (ownerRoot s v) (socket s v) (relativeShape B (atEnd s v)) (joint s t) (joint (!s) t)
          serial span (depth s t) (depth (!s) t) port=1+port*SHELF+relativeShape B (atEnd (!s) v) := by
  obtain ⟨e,owners,found⟩:=covers (Z) T B.tickets s v
  exact ⟨e,owners,fun serial span port h=>marker_from_donor B s _ v serial span port (fun a=>(owners a).symm)
      (found serial span h)⟩

/-- Conversely, a nonzero marker identifies an actual socket with the measured source shape
and its exact opposite endpoint. Padding and vacant source-shape positions yield zero. -/
theorem raw_contact_sound (s : Bool) (t : (R).Contact) (q : Root r Y) (z : Fin (Y+2^Ht))
    (src serial span port : ℕ) (paid : ∀i,t=.inl i→serial=i.2.val ∧ span=(R).span i.1)
    (live : mark (Z).graph r Ht s q z src (joint s t) (joint (!s) t)
      serial span (depth s t) (depth (!s) t) port≠0) :
    ∃v : (R).Contact,(∀a,(R).owner a v=(R).owner a t) ∧
      q=ownerRoot s v ∧ z=socket s v ∧ src=relativeShape B (atEnd s v) ∧
      mark (Z).graph r Ht s q z src (joint s t) (joint (!s) t) serial span (depth s t) (depth (!s) t) port=
        1+port*SHELF+relativeShape B (atEnd (!s) v) := by
  have entered : peer r Y Ht q z.val (joint s t) (joint (!s) t) serial span≠0:=by
    intro blank
    simp [mark,blank] at live
  obtain ⟨v,owners,rq,rz,other⟩:=sound (Z) T s t q z.val serial span paid entered
  have coord : z=socket s v:=Fin.ext rz
  subst q;subst z
  have mine : send ⟨0,r,Y,0,0,0,0⟩ Ht (ownerRoot s v) (socket s v)=joint s v:=rfl
  have shapeOK : relativeShape B (atEnd s v)=src:=by
    by_contra wrong
    have neq : relativeShape B (atEnd s v)+1≠src+1:=by omega
    simp only [mark,mine,←structural_depth B owners s,joint_endpoint B s v] at live
    exact live (ite_eq_right (fun test => neq test.2.1))
  subst src
  exact ⟨v,owners,rfl,rfl,rfl,marker_from_donor B s t v serial span port owners other⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
