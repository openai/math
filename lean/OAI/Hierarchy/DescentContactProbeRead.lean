import OAI.Hierarchy.DescentContactPortfolio
import OAI.Hierarchy.DescentReservedProbeInputs
import OAI.Hierarchy.DescentPackedIssuedBookRank

namespace OAI
/-! # Authentic seven input fields of a bounded structural contact marker -/
namespace Hierarchy.DescentContactProbeRead
open DescentSIMDLookup DescentSharedCableNames.Stage DescentResetPublicParentWord DescentResetLocalRoster
open scoped Classical Fin.CommRing
noncomputable section

/-- Preserve the old neighbor field only on its actual directed face. An opposite face in the
same signed rectangle is a vacant donor for this probe. -/
def portField (D cap : ℕ) (s : Bool) (x : Cell (DescentSignedCableCodec.width D cap)) : Option (Fin D) :=
  ((DescentSignedCableCodec.decode D cap x).filter (fun v=>decide (v.target=s))).map Live.neighbor

/-- The old book census is shared for each fallback address. Rotors have no fallback book. -/
def heightFrom (r Y Ht joint amount : ℕ) : ℕ :=
  match unpack ⟨0,r,Y,0,0,0,0⟩ Ht joint with
  | some (.inr _,_)=>Nat.clog 2 amount
  | _=>0

def inputs {b D cap : ℕ} (r Y Ht : ℕ) (s : Bool) (chip : Cell (DescentSignedCableCodec.width D cap))
    (raw : Fin 6→Cell b) : Fin 7→Cell b :=
  match portField D cap s chip with
  | none=>fun _=>0
  | some port=>![raw 0,raw 1,raw 2,raw 3,heightFrom r Y Ht (raw 0).val (raw 4).val,
      heightFrom r Y Ht (raw 1).val (raw 5).val,port.val]
end
end Hierarchy.DescentContactProbeRead

namespace Hierarchy.DescentIssuedFallbackPanel
open DescentSharedCableNames Stage DescentSixParty
open scoped Classical
noncomputable section
private theorem directed_signed {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i : ℕ} {bits : P → ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
    (A : GroupStage W G q ε J V k) (native : W.graph.Edge ↪ ℕ) (S : DescentCompiler.AtomSchedule)
    (ready : A.StateBounds S i) (names : Stage.Host J V k ↪ ℕ)
    (s : Bool) (h : Stage.Host J V k) (j : Fin (2 * A.cap)) :
    ((Stage.signedPanel A native S ready names h j).filter (fun t => decide (t.target = s))).map Stage.Live.neighbor =
      (atSlot A native S ready s h j).map
        (fun e => (Stage.live A native S ready names (port A s e).1 (port A s e).2).neighbor) := by
  cases found : atSlot A native S ready s h j with
  | some e =>
    have addr := (atSlot_iff A native S ready s h j e).mp found
    have facing : (Stage.live A native S ready names (port A s e).1 (port A s e).2).target = s := by cases s <;> rfl
    obtain ⟨v,p,hp⟩ : ∃ v : Stage.Host J V k, ∃ p : A.CellPorts v.1.1 v.1.2 v.2,
        port A s e = ⟨v,p⟩ := ⟨(port A s e).1,(port A s e).2,rfl⟩
    simp only [Option.map_some] at *
    rw [hp] at addr facing ⊢
    have same : v = h := congrArg Prod.fst addr
    subst v
    have slot : Stage.signed A native S ready h.1 h.2 p = j := congrArg Prod.snd addr
    rw [←slot,Stage.signed_read]
    simp [facing]
  | none =>
    by_cases used : ∃ p : A.CellPorts h.1.1 h.1.2 h.2, Stage.signed A native S ready h.1 h.2 p = j
    · obtain ⟨p,rfl⟩ := used
      have wrong : (Stage.live A native S ready names h p).target ≠ s := by
        intro same
        let e := Stage.recover A h p
        have eqn := from_any A native S ready names h p
        change port A (Stage.live A native S ready names h p).target e = ⟨h,p⟩ at eqn
        rw [same] at eqn
        have yes := (atSlot_iff A native S ready s h (Stage.signed A native S ready h.1 h.2 p) e).mpr
          (congrArg (address A native S ready) eqn)
        rw [found] at yes
        contradiction
      simp [Stage.signed_read,wrong]
    · simp [Stage.signed_empty A native S ready names h _ (not_exists.mp used)]
end
end Hierarchy.DescentIssuedFallbackPanel

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentPacking.PackedMatch.Local.Stage DescentStageEdgeReceipt
open DescentCompiler DescentColonies DescentGL DescentChosenRouter DescentSharedCableNames
open DescentGroupPeerOrder DescentIssuedFallbackPanel DescentReservedPeerMarker DescentResetLocalRoster
open DescentDenseHostOrder DescentResetAttachments DescentSIMDLookup DescentContactProbeRead
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "R" => B.reset.placement
local notation "A" => input.placement
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "E" => (old).graph.Edge
local notation "Y" => 2^(Z).n
local notation "height" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "shelf" => (DescentDenseHostOrder.roster (Z).graph r height).card
local notation "groups" => S.groupCount (i+1)
local notation "Host" => Stage.Host (Fin groups) B.next.V k
local notation "half" => 2^(S.groupWidth k tail i+k-(T).commonDepth)*(2*(A).cap)
local notation "joint" => (Z).senderJoint T
local notation "site" s:arg c:arg => (if s then (blocks B).dst (contactParent B c) else (blocks B).src (contactParent B c))
local notation "before" => input.order.trans Fin.valEmbedding
local notation "names" => cableNames k (groupRank (Fin.valEmbedding (n:=S.groupCount i)) (input.vertex.trans Fin.valEmbedding))
local notation "extent" => B.frame.enough.trans (Nat.sub_le ..)
local notation "digitsIn" => S.resetInputDigits ctl.base ctl.radix i
local notation "bookAt" s:arg t:arg => (T).leaves.window (DescentRelativeContacts.shortName (T).commonDepth ((T).code (fallEnd (R) s t)))
local notation "markAt" p:arg u:arg => mark (Z).graph r height p.1 p.2.1 p.2.2 (relativeShape B u)
local notation "fieldAt" b:arg p:arg u:arg => DescentReservedPeerMarker.fieldAt (Z).graph r height b p.1 p.2.1 p.2.2 (relativeShape B u)

theorem contactRowMark_bound (u : Host) (p : ContactProbe B) (e : E) :
    contactRowMark B u p e≤(A).degree*shelf := by
  by_cases zero : contactRowMark B u p e=0
  · rw [zero];exact Nat.zero_le _
  let t:=(R).contact e
  obtain ⟨v,_,_,_,_,eqn⟩:=raw_contact_sound B p.1 t p.2.1 p.2.2 (relativeShape B u)
    (contactTicketDigit B t) (contactPairSpan B t) (contactOldPort B p.1 e).val
    (by rintro a ha;rw [ha];exact ⟨rfl,rfl⟩) zero
  have small : relativeShape B (site (!p.1) v)<shelf:=
    (((Z).hostFields T (B.frame.host.symm.toEmbedding.trans input.vertex) (site (!p.1) v).1.2).2).isLt
  calc contactRowMark B u p e=1+(contactOldPort B p.1 e).val*shelf+relativeShape B (site (!p.1) v) := eqn
       _≤((contactOldPort B p.1 e).val+1)*shelf:=by rw [Nat.succ_mul];omega
       _≤(A).degree*shelf:=Nat.mul_le_mul_right _ (contactOldPort B p.1 e).isLt

/-- Output fits for the whole old-degree by shape directory, independent of donor and socket. -/
def contactMarkBits := Nat.clog 2 ((A).degree*shelf+1)

theorem contactMark_room : (A).degree*shelf<2^(contactMarkBits B) :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_pow_clog (by decide) _)

private theorem fallback_digits (s : Bool) (t) (p : ContactProbe B) (u : Host)
    (a b x y h₁ h₂ port : ℕ) :
    (markAt p u) (joint s (.inr t)) (joint (!s) (.inr t)) a b h₁ h₂ port=
      (markAt p u) (joint s (.inr t)) (joint (!s) (.inr t)) x y h₁ h₂ port := by
  simp only [DescentReservedPeerMarker.mark, DescentReservedSocketPanel.peer,
    DescentReservedSocketPanel.donor_decode (Z) T s (.inr t),
    DescentReservedSocketPanel.donor_decode (Z) T (!s) (.inr t)]
  rfl

/-- The six non-ordinal fields may be emitted independently; their arrival has already been
localized to this signed donor. Vacant fallback reservations have no constraint on ticket digits. -/
theorem contactRowMark_read {b width : ℕ} (u : Host) (p : ContactProbe B) (e : E) (x : Fin 7→Cell b)
    (room : (A).degree*shelf<2^width)
    (own : (x 0).val=joint p.1 ((R).contact e)) (remote : (x 1).val=joint (!p.1) ((R).contact e))
    (ticket : ∀t,(R).contact e=.inl t→(x 2).val=t.2.val ∧ (x 3).val=(R).span t.1)
    (left : (x 4).val=(Z).contactDepth p.1 ((R).contact e))
    (right : (x 5).val=(Z).contactDepth (!p.1) ((R).contact e))
    (port : (x 6).val=(contactOldPort B p.1 e).val) :
    ((fieldAt width p u) x).val=contactRowMark B u p e := by
  have one : (markAt p u) (x 0).val (x 1).val (x 2).val (x 3).val (x 4).val (x 5).val (x 6).val=
      contactRowMark B u p e := by
    rw [own,remote,left,right,port,contactRowMark]
    cases hOld : (R).contact e with
    | inl t=>obtain ⟨a,b⟩:=ticket t hOld;rw [a,b]; rfl
    | inr t=>exact fallback_digits B p.1 t p u _ _ _ _ _ _ _
  change (((markAt p u) (x 0).val (x 1).val (x 2).val (x 3).val (x 4).val (x 5).val (x 6).val : ℕ) : Cell width).val=_
  rw [one]
  exact Fin.val_cast_of_lt ((contactRowMark_bound B u p e).trans_lt room)

theorem contact_height_read (s : Bool) (t : (R).Contact) (amount : ℕ)
    (measured : ∀v,t=.inr v→amount=(bookAt s v).card) :
    heightFrom r Y height (joint s t) amount=(Z).contactDepth s t := by
  rw [heightFrom,DescentReservedSocketPanel.donor_decode (Z) T s t]
  cases t with
  | inl t=>rfl
  | inr t=>exact (congrArg (Nat.clog 2) (measured t rfl)).trans ((T).leaves.depth s (fallEnd (R) s t)).symm

theorem contact_depth_bound (s : Bool) (t : (R).Contact) : (Z).contactDepth s t≤height := by
  cases t with
  | inl t=>exact Nat.zero_le _
  | inr t=>exact (T).bookHeight s (fallEnd (R) s t)

local notation "prev" => Stage.Host (Fin (S.groupCount i)) input.V k
local notation "SG" => (Stage.signed A before S input.valid)
local notation "SD" => (Stage.signedPanel A before S input.valid names)
local notation "grainPort" s:arg e:arg => port A s (beforeStem B e)
local notation "chipVal" h:arg a:arg => Stage.live A before S input.valid names h a


def contactSignedWord (u : Host) (j : Fin half) : Cell (DescentSignedCableCodec.width (A).degree (A).cap) :=
  let at_ : Fin (2^(S.groupWidth k tail i+k-(T).commonDepth))×Fin (2*(A).cap):=finProdFinEquiv.symm j
  DescentSignedCableCodec.encode (SD
    (donor digitsIn B.frame.basis extent (B.frame.host.symm (receiverRoot B u).1) (receiverRoot B u).2 at_.1) at_.2)

theorem contact_signed_port (u : Host) (s : Bool) (j : Fin half) :
    portField (A).degree (A).cap s (contactSignedWord B u j)=
      (originalDonor B u s j).map (contactOldPort B s) := by
  let a : Fin (2^(S.groupWidth k tail i+k-(T).commonDepth))×Fin (2*(A).cap):=finProdFinEquiv.symm j
  let h:=donor digitsIn B.frame.basis extent (B.frame.host.symm (receiverRoot B u).1) (receiverRoot B u).2 a.1
  rw [portField,contactSignedWord,DescentSignedCableCodec.decode_encode,directed_signed A before S input.valid names s h a.2]
  change (stemDonor B u s a).map _=((stemDonor B u s a).map (priorGrain B).symm).map _
  cases read : stemDonor B u s a with
  | none=>rfl
  | some e=>
    change some (chipVal (port A s e).1 (port A s e).2).neighbor=
      some (contactOldPort B s ((priorGrain B).symm e))
    change _=some (chipVal (port A s (priorGrain B ((priorGrain B).symm e))).1
      (port A s (priorGrain B ((priorGrain B).symm e))).2).neighbor
    rw [Equiv.apply_symm_apply]

/-- The six incoming columns are local and returned sender words, two paid reservation digits
and the local and returned fallback book counts. The true old signed chip supplies the seventh
field and its polarity. An unoccupied donor reads zero regardless of the six other columns. -/
structure ProbeRead {b : ℕ} (u : Host) (p : ContactProbe B) (j : Fin half) (raw : Fin 6→Cell b) : Prop where
  own : ∀e,originalDonor B u p.1 j=some e→(raw 0).val=joint p.1 ((R).contact e)
  remote : ∀e,originalDonor B u p.1 j=some e→(raw 1).val=joint (!p.1) ((R).contact e)
  paid : ∀e,originalDonor B u p.1 j=some e→∀t,(R).contact e=.inl t→
    (raw 2).val=t.2.val ∧ (raw 3).val=(R).span t.1
  books : ∀e,originalDonor B u p.1 j=some e→∀t,(R).contact e=.inr t→
    (raw 4).val=(bookAt p.1 t).card ∧ (raw 5).val=(bookAt (!p.1) t).card

theorem contactProbe_raw {b width : ℕ} (u : Host) (p : ContactProbe B) (j : Fin half)
    (chip : Cell (DescentSignedCableCodec.width (A).degree (A).cap)) (raw : Fin 6→Cell b)
    (reached : chip=contactSignedWord B u j) (previous : ProbeRead B u p j raw)
    (oldRoom : (A).degree≤2^b) (depthRoom : height<2^b) (room : (A).degree*shelf<2^width) :
    ((fieldAt width p u) (inputs r Y height p.1 chip raw)).val=
      contactSheet B u (probeId B p) (finProdFinEquiv (finTwoEquiv.symm p.1,j)) := by
  rw [contactSheet_read,inputs,reached,contact_signed_port]
  cases sel : originalDonor B u p.1 j with
  | none=>
    change (((markAt p u) 0 0 0 0 0 0 0 : ℕ) : Cell width).val=0
    rw [DescentReservedPeerMarker.mark_empty]; rfl
  | some e=>
    let t:=(R).contact e
    have own:=previous.own e sel
    have remote:=previous.remote e sel
    have hl : heightFrom r Y height (raw 0).val (raw 4).val=(Z).contactDepth p.1 t :=
      by rw [own];exact contact_height_read B p.1 t _ (fun v hv=>(previous.books e sel v hv).1)
    have hr : heightFrom r Y height (raw 1).val (raw 5).val=(Z).contactDepth (!p.1) t :=
      by rw [remote];exact contact_height_read B (!p.1) t _ (fun v hv=>(previous.books e sel v hv).2)
    apply contactRowMark_read B u p e _ room own remote (previous.paid e sel)
    · exact (Fin.val_cast_of_lt (show heightFrom r Y height (raw 0).val (raw 4).val<2^b by rw [hl];exact (contact_depth_bound B p.1 t).trans_lt depthRoom)).trans hl
    · exact (Fin.val_cast_of_lt (show heightFrom r Y height (raw 1).val (raw 5).val<2^b by rw [hr];exact (contact_depth_bound B (!p.1) t).trans_lt depthRoom)).trans hr
    · exact Fin.val_cast_of_lt ((contactOldPort B p.1 e).isLt.trans_le oldRoom)

/-- Read the installed seven-source marker page directly. On a vacant row only the local
joint is required to be zero. The other six columns can hold values for unrelated roles. -/
theorem contactSheet_columns {b width : ℕ} (u : Host) (p : ContactProbe B) (j : Fin half)
    (x : Fin 7→Cell b) (room : (A).degree*shelf<2^width)
    (own : (x 0).val=(originalDonor B u p.1 j).elim 0 (fun e=>joint p.1 ((R).contact e)))
    (active : ∀e,originalDonor B u p.1 j=some e→
      (x 1).val=joint (!p.1) ((R).contact e) ∧
      (∀t,(R).contact e=.inl t→(x 2).val=t.2.val ∧ (x 3).val=(R).span t.1) ∧
      (x 4).val=(Z).contactDepth p.1 ((R).contact e) ∧
      (x 5).val=(Z).contactDepth (!p.1) ((R).contact e) ∧
      (x 6).val=(contactOldPort B p.1 e).val) :
    ((fieldAt width p u) x).val=contactSheet B u (probeId B p) (finProdFinEquiv (finTwoEquiv.symm p.1,j)) := by
  rw [contactSheet_read]
  cases sel : originalDonor B u p.1 j with
  | none=>
    have absent : (x 0).val=0:=by simpa [sel] using own
    change (((markAt p u) (x 0).val (x 1).val (x 2).val (x 3).val (x 4).val (x 5).val (x 6).val : ℕ) : Cell width).val=0
    rw [absent,DescentReservedPeerMarker.mark_empty]; rfl
  | some e=>
    obtain ⟨remote,ticket,localD,peerD,port⟩:=active e sel
    exact contactRowMark_read B u p e x room (by simpa [sel] using own) remote ticket localD peerD port

/-- This converts the published packed menu output to the real two-axis incidence sheet on the
same memory. All components can vary across the lanes, including the previous neighbor socket. -/
theorem contactProbe_source {b width hosts rows M word : ℕ} (p : ContactProbe B) (j : Fin half) (src : ℕ)
    (u : Fin hosts→Fin rows→Host)
    (chip : Fin hosts→Fin rows→Cell (DescentSignedCableCodec.width (A).degree (A).cap))
    (prior : Fin hosts→Fin rows→Fin 6→Cell b) (mem : Memory word)
    (reader : ProtocolRAM.Expr)
    (shape : ∀a g,relativeShape B (u a g)=src) (orig : ∀a g,chip a g=contactSignedWord B (u a g) j)
    (read : ∀a g,ProbeRead B (u a g) p j (prior a g)) (oldRoom : (A).degree≤2^b)
    (depthRoom : height<2^b) (room : (A).degree*shelf<2^width)
    (printed : DescentPackedZip.Source reader (fun a g=>DescentReservedPeerMarker.fieldAt (Z).graph r height width p.1
      p.2.1 p.2.2 src (inputs r Y height p.1 (chip a g) (prior a g))) M mem) :
    DescentPackedZip.Source reader (fun a g=>(contactSheet B (u a g) (probeId B p)
      (finProdFinEquiv (finTwoEquiv.symm p.1,j)) : Cell width)) M mem := by
  have val (a : Fin hosts) (g : Fin rows) := contactProbe_raw B (u a g) p j (chip a g) (prior a g)
    (orig a g) (read a g) oldRoom depthRoom room
  have same : (fun a g=>DescentReservedPeerMarker.fieldAt (Z).graph r height width p.1 p.2.1 p.2.2 src
      (inputs r Y height p.1 (chip a g) (prior a g)))=(fun a g=>(contactSheet B (u a g) (probeId B p)
      (finProdFinEquiv (finTwoEquiv.symm p.1,j)) : Cell width)) := by
    funext a g
    rw [←shape a g,←val a g]
    simp
  rwa [same] at printed


end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
