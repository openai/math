import OAI.Hierarchy.DescentContactDonorSelection
import OAI.Hierarchy.DescentContactSenderSearch
import OAI.Hierarchy.DescentResetPublicParentRaster
import OAI.Hierarchy.DescentReservedPeerMarker

namespace OAI
/-! # Selecting actual original signed donors at a fixed reached reset receiver -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentResetPublicParentWord DescentDenseHostOrder
open DescentResetLocalRoster DescentParallelBase DescentSIMDLookup DescentResetParentCodec
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
local notation "Y" => 2^(Z).n
local notation "r" => (Z).k-(T).commonDepth
local notation "Ht" => GroupStage.depthBound D n f g
local notation "pal" => DescentDenseHostOrder.roster (Z).graph r Ht
local notation "hostCodes" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "old" => W.granular B.count (z*G.b) B.fit

open DescentContactDonorSelection DescentReservedSocketPanel DescentReservedPeerMarker
local notation "L" => 2^(S.groupWidth k tail i+k-(T).commonDepth)
local notation "K" => 2*input.placement.cap
local notation "here" => fun s c=>((Z).rootVertex T ((R).owner s c),(Z).rootBlock T ((R).owner s c))
local notation "joint" => (Z).senderJoint T

def originalDonor (u : Host) (side : Bool) (j : Fin (L*K)) : Option (old).graph.Edge :=
  oldStemAt B u side (finProdFinEquiv.symm j)

theorem originalDonor_exists (u : Host) (side : Bool) (c : (R).Contact) (root : receiverRoot B u=here side c)
    (e : (old).graph.Edge) (holds : (R).owner side ((R).contact e)=(R).owner side c) :
    ∃j : Fin (L*K),originalDonor B u side j=some e := by
  obtain ⟨j,atOld⟩:=contact_old_slot B u side c e root holds
  exact ⟨finProdFinEquiv j,by simpa [originalDonor] using atOld⟩

theorem sender_not_zero (side : Bool) (c : (R).Contact) : joint side c≠0:=by
  unfold ResetInput.senderJoint DescentResetPublicParentWord.send
  omega

/-- The source and cargo are the two actual finite old signed sheets. Per-donor zero witnesses
are allowed in padding. A positive original grain ensures the requested sheet has a live visit. -/
theorem first_sender {a b : ℕ} (u : Host) (side : Bool) (c : (R).Contact)
    (root : receiverRoot B u=here side c) (live : active (blocks B) u (contactParent B c))
    (own : Fin (L*K)→Cell a) (cargo : Fin (L*K)→Cell b) (field : (R).Contact→Cell b)
    (label : ∀j,(own j).val=(originalDonor B u side j).elim 0 (fun e=>joint side ((R).contact e)))
    (pr : ∀j e,originalDonor B u side j=some e→cargo j=field ((R).contact e))
    (present : field c≠0) : visits (joint side c) own cargo=field c := by
  obtain ⟨e,who⟩:=actual_contact_grain B u c live
  obtain ⟨j,land⟩:=originalDonor_exists B u side c root e (congrArg ((R).owner side) who)
  have real (j' : Fin (L*K)) (same : (own j').val=joint side c) : ∃e,originalDonor B u side j'=some e ∧ (R).contact e=c:=by
    cases eqn : originalDonor B u side j' with
    | none=>
      have absent : (own j').val=0:=by rw [label,eqn];rfl
      exact False.elim (sender_not_zero B side c (same.symm.trans absent))
    | some e=>
      have home:=contact_old_slot_location B u side (finProdFinEquiv.symm j') e eqn
      have equal:=home.symm.trans root
      exact ⟨e,rfl,contact_sender_word_unique B side (congrArg Prod.fst equal) (congrArg Prod.snd equal)
        (by simpa [label,eqn] using same)⟩
  apply found _ _ _ _ (sender_not_zero B side c)
  · exact ⟨j,by simp [label,land,who],by rwa [pr j e land,who]⟩
  · intro t hit
    obtain ⟨v,loc,exactContact⟩:=real t hit
    rw [pr t v loc,exactContact]

/-- A numerical positive representative on either side yields the left sender word required by
the compact parent raster, including at receivers reached only from the old target side. -/
theorem first_left_sender {a b : ℕ} (u : Host) (side : Bool) (c : (R).Contact)
    (root : receiverRoot B u=here side c) (live : active (blocks B) u (contactParent B c))
    (own : Fin (L*K)→Cell a) (cargo : Fin (L*K)→Cell b)
    (label : ∀j,(own j).val=(originalDonor B u side j).elim 0 (fun e=>joint side ((R).contact e)))
    (pr : ∀j e,originalDonor B u side j=some e→(cargo j).val=joint false ((R).contact e))
    (width : ∀v,joint false v<2^b) : (visits (joint side c) own cargo).val=joint false c := by
  let payload:=fun v : (R).Contact=>(⟨joint false v,width v⟩ : Cell b)
  have valid : payload c≠0:=fun h=>sender_not_zero B false c (congrArg Fin.val h)
  exact congrArg Fin.val (first_sender B u side c root live own cargo payload label
    (fun j e h=>Fin.ext (pr j e h)) valid)

/-- For per-donor unfiltered probes the witness is located in the very same physical old
rectangle. The scalar input calibration is only needed on this genuine occupied predecessor. -/
theorem marker_donor_exists (u : Host) (side : Bool) (c : (R).Contact) (root : receiverRoot B u=here side c) :
    ∃(j : Fin (L*K)) (e : (old).graph.Edge),originalDonor B u side j=some e ∧
      let t:=(R).contact e;
      (∀a,(R).owner a t=(R).owner a c) ∧ ∀serial span port : ℕ,
      (∀v,t=.inl v→serial=v.2.val ∧ span=(R).span v.1)→
      mark (Z).graph r Ht side ((Z).rootTicket T ((R).owner side c)) ⟨_,(Z).contactSlotWord_lt T side c⟩
        (relativeShape B (if side then (blocks B).dst (contactParent B c) else (blocks B).src (contactParent B c)))
        (joint side t) (joint (!side) t) serial span ((Z).contactDepth side t) ((Z).contactDepth (!side) t) port=
        1+port*(pal).card+relativeShape B (if !side then (blocks B).dst (contactParent B c) else (blocks B).src (contactParent B c)) := by
  obtain ⟨e,owns,receipt⟩:=raw_contact_covered B side c
  obtain ⟨j,land⟩:=originalDonor_exists B u side c root e (owns side)
  exact ⟨j,e,land,owns,receipt⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
