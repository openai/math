import OAI.Hierarchy.DescentCalendarEnteredCandidateHeaders
import OAI.Hierarchy.DescentPhysicalRankSheetIntake

namespace OAI
/-! # The measured contact and private sectors in the signed rank chart -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentPackedColony Computability.VPVNP.BurstRAM PrivateRAM DescentDatedAddressBook DescentCompiler DescentColonies DescentDenseHostOrder DescentResetLocalRoster
open DescentPackedPrivateMenu DescentResetPeerUnionRAM DescentPackedColony DescentSIMDLookup
open DescentGroupPeerOrder DescentSortedRoster DescentContactOutputShape DescentPacking.PackedMatch.Local.Stage
open ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
set_option hygiene false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => input.placement
local notation "H" => S.hostSize i
local notation "J" => 2^(T).commonDepth
local notation "r" => (Z).k-(T).commonDepth
local notation "ht" => GroupStage.depthBound D n f g
local notation "shelf" => (DescentDenseHostOrder.roster (Z).graph r ht).card
local notation "gs" => S.groupCount (i+1)
local notation "cap₀" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(ht+1))
local notation "oldWidth" => DescentPackedPrivateMenu.fieldBits (Z).graph r ht (2^r*(2*(A).cap))
    (DescentRecordedRotorLayers.width f (A).cap) C (Z).width
variable (oldBatch batch : ℕ) (calendar : List ℕ) (paid : (A).cap=(calendar.take i).prod*256)
local notation "cap" => (calendar.take i).prod*256
local notation "field₀" => ResetMiddle.fieldWidth D cap n k ht
local notation "table₀" => CandidateSheets.fromBoard S ctl.board k tail i D f g cap batch
local notation "meta₀" => (table₀).metaBits
local notation "month" => CandidateFront.menu S ctl.board k tail i D f g oldBatch batch C ctl.bitsR calendar
local notation "good" => contactOutputs B H oldBatch field₀ (Nat.clog 2 (D+2)) (Nat.clog 2 (D+3)) gs (2^k)
    batch (month).contact.outputBits meta₀
local notation "deck" => privateProjection («H»:=H) (field:=oldWidth) B oldBatch batch meta₀
variable {date : PhysicalReset} {floor bw : ℕ} (I : date.DateInputs floor bw)
local notation "v₀" => date.successor
local notation "base₀" => date.rebased floor
local notation "phys₀" => (v₀).front
local notation "peer₀" => (phys₀).peer
local notation "pitch₀" => (phys₀).contactLayout ((v₀).actorEnd base₀)
local notation "Q₀" => (v₀).privateShape
local notation "K₀" => (v₀).contactShape
local notation "don₀" => (phys₀).donorStart ((v₀).actorEnd base₀)
local notation "used" => Fintype.card B.next.V
local notation "rawSize" => H*shelf
local notation "L" => 2^(S.groupWidth k tail i+k-(T).commonDepth)
local notation "K" => 2*(A).cap
local notation "F₀" => DescentOldContactSender.count (A).degree L (A).cap (Z).n r
variable (cal : MixedGeometry B oldBatch batch calendar v₀ base₀) (pad : Fintype.card input.V≤H)
local notation "portChart" => input.vertex.trans (Fin.castLEEmb pad)
local notation "adj_" => hostRotor portChart (hostRoster (A) ((portChart).trans Fin.valEmbedding))
variable {keyBits : ℕ} (prior : PriorPeerWords B H oldWidth keyBits)
    (xs : Fin H→Fin J→Fin F₀→Cell field₀) (raw : Fin L→Fin K→Fin H→Fin J→Cell field₀)
    (near : Fin rawSize→Fin 3→Option (Fin rawSize))

open DescentResetRankedWindows DescentResetCandidatePair DescentPackedZip DescentResetFieldAssembler
local notation "s₀" => (v₀).sheets
variable (bound : used≤(s₀).hosts) (geo : PhysicalReset.DateInputs.SheetGeometry I)
local notation "dense₀" => ((Z).denseHostRank T ((B.frame.host.symm.toEmbedding.trans input.vertex).trans
    (Fin.castLEEmb pad))).trans (Fin.castLEEmb bound)
local notation "rack₀" => rackOf B dense₀
local notation "gx" => congrArg DescentPrivateMaskDeck.Shape.groups cal.privateDeck
local notation "bx" => congrArg DescentPrivateMaskDeck.Shape.blocks cal.privateDeck
local notation "cx" => geo.contacts.trans (congrArg DescentContactOutputShape.Shape.sockets cal.contactDeck)
local notation "px" => geo.privates.trans (congrArg DescentPrivateMaskDeck.Shape.keys cal.privateDeck)
local notation "pos" => CandidateSheet.index (stemsCount B) (contactCount B) (privateCount B)
local notation "meter" => DescentResetFieldAssembler.raw (s₀).metaBits

private theorem dense_rank_at (v : Fin (s₀).hosts) :
    rack₀ v=if live:v.val<used then some ((compactActorOrder B pad).symm ⟨v.val,live⟩) else none:=by
  by_cases live:v.val<used
  · rw [dite_eq_left live]
    let u:=(compactActorOrder B pad).symm ⟨v.val,live⟩
    have id : dense₀ u=v:=by
      apply Fin.ext
      exact congrArg (fun ix : Fin used => ix.val) ((compactActorOrder B pad).apply_symm_apply ⟨v.val,live⟩)
    change rack₀ v = some u
    exact (congrArg (rackOf B dense₀) id).symm.trans (rack_present B dense₀ u)
  · rw [dite_eq_right live]
    apply rack_missing
    intro u same
    exact live ((congrArg Fin.val same) ▸ ((compactActorOrder B pad u).isLt))

theorem contact_rank_meta (x : Fin (s₀).blocks) (q : Fin (s₀).contacts)
    (v : Fin (s₀).hosts) (grp : Fin I.masked.groups) :
    (if live:v.val<used then contact_meta_at B oldBatch batch calendar I cal pad geo x q ⟨v.val,live⟩ grp else Meta.blank)=
      actualMeta B rack₀ (x.cast bx) (pos (.inr (.inr (.inl (q.cast cx))))) v (grp.cast gx):=by
  have ind : pos (.inr (.inr (.inl (q.cast cx))))=contactShelfIndex B (q.cast cx):=
    Fin.ext (CandidateSheet.contact_val _)
  rw [ind,actualMeta,dense_rank_at B pad bound]
  by_cases live:v.val<used
  · simp [live,contact_meta_at]
    rfl
  · simp [live]

theorem private_rank_meta (x : Fin (s₀).blocks) (q : Fin (s₀).privates)
    (v : Fin (s₀).hosts) (grp : Fin I.masked.groups) :
    (if live:v.val<used then private_meta_at B oldBatch batch calendar I cal pad geo x q ⟨v.val,live⟩ grp else Meta.blank)=
      actualMeta B rack₀ (x.cast bx) (pos (.inr (.inr (.inr (q.cast px))))) v (grp.cast gx):=by
  have ind : pos (.inr (.inr (.inr (q.cast px))))=privateShelfIndex B (q.cast px):=
    Fin.ext (CandidateSheet.private_val _)
  rw [ind,actualMeta,dense_rank_at B pad bound]
  by_cases live:v.val<used
  · simp [live,private_meta_at]
    rfl
  · simp [live]

private theorem reindex_group {w hostCount a n n' M : ℕ} {m : Computability.VPVNP.BurstRAM.Memory w} {e : Expr}
    (groupIx : n=n') (v : Fin hostCount→Fin n'→Cell a) (seen : Source e (fun h g=>v h (g.cast groupIx)) M m) :
    Source e v M m:=by subst n';exact seen

theorem shaped_contact {X X' s s' c c' p p' : ℕ} (hx:X=X') (hs:s=s') (hc:c=c') (hp:p=p')
    (src : Inputs X s c p) (x : Fin X') (j : Fin c') :
    shaped hx hs hc hp src x (.inr (.inr (.inl j)))=src (x.cast hx.symm) (.inr (.inr (.inl (j.cast hc.symm)))):=by
  subst X';subst s';subst c';subst p';rfl
theorem shaped_private {X X' s s' c c' p p' : ℕ} (hx:X=X') (hs:s=s') (hc:c=c') (hp:p=p')
    (src : Inputs X s c p) (x : Fin X') (j : Fin p') :
    shaped hx hs hc hp src x (.inr (.inr (.inr j)))=src (x.cast hx.symm) (.inr (.inr (.inr (j.cast hp.symm)))):=by
  subst X';subst s';subst c';subst p';rfl

/-- The two actual preceding sources in the original date's sectors have the values
read by the shared rank pass at every block, host and groupIx, including ghosts. -/
theorem rank_private_contact_sources
    (hx : (v₀).receiver.blocks=2^k) (hs : I.sectors.stems=stemsCount B)
    (hc : I.sectors.contacts=contactCount B) (hp : I.sectors.privates=privateCount B)
    (state : Computability.VPVNP.BurstRAM.Memory bw)
    (contacts : ∀(x:Fin (s₀).blocks) q,Source (I.sectorHeader x.val (.inr (.inr (.inl q))))
      (fun (v:Fin (s₀).hosts) grp=>meter (if live:v.val<used then contact_meta_at B oldBatch batch calendar I cal pad geo x q ⟨v.val,live⟩ grp else Meta.blank))
      (s₀).lanes state)
    (privateRows : ∀(x:Fin (s₀).blocks) q,Source (I.sectorHeader x.val (.inr (.inr (.inr q))))
      (fun (v:Fin (s₀).hosts) grp=>meter (if live:v.val<used then private_meta_at B oldBatch batch calendar I cal pad geo x q ⟨v.val,live⟩ grp else Meta.blank))
      (s₀).lanes state) :
    (∀x q,Source (shaped hx hs hc hp I.sectors.header x (.inr (.inr (.inl q))))
      (fun v grp=>meter (actualMeta B rack₀ x (pos (.inr (.inr (.inl q)))) v grp)) (s₀).lanes state) ∧
    (∀x q,Source (shaped hx hs hc hp I.sectors.header x (.inr (.inr (.inr q))))
      (fun v grp=>meter (actualMeta B rack₀ x (pos (.inr (.inr (.inr q)))) v grp)) (s₀).lanes state):=by
  constructor
  · intro x q
    rw [shaped_contact]
    apply reindex_group gx
    have read:=contacts (x.cast (bx).symm) (q.cast hc.symm)
    simp only [contact_rank_meta B oldBatch batch calendar I cal pad bound geo] at read
    exact read
  · intro x q
    rw [shaped_private]
    apply reindex_group gx
    have read:=privateRows (x.cast (bx).symm) (q.cast hp.symm)
    simp only [private_rank_meta B oldBatch batch calendar I cal pad bound geo] at read
    exact read

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
