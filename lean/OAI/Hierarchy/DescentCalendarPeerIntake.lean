import OAI.Hierarchy.DescentReachedCalendarPeers
import OAI.Hierarchy.DescentFrontEarlierRoot
import OAI.Hierarchy.DescentResetPeerOldReadings

namespace OAI
/-! # The attained actor and private-root banks are the original operands of the calendar scan -/
namespace Hierarchy.DescentResetPeerUnionRAM.PeerCatalog
open DescentSIMDLookup
noncomputable section
variable {C A : DescentContactPreROM.Layout} (eqn : C=A) (bundle : Banks C)
theorem move_key (j : Fin A.donors) :
    (move eqn bundle).keys j=bundle.keys (j.cast (congrArg DescentContactPreROM.Layout.donors eqn.symm)) := by
  subst A;rfl

theorem move_actor : (move eqn bundle).actorStarts=bundle.actorStarts ∧
    (move eqn bundle).actorData=bundle.actorData := by
  subst A;exact ⟨rfl,rfl⟩
open DescentDatedAddressBook DescentResetStemKey DescentResetLocalRoster ProtocolRAM
private theorem original_keys (v : CandidateFront) (floor : ℕ) {target : DescentContactPreROM.Layout}
    (eqn : v.contactLayout floor = target)
    (pages : Bool→Root (v.contactLayout floor).residual (2^(v.contactLayout floor).n)→Bank)
    (starts dat : Bank) :
    (move eqn (v.originalPages floor pages starts dat)).keys =
      fun j=>Columns.bank floor v.peer.oldDegree v.stemField v.oldLanes v.peer.oldHosts v.oldGroups j.val := by
  funext j
  rw [move_key]
  rfl

end
end Hierarchy.DescentResetPeerUnionRAM.PeerCatalog

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentDatedAddressBook CandidateFront DescentCompiler DescentColonies DescentDenseHostOrder
open DescentResetPeerUnionRAM DescentPackedColony DescentFallbackPeriod DescentSIMDLookup
open DescentGroupPeerOrder DescentPackedZip DescentContactDonorFront DescentResetLocalRoster ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {b : P→ℕ} {W : MarkedWorld F d P b}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl) (oldM nextM field metaBits : ℕ) (calendar : List ℕ)
local notation "A" => setupFront S ctl.board k tail i D f g oldM nextM field metaBits C ctl.bitsR calendar
local notation "H" => S.hostSize i
local notation "Ht" => GroupStage.depthBound D n f g
local notation "cap" => (calendar.take i).prod*256
local notation "r" => B.reset.k-B.terminals.commonDepth
local notation "shelf" => (DescentDenseHostOrder.roster B.reset.graph r Ht).card
local notation "bits" => (A).peer.bits
local notation "donor" => peerDonorShape B H oldM field (Nat.clog 2 (D+2)) (Nat.clog 2 (D+3))
variable (paid : input.placement.cap=cap) (floor : ℕ)
local notation "eqShape" => canonical_donor B oldM nextM field metaBits calendar paid
local notation "next" => (A).oldKeys floor
local notation "L" => peerLayout B next H oldM (A).privateBits ((A).stemField+2) bits
local notation "lo" => (L).endAddress
local notation "start" => (donor).endAddress lo
local notation "CA" => contactLayout B start H oldM field bits
local notation "rowCnt" => 2^B.terminals.commonDepth


local notation "pitch" => H*shelf
local notation "D₀" => input.placement.degree
local notation "srcBase" => (CA).endAddress
local notation "scratch_" => Program.scratchAt srcBase H shelf D₀ (peerEvidenceRows B) bits oldM
local notation "rawAddress" => outBase scratch_ pitch (Candidates.count shelf D₀)


open DescentResetNewActorDirectory DescentResetStemKey
variable (old : EarlierBanks D k cap n)
local notation "incoming" => canonical_peer_inputs B oldM nextM field metaBits calendar paid floor old
local notation "J" => 2^B.terminals.commonDepth
local notation "K" => chunks J oldM
local notation "padded" => (B.frame.host.symm.toEmbedding.trans input.vertex).trans (Fin.castLEEmb input.valid.host)
local notation "bundle" => (A).originalPages floor old.roots old.actorStarts old.actorData
local notation "contactEq" => canonical_contact_layout B oldM nextM field metaBits calendar paid floor
variable (directory : ℕ)
local notation "dir" => (⟨directory,H,shelf,K⟩ : DescentResetNewActorDirectory.Layout)
local notation "width" => (A).privateBits
local notation "oldStop" => Columns.stop (dir).endAddress D₀ field oldM H J (stemsCount B)

include paid in
theorem canonical_key_stop (placement : floor=(dir).endAddress) :
    (A).oldKeys floor=oldStop := by
  change Columns.stop floor D field oldM H (2^(S.groupWidth k tail i)) (A).oldKeysCount=_
  rw [placement,input.branch,B.commonDepth,(canonical_probes B oldM nextM field metaBits calendar paid).2.1]

private theorem peer_inputs_eq
    {key₁ key₂ : Fin (stemsCount B)→Bank} (pages : Bool→B.reset.RootTicket B.terminals→Bank)
    {start₁ start₂ data₁ data₂ : Bank} (ports : Bank)
    (ks : key₁=key₂) (ss : start₁=start₂) (ds : data₁=data₂) :
    (⟨key₁,pages,start₁,data₁,ports⟩ : PeerInputs B)=⟨key₂,pages,start₂,data₂,ports⟩ := by
  subst key₂; subst start₂; subst data₂
  rfl

theorem canonical_prior_directory (placement : floor=(dir).endAddress) (record : old.actorStarts=(dir).roots) :
    incoming=issuedPeerInputs («H» := H) (f₀:=field) (M:=oldM) B directory old.actorData old.oldRoster
      (incoming).privatePages := by
  let moved := PeerCatalog.move contactEq bundle
  have dims (j : ℕ) :
      Columns.bank floor (A).peer.oldDegree (A).stemField (A).oldLanes (A).peer.oldHosts (A).oldGroups j =
        Columns.bank (dir).endAddress D₀ field oldM H J j := by
    change Columns.bank floor D field oldM H (2^(S.groupWidth k tail i)) j = _
    rw [placement,input.branch,B.commonDepth]
  have fromPages := PeerCatalog.original_keys (A) floor contactEq old.roots old.actorStarts old.actorData
  have ks : moved.keys=(fun j=>Columns.bank (dir).endAddress D₀ field oldM H J j.val) :=
    fromPages.trans (funext (fun j=>dims j.val))
  have common:=PeerCatalog.move_actor contactEq bundle
  have got := peer_inputs_eq B (key₁:=moved.keys)
    (key₂:=fun j=>Columns.bank (dir).endAddress D₀ field oldM H J j.val)
    moved.pages (start₁:=moved.actorStarts) (start₂:=(dir).roots)
    (data₁:=moved.actorData) (data₂:=old.actorData) old.oldRoster
    ks (common.1.trans record) common.2
  unfold canonical_peer_inputs issuedPeerInputs
  dsimp only
  exact got

local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor B.reset.graph).Edge) (2^(Ht+1))

/-- The previous signed key return and the earlier actor and root-packet acquisitions all feed
the one emitted four-family scan at its actual lower address. -/
theorem canonical_old_reads {w : ℕ} (placement : floor=(dir).endAddress)
    (record : old.actorStarts=(dir).roots) (before after : Memory w)
    (values : Bool→B.reset.RootTicket B.terminals→Fin H→Fin J→Cell (width*(capacity*5)))
    (keys : Fin (stemsCount B)→Fin H→Fin J→Cell (field+2))
    (privateFit : ∀s t,((incoming).privatePages s t).Fits w directory ∧ H*K ≤ ((incoming).privatePages s t).size)
    (privateWords : ∀s t,Reads ((incoming).privatePages s t) (values s t) oldM before)
    (sceneFit : old.actorData.Fits w directory) (sceneRoom : pitch*K≤old.actorData.size)
    (scene : ∀(l : Fin shelf) (p : Row H J oldM),before (old.actorData.base+l.val*(H*K)+(row H J oldM p).val)=
      ((data (Recorded.realActor (reset:=B) (shapes B) (rack B input.valid.host) l) p).val:Word w))
    (chunkBound : K≤2^w) (roof : (A).oldKeys floor<2^w)
    (keyWords : ∀(j : Fin (stemsCount B)),Reads (Columns.bank floor D₀ field oldM H J j.val) (keys j) oldM after)
    (lower : ∀j,j<floor→after j=(dir).result old.actorData before j) :
    OldPeerReads B ((A).oldKeys floor) H oldM width (field+2) incoming
      ⟨keys,B.reset.sparseActor B.terminals padded,values⟩ after := by
  have cut:=canonical_key_stop B oldM nextM field metaBits calendar paid floor directory placement
  have bank:=canonical_prior_directory B oldM nextM field metaBits calendar paid floor old directory placement record
  rw [cut,bank]
  apply peer_old_banks B input.valid.host directory old.actorData old.oldRoster (incoming).privatePages before after
    values keys privateFit privateWords sceneFit sceneRoom scene chunkBound (cut ▸ roof)
  · simpa only [←placement] using keyWords
  · simpa only [←placement] using lower

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
