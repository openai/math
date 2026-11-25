import OAI.Hierarchy.DescentNamedResetDateInputs
import OAI.Hierarchy.DescentCalendarSceneIntake
import OAI.Hierarchy.DescentOriginalTrunkHeaderRoom
import OAI.Hierarchy.DescentResetAtlasRoom

namespace OAI
/-! # The actual public reset probes read only allocated original banks -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
  (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree payload : ℕ)
  (e previous M nextM C packet oldLanes primitiveLanes printedBits : ℕ) (venue : StageVenueTail.Date)
  (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "v" => (a).successor
local notation "start" => (a).stageStart floor
local notation "base₀" => (a).rebased start
local notation "cc" => S.groupWidth k tail age
local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "cap" => ((cal).take age).prod*256
local notation "Ht" => GroupStage.depthBound venue.degree n f g
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤laneBits (S.groupWidth k tail age+k) payload (S.localWalshBits p (S.groupWidth k tail age+k) f (quota S.rounds))-k) (fitsSigned : e≤previous) (fitsCut : previous≤S.groupWidth k tail age) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (a).rootPhase sh start count io.hubs g (2^n) roots w
local notation "P" => (a).stencilPhase sh start count io.hubs g (2^n)
local notation "E" => (a).estimator start
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "actorBase" => (v).middle.stop base₀
local notation "early" => (v).actorEnd base₀


open DescentPackedColony DescentFallbackPeriod.Projected DescentPacking.PackedMatch.Local.Stage
local notation "pop" => S.hostSize age
local notation "rows" => pop*chunks (2^cc) (2^e)
local notation "dir" => (v).actor.directory actorBase
local notation "active" => (v).actor.scene actorBase
local notation "src" => atlasSender atlas sh start count io.hubs g (2^n) roots w
local notation "raw" => CandidateFront.EarlierBanks.fromRoot rc book src (atlas).hostIndex io.hubs dir active
local notation "rfield" => ResetMiddle.fieldWidth venue.degree cap n k Ht
local notation "F₀" => (v).front
local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "scene" => (v).issuedScene base₀ older
local notation "peers" => (F₀).peers early
local notation "stop" => (F₀).peer.endAddress peers

/-- Static source bounds for the first four physical scans. All root banks are those
in the actual `namedOriginals`; the arithmetic mask bounds hold before any selector is read. -/
theorem named_scene_inputs (stencil : (P).Room w)
    (geometry : (src).OperandRoom pop (2^cc) (2^e) w ((rc).headerEnd book))
    (laid : (rc).preparedEnd book ≤ early) (small : 4 < 2^w)
    (hosts : pop < 2^w) (degrees : venue.degree+1 < 2^w)
    (packed : 2^e*max (rfield*8) (F₀).peer.bits ≤ w/2) (endRoom : stop < 2^w) :
    (∀q j,((scene).evidence.source q j).Fits w early) ∧
    (F₀).donor.Space ((F₀).donorStart early) (scene).donor w ∧
    ((F₀).contactLayout early).Space (scene).boardReads ((F₀).sensor early scene) w ∧
    (F₀).peer.Room (scene).peers peers w := by
  have half : (a).c/2=cap:=by change (2*cap)/2=cap;omega
  let registered:=((congrArg (fun t=>CandidateFront.EarlierBanks venue.degree k t n) half).mp raw)
  obtain ⟨p₁,p₂,p₃,p₄⟩:=(F₀).peer.ordered peers
  have topPeer : peers < 2^w:=(p₁.trans (p₂.trans (p₃.trans p₄))).trans_lt endRoom
  obtain ⟨a₁,a₂,a₃,a₄,a₅⟩:=((F₀).contactLayout early).ordered
  obtain ⟨d₁,d₂,d₃⟩:=(F₀).donor.ordered ((F₀).donorStart early)
  have sceneEnd : (F₀).rawTablesEnd early < 2^w:=
    (d₁.trans (d₂.trans (d₃.trans (a₁.trans (a₂.trans (a₃.trans (a₄.trans a₅))))))).trans_lt topPeer
  have rawStart : early ≤ (F₀).oldKeys early:=by
    dsimp [CandidateFront.oldKeys,DescentResetStemKey.Columns.stop,DescentResetStemKey.Columns.start]
    omega
  have capEnd : early < 2^w:=by
    have layout:=((F₀).rawTables early).end_eq
    have same:=(F₀).tables_end early rfl
    exact (rawStart.trans (show (F₀).oldKeys early ≤ (F₀).rawTablesEnd early by
      rw [←same,layout];exact Nat.le_add_right ..)).trans_lt sceneEnd
  have idFit : (atlas).hostIndex.Fits w (rc).origin:=by
    have banks:=((P).S.banks (P).X (P).base (P).bank stencil.operands).1
    exact ⟨banks.1,banks.2.1,banks.2.2.trans ((P).S.header_before_output (P).base)⟩
  have actorArea : (active).Fits w early:=by
    have size : (active).base+(active).size ≤ early:=Nat.le_add_right ((v).actor.endAddress actorBase) _
    exact ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (size.trans_lt capEnd),size⟩
  have lawful : (raw).Bounds pop (2^cc) (2^e) w early :=
    CandidateFront.EarlierBanks.from_root_bounds rc book src (atlas).hostIndex io.hubs dir active
      geometry (fun _=>rfl) (fun _ _=>Nat.le_pow_clog (by decide) _) idFit laid actorArea capEnd
  have reranked : registered.Bounds pop (2^cc) (2^e) w early:=
    CandidateFront.EarlierBanks.transfer_bounds raw half lawful
  exact CandidateFront.calendar_scene_inputs S board k tail age venue.degree f g (2^e) M rfield (F₀).metaBits
    C packet cal early registered (dir).flags (dir).count (dir).inverse reranked small hosts degrees packed endRoom

/-- Assemble all eleven public bounds of the scene. The stem check consumes the
same source certificate obtained here from the actual root and sender tables. -/
theorem named_scene_room (stencil : (P).Room w)
    (geometry : (src).OperandRoom pop (2^cc) (2^e) w ((rc).headerEnd book))
    (laid : (rc).preparedEnd book ≤ early) (small : 4 < 2^w)
    (hosts : pop < 2^w) (degrees : venue.degree+1 < 2^w)
    (packed : 2^e*max (rfield*8) (F₀).peer.bits ≤ w/2)
    (extent : (F₀).mixed early < 2^w)
    (stem : (∀q j,((scene).evidence.source q j).Fits w early) →
      (F₀).StemRoom (scene).stems early w) : (F₀).SceneRoom early scene w := by
  have parent : (F₀).parentStart early < 2^w:=((F₀).front_order early).1.trans_lt
    (((F₀).front_order early).2.1.trans_lt extent)
  have top : stop < 2^w:=(Nat.le_add_right ..).trans_lt parent
  obtain ⟨probe,donor,contact,full⟩:=named_scene_inputs G S board k tail age p f g drift degree payload e previous M nextM
    C packet oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
    stencil geometry laid small hosts degrees packed top
  obtain ⟨p₁,p₂,p₃,p₄⟩:=(F₀).peer.ordered peers
  obtain ⟨a₁,a₂,a₃,a₄,a₅⟩:=((F₀).contactLayout early).ordered
  obtain ⟨d₁,d₂,d₃⟩:=(F₀).donor.ordered ((F₀).donorStart early)
  have key : early ≤ (F₀).oldKeys early:=by
    dsimp [CandidateFront.oldKeys,DescentResetStemKey.Columns.stop,DescentResetStemKey.Columns.start]
    omega
  have rawBound : (F₀).oldKeys early ≤ (F₀).rawTablesEnd early:=by
    rw [←(F₀).tables_end early rfl,((F₀).rawTables early).end_eq]
    exact Nat.le_add_right ..
  have endRaw : (F₀).rawTablesEnd early ≤ stop :=
    d₁.trans (d₂.trans (d₃.trans (a₁.trans (a₂.trans (a₃.trans (a₄.trans (a₅.trans
      (p₁.trans (p₂.trans (p₃.trans p₄))))))))))
  have edge : early ≤ stop:=key.trans (rawBound.trans endRaw)
  have slots:=(dir).fits (edge.trans_lt top)
  exact ⟨probe,rfl,endRaw.trans_lt top,donor,contact,full,
    Chooser.bank_before slots.2.2.2.1 edge,Chooser.bank_before slots.2.2.2.2 edge,
    (F₀).original_scalar early older (dir).flags (dir).count (dir).inverse parent,parent,stem probe⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
