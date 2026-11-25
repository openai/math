import OAI.Hierarchy.DescentPhysicalResetDateOperands
import OAI.Hierarchy.DescentOperandSourcesBeforePacket

namespace OAI
/-! # The dated reset up to the first operand-packet gather -/
namespace Hierarchy.DescentDatedAddressBook
open DescentSIMDLookup DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open DescentResetOperandSetup DescentResetFieldAssembler DescentResetCandidatePair
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 4096
attribute [local irreducible] ProtocolRAM.CheapCode

namespace ResetOutput
variable (v : ResetOutput)
local notation "A" => v.receiver
section Ranked
variable (u : v.RankInputs) (base degree : ℕ)
local notation "L" => v.rankBook u base
local notation "r₀" => v.renderFromRanks u base
variable (bank : v.setup.Sources)
local notation "source₀" w => v.setup.sources (v.operandFloor base) w bank

/-- The original rank-port installation, rank and control scans, and final operations ending with placement of the signed input sheets. -/
def ranksToPacket (w : ℕ) : Code w :=
  ⟨(v.rankPortPhase base w).program.seq (((L).program w).seq ((v.renderProgram r₀ base degree w).seq
     ((v.controlPhase base bank w).program.seq (source₀ w).program))),
   (v.rankPortPhase base w).ticks+((L).time+(v.renderTicks r₀ base degree+((v.controlPhase base bank w).ticks+(source₀ w).time))),
   fun m=>(source₀ w).image ((v.controlPhase base bank w).image
     (v.renderMemory r₀ base degree ((L).memory ((v.rankPortPhase base w).image m))))⟩

theorem ranks_to_packet {w : ℕ} (m : Memory w) (width : (A).signedBits=v.assemblerBits)
    (ports : v.RankPortRoom base w) (reads : (L).Previous w) (controls : v.ControlRoom base bank w)
    (placed : v.setup.Ready bank w (v.operandFloor base)) (room : v.endAddress base < 2^w) :
    Code.Runs (v.ranksToPacket u base degree bank w) (v.candidateEnd base)
      (v.setup.placed (v.operandFloor base)) m := by
  let low:=v.rankEnd base
  let mid:=(A).rendered (v.fieldsEnd base)
  have room₀: low≤ mid:=by
    change v.rankEnd base≤DescentNextSignedWindow.Native.All.endAddress (v.fieldsEnd base) _ _ _ _ _ _
    unfold fieldsEnd DescentResetFieldAssembler.endAddress DescentNextSignedWindow.Native.All.endAddress
    omega
  have start : mid≤v.operandFloor base := by
    change mid≤v.controlRegisters.endAddress mid
    rw [v.controlRegisters.translated mid]
    exact Nat.le_add_right ..
  have beforeSetup : v.operandFloor base≤v.operandStart base := by
    refine le_trans ?_ (v.keep_before base)
    change v.operandFloor base≤v.setup.endAddress (v.operandFloor base)
    rw [v.setup.affine]
    exact Nat.le_add_right ..
  obtain ⟨afterSetup,afterLookup⟩:=v.operand_order base
  have endFits : v.operandFloor base≤v.endAddress base := beforeSetup.trans (afterSetup.trans afterLookup)
  have room₁ := start.trans endFits
  have rfit : (L).endAddress<2^w:=(room₀.trans room₁).trans_lt room
  have rankStart : v.rankPortEnd base≤low:=by
    obtain ⟨a,b,c,d⟩:=(L).ordered
    exact ((a.trans b).trans c).trans d
  obtain ⟨portRun,portFrame⟩:=v.rankPort_any base w m ports
  let portMemory:=(v.rankPortPhase base w).image m
  have lstage:=(L).any portMemory reads rfit
  have fit₀ : ∀x j,(u.header x j).Fits w (v.rankEnd base) := by
    intro x j
    obtain ⟨h,i,k,o⟩:=(L).ordered
    exact ProtocolRAMGeneratedWrite.fits_mono _ (((h.trans i).trans k).trans o) (reads.header x j)
  have middle:=v.render_any r₀ base degree ((L).memory portMemory) width fit₀ ((L).finalRank_fits reads rfit) (room₁.trans_lt room)
  let rendered:=v.renderMemory r₀ base degree ((L).memory portMemory)
  let registers:=v.controlPhase base bank w
  obtain ⟨regRun,regFrame⟩:=v.controlRegisters.any (v.controlFloor base) (v.actor.scene (v.middle.stop base))
    bank.count bank.inverse rendered controls (endFits.trans_lt room)
  let floor := v.operandFloor base
  have sourceStart : floor ≤ v.setup.placed floor := by
    obtain ⟨a,b,c⟩ := v.setup.before floor
    exact (a.trans b).trans c
  have sourceCap : v.setup.placed floor ≤ v.operandStart base := by
    have pair := v.setup.packets.join (v.setup.placed floor)
    have toPair : v.setup.placed floor ≤ v.setup.packetEnd floor := pair.1.trans pair.2
    have toPublic : v.setup.packetEnd floor ≤ v.setup.publicEnd floor := Nat.le_add_right ..
    obtain ⟨d,e,f,g,h,i,j,k⟩ := v.setup.order floor
    apply le_trans _ (v.keep_before base)
    change v.setup.placed floor ≤ v.setup.endAddress floor
    omega
  have last := v.setup.sources_run floor (registers.image rendered) bank placed
    ((sourceCap.trans (afterSetup.trans afterLookup)).trans_lt room)
  refine ⟨?_,cheap_seq (v.rankPortPhase base w).cheap
    (cheap_seq lstage.2.2 (cheap_seq middle.2.2 (cheap_seq registers.cheap last.cheap))),?_⟩
  · intro P R registers mach
    exact Procedure.Exec.then portRun (Procedure.Exec.then lstage.1 (Procedure.Exec.then middle.1
      (Procedure.Exec.then regRun last.exec))) mach
  intro addr outside
  have first := (v.rankPort_after base).trans rankStart
  rcases outside with lower|upper
  · have atControl : addr < mid := lower.trans_le (first.trans room₀)
    exact (last.frame addr (.inl (atControl.trans_le start))).trans
      ((regFrame addr (.inl atControl)).trans
        ((middle.2.1 addr (.inl (lower.trans_le first))).trans
          ((lstage.2.1 addr (.inl (lower.trans_le (v.rankPort_after base)))).trans (portFrame addr (.inl lower)))))
  · have after : floor ≤ addr := sourceStart.trans upper
    have postRank : low ≤ addr := (room₀.trans start).trans after
    exact (last.frame addr (.inr upper)).trans
      ((regFrame addr (.inr after)).trans ((middle.2.1 addr (.inr (start.trans after))).trans
        ((lstage.2.1 addr (.inr postRank)).trans (portFrame addr (.inr (rankStart.trans postRank))))))

include u in
theorem candidates_le_packet : v.candidateEnd base ≤ v.setup.placed (v.operandFloor base) := by
  have rk := (L).ordered
  obtain ⟨a,b,c⟩ := v.setup.before (v.operandFloor base)
  have ra : v.candidateEnd base ≤ v.rankEnd base := (v.rankPort_after base).trans (((rk.1.trans rk.2.1).trans rk.2.2.1).trans rk.2.2.2)
  have rf : v.rankEnd base ≤ v.controlFloor base := by
    change v.rankEnd base ≤ DescentNextSignedWindow.Native.All.endAddress (v.fieldsEnd base) _ _ _ _ _ _
    unfold fieldsEnd DescentResetFieldAssembler.endAddress DescentNextSignedWindow.Native.All.endAddress
    omega
  have rc : v.controlFloor base ≤ v.operandFloor base := by
    change v.controlFloor base ≤ v.controlRegisters.endAddress (v.controlFloor base)
    rw [v.controlRegisters.translated];exact Nat.le_add_right ..
  exact ((((ra.trans rf).trans rc).trans a).trans b).trans c
end Ranked

section Sheets
variable (q : v.Sectors) (start : ℕ)
local notation "X" => (A).blocks
local notation "K" => CandidateSheet.size q.stems q.contacts q.privates
local notation "B" => q.pageBits
variable (base degree : ℕ)
local notation "q₀" => v.linkedRankInputs q start
local notation "L" => v.rankBook q₀ base
local notation "r₀" => v.renderFromRanks q₀ base
local notation "stop₀" => DescentResetCandidatePair.endAddress start X K B
variable (bank : v.setup.Sources)

/-- The original paired-candidate table followed by the rank and operand-source phases. -/
def sheetsToPacket (w : ℕ) : Code w :=
  let pair : Code w :=
    ⟨DescentResetCandidatePair.program start B (A).hosts (A).groups (A).lanes w q.header q.original,
     DescentResetCandidatePair.time start B (A).hosts (A).groups (A).lanes q.header q.original,
     DescentResetCandidatePair.memory start B (A).hosts (A).groups (A).lanes q.header q.original⟩
  pair.join (v.ranksToPacket q₀ base degree bank w)

theorem sheets_to_packet {w : ℕ} (m : Memory w) (matched : stop₀=v.candidateEnd base)
    (room : v.finalEnd base < 2^w) (fitH : ∀ x j,(q.header x j).Fits w start)
    (fitO : ∀ x j,(q.original x j).Fits w start) (r : (A).hosts*chunks (A).groups (A).lanes ≤ 2^B)
    (width : (A).signedBits=v.assemblerBits) (ports : v.RankPortRoom base w) (prev : (L).Previous w)
    (controls : v.ControlRoom base bank w) (placed : v.setup.Ready bank w (v.operandFloor base)) :
    Code.Runs (v.sheetsToPacket q start base degree bank w) start
      (v.setup.placed (v.operandFloor base)) m := by
  have lo:start≤v.candidateEnd base:=by rw [←matched]; exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have rk:=(L).ordered
  have bound:v.candidateEnd base≤v.finalEnd base:=(v.rankPort_after base).trans <| (((rk.1.trans rk.2.1).trans rk.2.2.1).trans rk.2.2.2).trans
    ((v.earlier base).2.2.trans (v.final_ge base))
  have hs:=DescentResetCandidatePair.any start B (A).hosts (A).groups (A).lanes q.header q.original m fitH fitO r
    (by simpa only [matched] using bound.trans_lt room)
  let after:=DescentResetCandidatePair.memory start B (A).hosts (A).groups (A).lanes q.header q.original m
  have carried := v.ranks_to_packet q₀ base degree bank after width ports prev controls placed
    ((v.final_ge base).trans_lt room)
  have «until» := v.candidates_le_packet q₀ base
  refine ⟨?_,cheap_seq hs.2.2 carried.cheap,?_⟩
  · intro P R registers mach
    exact Procedure.Exec.then hs.1 carried.exec mach
  intro i outside
  rcases outside with h|h
  · exact (carried.frame i (.inl (h.trans_le lo))).trans (hs.2.1 i (.inl h))
  · exact (carried.frame i (.inr h)).trans (hs.2.1 i (.inr (by simpa only [matched] using «until».trans h)))
end Sheets
end ResetOutput

namespace PhysicalReset.DateInputs
open DescentSixParty DescentSixParty.Chronology DescentFallbackPeriod DescentResetFieldAssembler
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "s" => (v).sheets
local notation "rbase" => ((v).remap b).endAddress
local notation "root" => a.rootPhase u.shape floor u.count u.hub u.g u.Y u.roots w
local notation "actorBase" => (v).middle.stop b
local notation "head" => a.throughPublishedRoots u.shape floor u.count u.hub u.g u.Y u.roots u.book u.src u.sourceRows u.oldDegree w u.bookFits
local notation "ht" => a.throughPublishedTicks u.shape floor u.count u.hub u.g u.Y u.roots u.book u.sourceRows u.oldDegree w u.bookFits
local notation "actors" => (v).actor.actorBody u.actor actorBase w
local notation "atime" => (v).actor.actorTicks u.actor actorBase w
local notation "scene" => (v).front.trunkScene ((v).actorEnd b) ((v).issuedScene b u.earlier) u.sceneFits
local notation "S₀" => (v).sheetsStart b

local notation "front₀" => (v).front
local notation "peer₀" => (front₀).peer
local notation "cut₀" => (v).actorEnd b
local notation "old₀" => (v).issuedScene b u.earlier
local notation "donor₀" => (front₀).donorStart cut₀
local notation "mass₀" => (v).trunkEnd b
local notation "join₀" => (v).massEnd b

local notation "jointPhase" => (v).jointPhase b u.earlier w
local notation "massPhase" => (v).contactShape.issuedProgram donor₀ mass₀ (old₀).donor w
local notation "mticks" => (v).contactShape.issuedTicks donor₀ mass₀ (old₀).donor

local notation "pr₀" => (v).privateShape
local notation "oldPitch" => (front₀).contactLayout cut₀
local notation "pcode" => (pr₀).code ((v).jointEnd b) oldPitch u.earlier.pages w
local notation "pclock" => (pr₀).ticks ((v).jointEnd b) oldPitch u.earlier.pages

local notation "num" => u.numbered.code rbase w
local notation "tail₀" => (v).sheetsToPacket u.sectors S₀ b u.degree u.bank w

/-- Literal program prefix terminating immediately before packet gathering. -/
def beforePacket : Procedure w :=
  (((((head).seq actors).seq (scene).program).seq massPhase).seq (jointPhase).program).seq
    ((((pcode).seq (u.masked.code w)).seq num).seq (tail₀).program)

def beforePacketTicks : ℕ :=
  ((((ht+atime)+(scene).ticks)+mticks)+(jointPhase).ticks)+
    (((pclock+u.masked.ticks)+u.numbered.time rbase)+(tail₀).time)

def beforePacketImage (ok : u.Ready) (atActors : Memory w) : Memory w :=
  (tail₀).image (u.sheetsEntry ok atActors)

/-- Starting at the packet rows, the original program installs packet and control
dictionaries, evaluates the operands, and emits the node books. -/
def afterPacketImage (input : Memory w) : Memory w :=
  let sourceFloor := (v).operandFloor b
  let packets := ((v).setup.packetBook sourceFloor w).image input
  let casts := ((v).setup.publicBook sourceFloor w).image packets
  let control := ((v).setup.control sourceFloor w u.laws).image casts
  let kept := ((v).keepBook b w).image control
  let render := (v).renderFromRanks ((v).linkedRankInputs u.sectors S₀) b
  DescentResetNodeBooks.image ((v).scalarEnd b) ((v).operandDictionaryEnd b) (v).nodeNames
    (v).nodes (v).receiver.hosts (v).receiver.groups (v).nodeBits (v).receiver.lanes
    ((v).operandMemory u.operand render b kept)

/-- The memory received by the measured gather is the intermediate memory of
the original full operand computation on this actor image. -/
theorem sheets_result_from_before_packet (ok : u.Ready) (atActors : Memory w) :
    u.sheetsResult ok atActors=u.afterPacketImage (u.beforePacketImage ok atActors) := rfl

theorem sheets_le_packet (ok : u.Ready) : S₀ ≤ (v).setup.placed ((v).operandFloor b) := by
  have before : S₀ ≤ (v).candidateEnd b := by
    rw [←ok.matched]
    exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  exact before.trans ((v).candidates_le_packet ((v).linkedRankInputs u.sectors S₀) b)

private theorem packet_after_scene (ok : u.Ready) (atActors : Memory w) :
    (∀ {m : Memory w}, ((head).seq actors).Exec m atActors (ht+atime) →
      CheapCode ((head).seq actors) →
      u.beforePacket.Exec m (u.beforePacketImage ok atActors) u.beforePacketTicks ∧ CheapCode u.beforePacket) ∧
    ∀z,z < (v).trunkEnd b ∨ (v).setup.placed ((v).operandFloor b) ≤ z →
      u.beforePacketImage ok atActors z=(scene).image atActors z := by
  obtain ⟨t₃,h₃⟩:=(v).front.trunkScene_any ((v).actorEnd b) ((v).issuedScene b u.earlier) u.sceneFits atActors ok.trunk
  let m₃:=(scene).image atActors
  obtain ⟨massRun,massCheap,massFrame⟩:=(v).contactShape.actual donor₀ mass₀
    (old₀).donor u.sceneFits.donor ok.donors ok.mass ok.projectionLanes ok.projectionBlocks m₃
  let massOut:=(v).contactShape.issuedImage donor₀ mass₀ (old₀).donor m₃
  obtain ⟨joinRun,joinFrame⟩:=(v).joint_any b u.earlier massOut ok.joints ok.packed
  let mid:=(jointPhase).image massOut
  have privateFits:=(v).private_inputs_fit b u.earlier ok.pages ok.privates
  let post:=(v).privatePhase b u.earlier ok.projectionLanes ok.projectionBlocks privateFits ok.privates
  obtain ⟨pRun,pKeep⟩:=(v).private_any b u.earlier mid ok.projectionLanes ok.projectionBlocks privateFits ok.privates
  obtain ⟨t₄,c₄,h₄⟩:=u.masked.any (post.image mid) (u.genuine_mask_previous ok.joints ok.masked) ok.masked
  obtain ⟨t₅,c₅,h₅⟩:=u.numbered.any rbase (u.masked.image (post.image mid)) ok.numbers
  have last := (v).sheets_to_packet u.sectors S₀ b u.degree u.bank (u.sheetsEntry ok atActors)
    ok.matched ok.full ok.header ok.original ok.rows ok.width ok.rankPorts ok.ranks ok.controls ok.placed
  constructor
  · intro m toActors cheap
    refine ⟨?_,cheap_seq (cheap_seq (cheap_seq (cheap_seq cheap (scene).cheap) massCheap) (jointPhase).cheap)
        (cheap_seq (cheap_seq (cheap_seq post.cheap c₄) c₅) last.cheap)⟩
    intro P R registers mach
    exact Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then
      (Procedure.Exec.then toActors t₃) massRun) joinRun) (Procedure.Exec.then (Procedure.Exec.then
      (Procedure.Exec.then pRun t₄) t₅) last.exec) mach
  obtain ⟨a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉⟩ := ok.ordered
  have mEnd:=u.masks_end
  have roof := u.sheets_le_packet ok
  intro z hz
  exact (last.frame z (by omega)).trans ((h₅ z (by change z<(s).metaEnd rbase ∨ S₀≤z;omega)).trans
    ((h₄ z (by change z<(v).privateEnd b ∨ u.masked.endAddress≤z;omega)).trans
    ((pKeep z (by omega)).trans
    ((joinFrame z (by omega)).trans
    (massFrame z (by change z < (v).trunkEnd b ∨ (v).massEnd b ≤ z;omega))))))

/-- The parent directory emitted by the trunk scene remains available to the gather. -/
theorem before_packet_scene (ok : u.Ready) (atActors : Memory w) :
    ∀z,z < (v).trunkEnd b ∨ (v).setup.placed ((v).operandFloor b) ≤ z →
      u.beforePacketImage ok atActors z=(scene).image atActors z :=
  (u.packet_after_scene ok atActors).2

theorem before_packet_from_actors (ok : u.Ready) {m atActors : Memory w}
    (toActors : ((head).seq actors).Exec m atActors (ht+atime))
    (cheap : CheapCode ((head).seq actors)) :
    u.beforePacket.Exec m (u.beforePacketImage ok atActors) u.beforePacketTicks ∧
    CheapCode u.beforePacket ∧ ∀z,z < (v).actorEnd b ∨ (v).setup.placed ((v).operandFloor b) ≤ z →
      u.beforePacketImage ok atActors z=atActors z := by
  obtain ⟨exec,kept⟩ := u.packet_after_scene ok atActors
  obtain ⟨run,cheap'⟩ := exec toActors cheap
  obtain ⟨_,sceneFrame⟩ := (v).front.trunkScene_any ((v).actorEnd b)
    ((v).issuedScene b u.earlier) u.sceneFits atActors ok.trunk
  refine ⟨run,cheap',?_⟩
  obtain ⟨o₁,o₂,o₃,o₄,o₅,o₆,o₇,o₈,o₉⟩ := ok.ordered
  have top := u.sheets_le_packet ok
  intro z hz
  exact (kept z (by omega)).trans (sceneFrame z (by change z < (v).actorEnd b ∨ (v).trunkEnd b ≤ z;omega))

/-- The original prepared input memory and the actor's true directory both survive
up to the physical packet gather. The witness is the actual actor publication. -/
theorem before_packet_from_roots (ok : u.Ready) {m afterRoots : Memory w}
    (ran : (head).Exec m afterRoots ht) :
    ∃ atActors : Memory w, (actors).Exec afterRoots atActors atime ∧
      u.beforePacket.Exec m (u.beforePacketImage ok atActors) u.beforePacketTicks ∧
      CheapCode u.beforePacket ∧
      (∀z,z < (v).actorEnd b ∨ (v).setup.placed ((v).operandFloor b) ≤ z →
        u.beforePacketImage ok atActors z=atActors z) ∧
      ∀z,z < (root).preparedEnd u.book ∨ (v).setup.placed ((v).operandFloor b) ≤ z →
        u.beforePacketImage ok atActors z=afterRoots z := by
  obtain ⟨_,_,cheap,_⟩ := a.throughPublishedRoots_any_framed u.shape floor u.count u.hub u.g u.Y
    u.roots u.book u.src u.sourceRows u.oldDegree w u.bookFits m ok.prime ok.stencil
  obtain ⟨atActors,act,price,frame⟩ := (v).actor.dated_any u.actor actorBase afterRoots ok.actor
  have both : ((head).seq actors).Exec m atActors (ht+atime) := by
    intro P R registers mach
    exact Procedure.Exec.then ran act mach
  obtain ⟨run,small,actorFrame⟩ := u.before_packet_from_actors ok both (cheap_seq cheap price)
  refine ⟨atActors,act,run,small,actorFrame,?_⟩
  obtain ⟨o₁,o₂,o₃,o₄,o₅,o₆,o₇,o₈,o₉⟩ := ok.ordered
  have hi := u.sheets_le_packet ok
  intro z outside
  rw [ok.rootEnd] at outside
  have early := ok.ordered.2.1
  exact (actorFrame z (by omega)).trans (frame z (by change z < actorBase ∨ (v).actorEnd b ≤ z;omega))

end PhysicalReset.DateInputs
end
end Hierarchy.DescentDatedAddressBook

end OAI
