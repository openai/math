import OAI.Hierarchy.DescentTerminalFundedReadback
import OAI.Hierarchy.DescentCompleteBootReel
import OAI.Hierarchy.DescentDatedSeedCheapBoot
import OAI.Hierarchy.DescentNamedPostEarlyPreflight

namespace OAI
/-! # The funded dated machine and its true observations at the last native preflight -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch DescentKernelHistory DescentGL DescentColonies DescentExterior
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p : ℕ}
attribute [local irreducible] Origin.source
set_option quotPrecheck false
variable {he : 0 ≤ ((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower}
    {hu : 0 ≤ 1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower ^ S.priceExponent : ℝ)) *
      (S.epochPower ^ S.priceExponent : ℝ)}
    {radix : S.radix = 2 ^ k} {R : ℕ}
    {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
      (t := S.rounds) S.height
      (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S radix R r c) (hp : 0<p)

namespace Branch
open DescentDatedSeedStartup DescentDatedSeedStartup.Input DescentSeedRoot DescentSeedInitialTable DescentPackedSeed DescentRotor DescentInitialHost
open PinCohorts DescentExteriorMatrixUpdate DescentExteriorShelf
variable {tail j rest : ℕ} (base : S.baseGroups=2^tail)
local notation "initialBits" => S.groupWidth k tail 0+k
local notation "shape" => j+(j+rest)
local notation "E" => Fintype.card (Port P X.width)
variable (width : S.groupWidth k tail 0+k=j+(j+rest))

variable {t : ℕ} (roof : ℕ) (tag : ℕ→Bool) (rotation : ℕ→ℕ)
local notation "end_" => Calendar.stop S k tail roof
local notation "early" => Calendar.earlyAt S k tail roof
local notation "reel" => Calendar.reel S k tail roof tag rotation
local notation "H" => span j rest t E

open Chronology DescentTerminalEpochDecoder
local notation "tags" => kindCalendar S.rounds S.height
local notation "dates" => countDates 0 tags
variable (loc : ℕ→ℕ) (lo compact : ℕ)
local notation "source" => (fun (j:ℕ)=>loc ((dates)[j]?.getD 0))

variable (op : RotorSpec) {hosts : ℕ} (wide : Fintype.card b.origin.raw.V≤hosts)
    (pub : Fintype.card (Vertex X)≤hosts) (l : DescentDatedSeedStartup.Layout) (header payload Z : ℕ)
local notation "ds" => S.initialDigits radix
local notation "ch" => DescentDatedSeedStartup.Input.nodeChart l k hosts (S.groupCount 0)
local notation "seedEnd" => (ch).seedEnd (DescentDatedSeedStartup.endAddress X l hosts (S.groupCount 0) k)
local notation "pitch" => DescentDatedSeedStartup.Primitive.paletteLanes G op l.seedWidth Z payload k
local notation "jobs" => DescentPackedSeed.Primitive.Source.jobs X S.copies l.seedWidth payload
local notation "bound" => DescentDatedSeedStartup.Primitive.initialEnd X S.copies l.seedWidth payload k hosts (S.groupCount 0) pitch seedEnd
local notation "boot" => completeAfter G op X ds pub l header payload Z
local notation "ticks" => completeTicks (S:=S) (k:=k) G op X pub l payload Z
local notation "startedAt" => completeImage G op X ds pub l header payload Z
open DescentMixedRouter DescentExteriorReplay
open DescentTerminalPreflightSpace DescentTerminalFixedSlices DescentTerminalPrimitiveArena
open DescentTerminalPointerDigits DescentTerminalCombinedRole DescentSIMDLookup
variable {w:ℕ} (teams drift headerRows paidRows:ℕ) (phase:Phase F) (snapshots:Snapshots k)
local notation "spec" => preflightSpec X G S k g p tail (geometryFormat G S k g p tail teams drift op headerRows paidRows)
local notation "batchCal" => replayCalendar X S k tail j rest snapshots
local notation "early_" => DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail roof j rest t E
local notation "slices_" => phase.stop early_
local notation "rom_" => (batchCal).packetEnd slices_
local notation "shelf" => (spec).scanPages rom_ teams
local notation "census_" => (shelf).stop
local notation "matrix" => DescentExteriorMatrixUpdate.Calendar.stop S k tail roof+S.length
local notation "bks" => (spec).scalar.blocks
local notation "places" => (spec).scalar.shops
local notation "hw_" => phase.output.receiver
variable (blocks:2^k=phase.output.receiver.blocks) (shops:S.hostSize S.length=phase.output.receiver.hosts) (roleBase:ℕ)
  (peer:Bank) (paid actor:Fin (2^k)→Bank) (signedBanks:Fin (2^k)→Fin (2*((capCalendar G.b S.rounds g S.height).prod*256))→Bank)
local notation "ptr" => fun (f:Fin 4) (j:Fin phase.output.argumentSlots) (b:Fin bks) =>
  phase.output.terminalPointers phase.dateBase f j (b.cast blocks)
variable (cohortRoom :
  let book := replayCalendar X S k tail j rest snapshots
  let endAddress := Calendar.earlyEnd S k tail roof j rest t (Fintype.card (Port P X.width))
  let layout := preflightSpec X G S k g p tail (geometryFormat G S k g p tail teams drift op headerRows paidRows)
  book.stop (layout.scanPages (book.packetEnd (phase.stop endAddress)) teams).stop < 2^w)
local notation "out_" => postEarlyPreflightMemory X G S base radix g p teams drift op headerRows paidRows j rest t
  roof phase snapshots blocks roleBase peer paid actor signedBanks cohortRoom
local notation "code_" => postEarlyPreflight X G S base radix g p teams drift op headerRows paidRows j rest t
  roof phase snapshots blocks roleBase peer paid actor signedBanks cohortRoom
local notation "clock_" => postEarlyPreflightClocks X G S (k:=k) (tail:=tail) g p teams drift op headerRows paidRows j rest t
  roof phase snapshots blocks peer paid actor signedBanks cohortRoom

local notation "s₀" => S.firstWidth G.b p
local notation "colors" => DescentPrimitivePalette.colors G s₀ (S.grainAt G.b p 0) op
local notation "maxArgs" => NativeBranch.privateSlotCapacity G S drift
local notation "roleBits" => fun f:Fin 6 => DescentTerminalCombinedRole.width colors (max 8 (2^S.capGain))
  maxArgs p drift f*(S.epochPower^S.localTokenExponent)*(spec).groups
include hp width wide shops in
theorem original_funded_source
    (geometryRoom:(spec).maskBase census_<2^w) (wordPositive:0<w) (alive:0<places)
  (priorMetadata:phase.output.metadataEnd phase.dateBase≤early_) (one:chunks (hw_).groups (hw_).lanes=1)
  (rank:∀t<S.length,∀b,snapshots.compact t=some b→b.Fits w ((batchCal).scratch slices_))
  (roleEnd:roleBase+DescentTerminalRoleTables.count roleBits≤(spec).cohortEnd census_)
  (before:(spec).Before census_ paid actor signedBanks peer (shelf).total (shelf).modulo ((batchCal).homes slices_) (shelf).boundaries)
  (paidRowsFit:∀b,places≤(paid b).size) (signedRows:∀b j,places≤(signedBanks b j).size)
    (date : ℕ→DateCode w) (raw : Memory w)
    (signed : DescentSignedCableCodec.width 3 256*l.packedLanes≤w)
    («fields» : l.operandBits*l.operandLanes≤w) (earlyWord : header<l.base)
    (sourceSpace : DescentPackedSeed.publicWords X+DescentDyadicSpan.span jobs≤ seedEnd)
    (active : 0<pitch) (embed : payload≤w) (space : bound<2^w)
    (total : ∀i< S.length,∀m,∃out,(date i).Runs m out) (limit : ℕ) (accepted : Prop)
    (x : Fin E→Plane j rest→Fin t→Bool) (z : Hidden E j rest t→Bool)
    (printed : Loaded compact (fun _=>LinearEquiv.refl _ _) x z raw)
    (floors : ℕ→ℕ) (original : compact+17*H≤ header)
    (order : ∀i< S.length,header< floors i)
    (observed : b.path.dateReadbacks (DateCode.history date (startedAt raw)) tag rotation loc limit accepted)
    (apartCount : ∀i< S.length,loc i≠header) (apartMatrix : ∀i< S.length,rotation i≠header)
    (keepCount : ∀j< S.length,∀i,S.length≥i→ j< i→loc j< floors i)
    (keepMatrix : ∀j< S.length,∀i,S.length≥i→ j< i→ rotation j< floors i)
    (frame : ∀i< S.length,∀a,a≠header→a< floors i→
      DateCode.history date (startedAt raw) (i+1) a=DateCode.history date (startedAt raw) i a)
    (batchFit : S.batch< 2^w)
    (lowWrite : lo+(dates).length≤ compact) (below : compact+32*H≤ roof)
    (locs : ∀a∈dates,lo+(dates).length≤ loc a ∧ loc a+1< 2^w)
    (rotLo : ∀a< S.length,lo+(dates).length≤ rotation a) (rotHi : ∀a< S.length,rotation a< roof)
    (word : Calendar.earlyEnd S k tail roof j rest t E< 2^w)
    (dateCheap:∀i<S.length,(date i).cheap)
    (seedFlag historyStart extra:ℕ) (seedLeft:seedFlag<lo)
    (captureEnd:lo+(dates).length≤historyStart) (historyLow:historyStart≤compact)
    (archiveEnd:compact+17*H+extra≤header) (reelData:compact+17*H+extra≤roof) :
    let past:=DateCode.history date (startedAt raw) S.length
    let copied:=DescentLowCountBook.output lo source past (dates).length
    let earlyAt_:=Calendar.earlyImage S k tail roof tag rotation j rest t E compact copied
    let finished:=out_ earlyAt_
    (((DateCode.afterBoot (boot w) date S.length).seq
       (historyCountReel X S roof tag rotation loc lo compact k tail j rest t w)).seq code_).Exec raw finished
      ((DateCode.afterTicks (ticks w) date S.length+((4+11*(dates).length)+Calendar.earlyClock S k tail j rest t E))+clock_) ∧
    CheapCode (((DateCode.afterBoot (boot w) date S.length).seq
       (historyCountReel X S roof tag rotation loc lo compact k tail j rest t w)).seq code_) ∧
    finished seedFlag=raw seedFlag ∧
    (∀i,historyStart≤ i→i<compact→finished i=raw i) ∧
    (∀(col:Fin 17)(i:ℕ),i<H→finished ((DescentExteriorShelf.bank j rest t E compact col.val).base+i)=
      raw ((DescentExteriorShelf.bank j rest t E compact col.val).base+i)) ∧
    (∀i,i<extra→finished (compact+17*H+i)=raw (compact+17*H+i)) ∧
    (∀a v,a<limit→b.path.selections[a]?=some v→(finished (lo+a)).val=selectionCount G v) ∧
    (accepted→b.path.savedRotations reel end_ tail finished) ∧ (shelf).Reads finished := by
  intro past copied earlyAt_ finished
  have seeded:=complete_after_count G op X ds pub l header payload Z b.origin wide raw signed «fields» earlyWord
    sourceSpace active embed space
  have issued:=booted_early_prefix X G S b hp base width roof tag rotation loc lo compact op wide pub l
    header payload Z date raw signed «fields» earlyWord sourceSpace active embed space total limit accepted
    x z printed floors original order observed apartCount apartMatrix keepCount keepMatrix frame batchFit
    lowWrite below locs rotLo rotHi word
  have loFits:lo<2^w:=by
    have prior:roof≤early_:=by
      unfold Calendar.earlyEnd Calendar.earlyAt Calendar.stop Calendar.tableAt
      omega
    omega
  have addr (i : ℕ) (hi : i<(dates).length) : source i=(loc (dates)[i]):=by
    simp only [List.getElem?_eq_getElem hi,Option.getD_some]
  have funds:=funded_middle_run X G S base radix g p teams drift op headerRows paidRows
    j rest t roof compact tag rotation phase snapshots blocks shops roleBase peer paid actor signedBanks cohortRoom
    geometryRoom wordPositive alive rotHi below priorMetadata one rank roleEnd before paidRowsFit signedRows
    (boot w) (ticks w) date lo source (dates).length raw (startedAt raw) seeded.1
    (completeAfter_cheap G op X ds pub l header payload Z sourceSpace space embed active) total dateCheap loFits
    (fun i hi => (Nat.add_le_add_left hi.le lo).trans
      ((locs _ (List.getElem_mem hi)).1.trans (addr i hi).symm.le))
    (fun i hi => (Nat.add_le_add_right (addr i hi).le 1).trans_lt (locs _ (List.getElem_mem hi)).2)
  have dateLow (u:ℕ) (lt:u<header):past u=raw u:=by
    have keep (n:ℕ) (hn:n≤S.length):DateCode.history date (startedAt raw) n u=(startedAt raw) u:=by
      induction n with
      | zero=>rfl
      | succ n ih=>
        exact (frame n (by omega) u lt.ne (lt.trans (order n (by omega)))).trans (ih (by omega))
    exact (keep S.length le_rfl).trans (seeded.2.2.2.2 u lt.ne (.inl (lt.trans earlyWord)))
  have earlierWord (u:ℕ) (lo_:u<roof) (low_:u<header) (away:u<lo ∨ lo+(dates).length≤u):finished u=raw u :=
    (funds.2.2.2.2.1 u lo_ away).trans (dateLow u low_)
  have elimit:end_≤early_:=by
    unfold Calendar.earlyEnd Calendar.earlyAt
    omega
  have counts (a:ℕ) (v:_) (ha:a<limit) (hv:b.path.selections[a]?=some v):
      (finished (lo+a)).val=selectionCount G v:=by
    have normalized : (dates).length=b.path.selections.length:=
      (congrArg (fun kinds : List Bool => (countDates 0 kinds).length) b.kinds.symm).trans
        b.path.countDates_length
    have valid:a<(dates).length:=by
      rw [normalized]
      by_contra! impossible
      rw [List.getElem?_eq_none impossible] at hv
      contradiction
    have address:lo+a<early_:=by
      have placements:compact≤roof:=by omega
      have endRoof:roof≤early_:=by
        unfold Calendar.earlyEnd Calendar.earlyAt Calendar.stop Calendar.tableAt
        omega
      omega
    exact (congrArg Fin.val (funds.2.2.1 _ address)).trans (issued.2.1 a v ha hv)
  have seedBeforeCompact : seedFlag < compact :=
    seedLeft.trans_le ((Nat.le_add_right lo _).trans (captureEnd.trans historyLow))
  refine ⟨@funds.1,@funds.2.1,earlierWord _ (seedBeforeCompact.trans_le (by omega)) (by omega) (.inl seedLeft),
    fun i h₁ h₂=>earlierWord i (by omega) (by omega) (.inr (by omega)),?_,?_,counts,?_,funds.2.2.2.2.2⟩
  · intro col i hi
    have hc:col.val+1≤17:=col.isLt
    have cBound:=Nat.mul_le_mul_right H hc
    rw [Nat.add_mul,one_mul] at cBound
    change finished (compact+col.val*H+i)=raw (compact+col.val*H+i)
    exact earlierWord _ (by omega) (by omega) (.inr (by omega))
  · intro i hi
    exact earlierWord _ (by omega) (by omega) (.inr (by omega))
  · intro yes
    exact b.path.savedRotations_move reel end_ (issued.2.2 yes).2 (fun u hu=>funds.2.2.1 u (hu.trans_le elimit))


include shops in
/-- The debt word written by the chosen dated history survives the count copy,
early matrix relocation, and complete final preflight on their actual memories. -/
theorem funded_preflight_held
    (geometryRoom:(spec).maskBase census_<2^w) (wordPositive:0<w) (alive:0<places)
  (priorMetadata:phase.output.metadataEnd phase.dateBase≤early_) (one:chunks (hw_).groups (hw_).lanes=1)
  (rank:∀t<S.length,∀b,snapshots.compact t=some b→b.Fits w ((batchCal).scratch slices_))
  (roleEnd:roleBase+DescentTerminalRoleTables.count roleBits≤(spec).cohortEnd census_)
  (before:(spec).Before census_ paid actor signedBanks peer (shelf).total (shelf).modulo ((batchCal).homes slices_) (shelf).boundaries)
  (paidRowsFit:∀b,places≤(paid b).size) (signedRows:∀b j,places≤(signedBanks b j).size)
    (past:Memory w) (head:ℕ) (held:b.path.Held head past)
    (low:head<roof) (separate:head<lo ∨ lo+(dates).length≤head)
    (rotHi:∀a<S.length,rotation a<roof) (below:compact+32*H≤roof)
    (earlyRoom:Calendar.earlyEnd S k tail roof j rest t E<2^w) :
    let copied:=DescentLowCountBook.output lo source past (dates).length
    let moved:=Calendar.earlyImage S k tail roof tag rotation j rest t E compact copied
    b.path.Held head (out_ moved) := by
  intro copied moved
  have scan:=Calendar.early_run S k tail roof tag rotation j rest t E compact copied wordPositive rotHi below earlyRoom
  have last_:=post_early_preflight_run X G S base radix g p teams drift op headerRows paidRows
    j rest t roof phase snapshots blocks shops roleBase peer paid actor signedBanks cohortRoom
    geometryRoom wordPositive alive priorMetadata one rank roleEnd before paidRowsFit signedRows moved
  have first : roof≤early_:=by
    unfold Calendar.earlyEnd Calendar.earlyAt Calendar.stop Calendar.tableAt
    omega
  exact held.keep ((last_.1.2.2.1 head (.inl (low.trans_le first))).trans
    ((scan.2.2 head (.inl low)).trans (DescentLowCountBook.frame lo source past (dates).length head separate)))

omit [Field F] in
/-- The original layout puts the complete count book below the compact source
matrix and its seventeen pages below the retained header. -/
theorem counts_before_header (header:ℕ) (counts:lo+(dates).length≤compact)
    (cells:compact+17*H≤header) : lo+(dates).length≤header:=
  counts.trans ((Nat.le_add_right ..).trans cells)

include hp width wide shops in
theorem original_funded_readback
    (geometryRoom:(spec).maskBase census_<2^w) (wordPositive:0<w) (alive:0<places)
  (priorMetadata:phase.output.metadataEnd phase.dateBase≤early_) (one:chunks (hw_).groups (hw_).lanes=1)
  (rank:∀t<S.length,∀b,snapshots.compact t=some b→b.Fits w ((batchCal).scratch slices_))
  (roleEnd:roleBase+DescentTerminalRoleTables.count roleBits≤(spec).cohortEnd census_)
  (before:(spec).Before census_ paid actor signedBanks peer (shelf).total (shelf).modulo ((batchCal).homes slices_) (shelf).boundaries)
  (paidRowsFit:∀b,places≤(paid b).size) (signedRows:∀b j,places≤(signedBanks b j).size)
    (date : ℕ→DateCode w) (raw : Memory w)
    (signed : DescentSignedCableCodec.width 3 256*l.packedLanes≤w)
    («fields» : l.operandBits*l.operandLanes≤w) (earlyWord : header<l.base)
    (sourceSpace : DescentPackedSeed.publicWords X+DescentDyadicSpan.span jobs≤ seedEnd)
    (active : 0<pitch) (embed : payload≤w) (space : bound<2^w)
    (total : ∀i< S.length,∀m,∃out,(date i).Runs m out) (limit : ℕ) (accepted : Prop)
    (x : Fin E→Plane j rest→Fin t→Bool) (z : Hidden E j rest t→Bool)
    (printed : Loaded compact (fun _=>LinearEquiv.refl _ _) x z raw)
    (floors : ℕ→ℕ) (original : compact+17*H≤ header)
    (order : ∀i< S.length,header< floors i)
    (observed : b.path.dateReadbacks (DateCode.history date (startedAt raw)) tag rotation loc limit accepted)
    (apartCount : ∀i< S.length,loc i≠header) (apartMatrix : ∀i< S.length,rotation i≠header)
    (keepCount : ∀j< S.length,∀i,S.length≥i→ j< i→loc j< floors i)
    (keepMatrix : ∀j< S.length,∀i,S.length≥i→ j< i→ rotation j< floors i)
    (frame : ∀i< S.length,∀a,a≠header→a< floors i→
      DateCode.history date (startedAt raw) (i+1) a=DateCode.history date (startedAt raw) i a)
    (batchFit : S.batch< 2^w)
    (lowWrite : lo+(dates).length≤ compact) (below : compact+32*H≤ roof)
    (locs : ∀a∈dates,lo+(dates).length≤ loc a ∧ loc a+1< 2^w)
    (rotLo : ∀a< S.length,lo+(dates).length≤ rotation a) (rotHi : ∀a< S.length,rotation a< roof)
    (word : Calendar.earlyEnd S k tail roof j rest t E< 2^w)
    (dateCheap:∀i<S.length,(date i).cheap)
    (seedFlag historyStart extra:ℕ) (seedLeft:seedFlag<lo)
    (captureEnd:lo+(dates).length≤historyStart) (historyLow:historyStart≤compact)
    (archiveEnd:compact+17*H+extra≤header) (reelData:compact+17*H+extra≤roof) :
    let past:=DateCode.history date (startedAt raw) S.length
    let copied:=DescentLowCountBook.output lo source past (dates).length
    let earlyAt_:=Calendar.earlyImage S k tail roof tag rotation j rest t E compact copied
    let finished:=out_ earlyAt_
    DescentTerminalFundedReadback.Receipt (((DateCode.afterBoot (boot w) date S.length).seq
      (historyCountReel X S roof tag rotation loc lo compact k tail j rest t w)).seq code_)
      ((DateCode.afterTicks (ticks w) date S.length+((4+11*(dates).length)+Calendar.earlyClock S k tail j rest t E))+clock_)
      raw finished seedFlag historyStart compact j rest t E extra (fun out=>
        (∀a v,a<limit→b.path.selections[a]?=some v→(out (lo+a)).val=selectionCount G v) ∧
        (accepted→b.path.savedRotations reel end_ tail out) ∧ (shelf).Reads out) := by
  intro past copied earlyAt_ finished
  have paid_:=original_funded_source (X:=X) (G:=G) (S:=S) (b:=b) (hp:=hp) (base:=base) (width:=width)
    (roof:=roof) (tag:=tag) (rotation:=rotation) (loc:=loc) (lo:=lo) (compact:=compact)
    (op:=op) (wide:=wide) (pub:=pub) (l:=l) (header:=header) (payload:=payload) (Z:=Z)
    (teams:=teams) (drift:=drift) (headerRows:=headerRows) (paidRows:=paidRows) (phase:=phase)
    (snapshots:=snapshots) (blocks:=blocks) (shops:=shops) (roleBase:=roleBase) (peer:=peer)
    (paid:=paid) (actor:=actor) (signedBanks:=signedBanks) (cohortRoom:=cohortRoom)
    (geometryRoom:=geometryRoom) (wordPositive:=wordPositive) (alive:=alive) (priorMetadata:=priorMetadata)
    (one:=one) (rank:=rank) (roleEnd:=roleEnd) (before:=before) (paidRowsFit:=paidRowsFit) (signedRows:=signedRows)
    date raw signed «fields» earlyWord sourceSpace active embed space total limit accepted
    x z printed floors original order observed apartCount apartMatrix keepCount keepMatrix frame batchFit
    lowWrite below locs rotLo rotHi word dateCheap seedFlag historyStart extra seedLeft captureEnd historyLow archiveEnd reelData
  obtain ⟨exec_,cheap_,seed_,archive_,pins_,extra_,observed_⟩:=paid_
  exact ⟨@exec_,@cheap_,seed_,archive_,pins_,extra_,observed_⟩


end Branch
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
