import OAI.Hierarchy.ProbeFixedWideSpillTurnRun
import OAI.Hierarchy.ProbeFixedWideTerminalWalk
import OAI.Hierarchy.ProtocolRAMDateSpillTurnEvidence
import OAI.Hierarchy.ProbeFixedWideSpillOriginalWords

namespace OAI
/-! # Calibrating the dated CPU from the original physical route, rank, and class words -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard ReportSockets WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat.RAM PhysicalProcedure
open HistoryRoles RoleProgram CoreRoute ProtocolRAMTurnChart ProtocolRAMTurnItinerary
open ProtocolRAMDateSpillRank ProtocolRAMTurnReplayed
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width bits datedROM terminalROM terminalWork rankFirst turnFirst : ℕ)
local notation "N" => (events v.mesh).length
local notation "T" => v.wideTerminal h width bits terminalROM terminalWork
local notation "L" => v.wideTurnWindow h width bits terminalWork
local notation "D" => 2^v.W
local notation "W" => Native.wordBits h D Native.copies
local notation "P" => v.widePlacement h width
local notation "E" => (P).catalogue.rows
local notation "Src" => ProtocolRAMTurnGeometry.Source E h D k
local notation "num" => ProtocolRAMTurnGeometry.sourceOrder E h D k
local notation "names" => (ProtocolRAMTurnGeometry.sourceOrder E h D k).symm
local notation "roles" => WordSeats.fixedRoom (k:=k) (attempts:=v.wideJobs) v.sampler
local notation "o" => wideRouteOrder h D k
local notation "u" => ProtocolRAMTurnGeometry.header o roles names
local notation "len" => ProtocolRAMTurnGeometry.length (h:=h) (d:=D) (k:=k) (edges:=E) ∘ names
local notation "raw" => ProtocolRAMTurnOrder.raw len
variable (oldStart newStart leftOnly rightOnly : Fin (events v.mesh).length→ℕ) (j : Fin (events v.mesh).length)
local notation "panel" => v.wideSpillTurnPage h width bits datedROM terminalROM terminalWork rankFirst turnFirst
  oldStart newStart leftOnly rightOnly j
local notation "pagej" => v.wideSpillPage h width bits rankFirst j.val
variable {π : Equiv.Perm (Fin (2^h))}
  (B : Mount (S:=v.sampler) π (name (h:=h) («W»:=v.W) (k:=k))
    (v.widePlacement h width).catalogue.rows)
  (pad : Chord (siteLast h (2^v.W) k+1))
local notation "inj" => (siteNumber h D k).injective
local notation "visit" => ProtocolRAMVisitAdjacency.vertex len (fun a=>ProtocolRAMTurnEdges.visit B inj pad (names a))
local notation "wire" => ProtocolRAMTurnOccurrence.edgeAt (h:=h) (d:=D) (k:=k) (edges:=E) B inj pad o
local notation "ends" => ProtocolRAMTurnOccurrence.endsAt (h:=h) (d:=D) (k:=k) (edges:=E) B inj pad
local notation "vals" m:arg => ProtocolRAMTurnSnapshot.values (panel).banks m
local notation "words" m:arg => captured (panel).data m
local notation "used" m:arg a:arg => (words m).width ((num) ((names) a)).val

private theorem expose {w : ℕ} (b : Bank) {a d : ℕ} (h : b.Fits w a) (le : a≤d) : b.Fits w d :=
  ⟨h.1,h.2.1,h.2.2.trans le⟩

private theorem chartBoardBeforeRank (b : Board) :
    b.base ≤ b.endAt+3*b.old+b.widthBank.size+(b.newRole true).size := by
  simp only [Board.endAt, Board.newBase]
  omega

private theorem chartKeyBeforeEnd (first count edges : ℕ) :
    first+2^ProtocolRAMPackedRanked.groupBits count ≤ endAt first count edges := by
  change first+2^ProtocolRAMPackedRanked.groupBits count ≤
    first+2^ProtocolRAMPackedRanked.groupBits count+2^ProtocolRAMPackedRanked.groupBits count+
    2*count+3*count+4*count+edges+3+2^ProtocolRAMPackedRanked.groupBits (4*count)
  simp only [Nat.add_assoc]
  exact Nat.add_le_add_left (Nat.le_add_right ..) first

private theorem chartMoveBanks {w oldCut cut : ℕ}
    (os ot oldKey tailS tailR headR oldRanks heads newKey newRanks : Bank)
    (inherited : ∀ a ∈ [os,ot,oldKey,tailS,tailR,headR,oldRanks,heads], a.Fits w oldCut)
    (later : oldCut ≤ cut) (keyFits : newKey.Fits w cut) (rankFits : newRanks.Fits w cut) :
    ∀ a ∈ [heads,os,ot,newKey,tailS,tailR,headR,newRanks], a.Fits w cut := by
  simp only [List.forall_mem_cons] at inherited ⊢
  obtain ⟨s,t,_,ts,tr,hr,_,head,_⟩ := inherited
  exact ⟨expose _ head later, expose _ s later, expose _ t later, keyFits,
    expose _ ts later, expose _ tr later, expose _ hr later, rankFits, fun _ h => nomatch h⟩

private theorem chartROMBounds (layout : ProtocolRAMTurnWindow.Layout) (start amount cut : ℕ)
    (bound : layout.readOnlyEnd start amount ≤ cut) :
    layout.directoryBase start+4*2^layout.romBits ≤ cut ∧
      start+6*2^ProtocolRAMPackedRanked.groupBits layout.rows ≤ cut := by
  have halfBefore : layout.halfBase start ≤ cut := (Nat.le_add_right ..).trans bound
  have headerBefore : layout.directoryBase start ≤ layout.halfBase start := Nat.le_add_right ..
  exact ⟨halfBefore, headerBefore.trans halfBefore⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1600000 in
/-- A phase on one date has no paid identity or catalyst-center source with nonzero spill.
The edge key is read from the newly executed rank pass. Original forward/role words and
paid half-edges are read on precisely those source rows that actually have width. -/
def wide_spill_turn_chart (mark : Marks h v.W k v.wideJobs) (unique : Exclusive mark)
    (initial m original : Memory W)
    (rank : RankRead B o (pagej).rankStart (pagej).overflow original m)
    (frozen : ∀a,terminalROM≤a→a<v.wideTerminalROMEnd h width bits terminalROM terminalWork→
      m a=v.wideTerminalWords h width bits terminalROM terminalWork initial a)
    (ro : v.wideTerminalROMEnd h width bits terminalROM terminalWork≤terminalWork)
    (oldWindow : v.wideTerminalWorkEnd h width bits terminalWork≤turnFirst)
    (rankWindow : (pagej).offsetsStart≤turnFirst) (word : turnFirst<2^W)
    (left : (panel).left.prefix.Fits W turnFirst) (right : (panel).right.prefix.Fits W turnFirst)
    (siteWord : (T).sites≤2^W) (lenWord : ∀a,len a<2^W)
    (active : ∀a,0<used m a→∃g,(names) a=.inr (.inl g) ∧
      (panel).data.rawSource.read m (((num) ((names) a)).val:Word W)=
        (ProtocolRAMTurnEdges.visit B inj pad ((names) a) 0:Word W) ∧
      (words m).sourceRole ((num) ((names) a)).val<2*roles ∧
      (words m).targetRole ((num) ((names) a)).val<2*roles)
    (halves : ∀a,0<used m a→∀t<len a,
      let e:=wire (ProtocolRAMTurnGeometry.origin o ((names) a)+t)
      (panel).banks.tailSite.read m (e:Word W)=((ends e).1:Word W) ∧ (T).heads.read m (e:Word W)=((ends e).2:Word W)) :
    (panel).Inputs turnFirst m := by
  let l:=L
  have oldWin : l.stop≤turnFirst:=oldWindow
  have bounds:=l.bounds
  have before : terminalWork≤l.floor :=
    (chartBoardBeforeRank (v.wideTerminalBoard h width bits terminalWork)).trans
      ((Nat.le_add_right _ _).trans (chartKeyBeforeEnd (v.wideTerminalRankStart h width bits terminalWork)
        ((T).edges+(T).routeEntries) (T).edges))
  have upto : l.zero≤turnFirst := by omega
  have readOnly := ro.trans (before.trans (by omega : l.floor≤turnFirst))
  have dataROM:=l.retained terminalROM roles u initial m (readOnly.trans word.le) frozen
  have header:=dataROM.1
  have rom:=dataROM.2.1
  have half:=dataROM.2.2
  have dataBanks:=v.wide_terminal_banks h width bits terminalROM terminalWork ro (oldWin.trans word.le)
  have safe:=dataBanks.1
  have banks:=dataBanks.2
  have newEnd : endAt (pagej).rankStart ((pagej).edges+(pagej).core) (pagej).edges≤turnFirst :=
    (Nat.le_add_right ..).trans rankWindow
  have keysLow : (key (pagej).rankStart ((pagej).edges+(pagej).core)).base+
      (key (pagej).rankStart ((pagej).edges+(pagej).core)).size≤turnFirst :=
    (chartKeyBeforeEnd (pagej).rankStart ((pagej).edges+(pagej).core) (pagej).edges).trans newEnd
  have treeLo : (pagej).amount.base+(pagej).amount.size≤turnFirst := by
    change (pagej).rankStart≤turnFirst
    change (pagej).rankStart+_≤turnFirst at keysLow
    omega
  have rankCount : E+coreCount o≤2^W := by
    have a:=ProtocolRAMPackedRanked.group_capacity (E+coreCount o)
    change (pagej).rankStart+2^ProtocolRAMPackedRanked.groupBits (E+coreCount o)≤turnFirst at keysLow
    omega
  have sized (b : Bank) (h : b.base+b.size≤turnFirst) : b.Fits W turnFirst :=
    ⟨Nat.two_pow_pos _,by omega,h⟩
  have safeNew : ProtocolRAMTurnCursor.Safe (panel).data W turnFirst :=
    ⟨expose _ safe.rawSource upto,expose _ safe.rawTarget upto,sized _ treeLo,expose _ safe.sourceRole upto,
     expose _ safe.targetRole upto,expose _ safe.half upto⟩
  have provided : ∀a∈(T).heads::[(panel).banks.oldSource,(panel).banks.oldTarget,(panel).banks.edge,
        (panel).banks.tailSite,(panel).banks.tailRole,(panel).banks.headRole,(panel).banks.starts],a.Fits W turnFirst := by
    exact chartMoveBanks (T).walk.oldSource (T).walk.oldTarget (T).walk.edge (T).walk.tailSite
      (T).walk.tailRole (T).walk.headRole (T).walk.starts (T).heads (panel).banks.edge
      (panel).banks.starts banks upto (sized _ keysLow) (sized _ newEnd)
  have oldBit : (T).base≤turnFirst := by change l.base≤turnFirst;omega
  have ahead : turnFirst≤(panel).base := by
    have b:=(panel).window.bounds
    have z : turnFirst≤(panel).window.floor := by change turnFirst≤turnFirst+_+_+_+_;omega
    change turnFirst≤(panel).window.base;omega
  have roRange : (T).rom+4*2^(T).romBits≤turnFirst ∧ (T).header+6*2^(T).headerBits≤turnFirst :=
    chartROMBounds l terminalROM roles turnFirst readOnly
  have keyOn a (positive : 0<used m a) b (h : b<len a) :
      let q:=ProtocolRAMTurnGeometry.origin o ((names) a)+b
      (panel).banks.edge.read m (q:Word W)=(wire q:Word W) := by
    obtain ⟨g,eqn,_⟩:=active a positive
    rw [Function.comp_apply,eqn] at h
    simp only [eqn]
    exact RankRead.key_on B inj pad o (pagej).rankStart rank rankCount g ⟨b,h⟩
  have each a (positive : 0<used m a) b (h : b<len a) :
      (vals m).edge (ProtocolRAMTurnGeometry.origin o ((names) a)+b)<E := by
    obtain ⟨g,eqn,_⟩:=active a positive
    have k:=keyOn a positive b h
    let path:=ProtocolRAMTurnEdges.walk B ((names) a)
    have iph : b<path.length := by change b<(ProtocolRAMTurnEdges.walk B ((names) a)).length;rw [ProtocolRAMTurnEdges.walk_length];exact h
    have geo:=ProtocolRAMTurnOccurrence.read B inj pad o ((names) a) b iph
    dsimp only at k
    rw [geo] at k
    have atW:=((path[b]).isLt.trans_le (by omega : E≤2^W))
    change ((panel).banks.edge.read m _).val<E
    rw [k,Fin.val_cast_of_lt atW];exact (path[b]).isLt
  let startPos (n : ℕ):=((panel).left.prefix.eval m (n:Word W)).val
  let endPos (n : ℕ):=((panel).right.prefix.eval m (n:Word W)).val
  have noPermanent (e : Fin E) : (words m).width ((num) (.inl e)).val=0 := by
    apply Nat.eq_zero_of_not_pos
    intro pos
    let a:=(num) (.inl e)
    have eqn : (names) a=.inl e := (num).symm_apply_apply _
    obtain ⟨g,c,_⟩:=active a (by simpa only [eqn] using pos)
    rw [eqn] at c;cases c
  let seating:=DateSpill.Turns.placed v.sampler π B pad o v.depth mark unique names (words m) (vals m) startPos endPos noPermanent
  refine {
    «u» := u
    w := words m
    sitesAt := visit
    oldBase := startPos
    newBase := endPos
    leftSafe := left
    rightSafe := right
    original := rom
    romLow := roRange.1
    oldBaseLow := oldBit.trans ahead
    bits := rfl
    headerLow := roRange.2
    «public» := header
    safe := safeNew
    bank := provided
    weights := fun i => captured_width _ _ _
    within := ProtocolRAMTurnGeometry.within o roles names
    lengthFit := fun i => lenWord ((raw) i).1
    posPrev := ProtocolRAMTurnOrder.has_previous len
    siteFits := ?siteFits
    old := ?old
    closed := ?closed
    endpoint := ?endpoint
    left := ?leftRead
    right := ?rightRead
    put := seating.val
    loc := seating.property
    widthFit := fun _ => Fin.isLt _ }
  case siteFits =>
    intro i _
    exact (v.wide_visit_bound h width B pad ((names) ((raw) i).1) ((raw) i).2.val).trans_le siteWord
  case old =>
    intro i pos
    obtain ⟨g,eqn,_,a,b⟩:=active ((raw) i).1 pos
    exact captured_at _ m _ roles half a b
  case closed =>
    intro i hp hi
    exact ProtocolRAMTurnMap.live_closed names (fun a=>used m a) i hp hi
  case endpoint =>
    intro i hi
    exact ProtocolRAMTurnMap.live_endpoint_on B inj pad o names (T).header (T).headerBits roles
      (panel).data (panel).banks.edge (panel).banks.tailSite (T).heads m (fun a=>used m a) header lenWord
      (fun a h=>(active a h).choose_spec.2.1) keyOn halves i hi
  case leftRead =>
    intro i _ s _
    exact ⟨(num ((names) ((raw) i).1)).isLt,(Fin.cast_val_eq_self _).symm⟩
  case rightRead =>
    intro i hi s hb
    have shape : (record u (words m) visit i).position≤(u i).length := by
      change (if _ then _ else _)≤_
      split
      · exact Nat.sub_le ..
      · exact ProtocolRAMTurnGeometry.within o roles names i
    obtain ⟨t,loc⟩:=DateSpill.Turns.indexed_occurrence (record u (words m) visit i) shape s hb
    refine ⟨?_,(Fin.cast_val_eq_self _).symm⟩
    exact (congrArg (vals m).edge loc).trans_lt (each ((raw) i).1 hi t.val t.isLt)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
