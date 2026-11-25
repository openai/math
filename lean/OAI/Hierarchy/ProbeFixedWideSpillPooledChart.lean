import OAI.Hierarchy.ProbeFixedWideSpillTurnChart
import OAI.Hierarchy.TaggedWideSpillPooledChart

namespace OAI
/-! # The concrete per-date five-field RAM publication on physically sorted sparse rows -/
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

theorem wide_spill_turn_chart_word (mark : Marks h v.W k v.wideJobs) (unique : Exclusive mark)
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
    let R:=v.wide_spill_turn_chart h width bits datedROM terminalROM terminalWork rankFirst turnFirst
      oldStart newStart leftOnly rightOnly j B pad mark unique initial m original rank frozen ro oldWindow rankWindow word
      left right siteWord lenWord active halves
    let keep:=ProtocolRAMDateSpillPosition.chartReal v.sampler π B pad
    let sparse:=R.columns ∘ keep
    let seats:=(ProtocolRAMTurnShelf.restrictedLive R.columns keep).trans R.put
    (∀f a,R.word f a=ProtocolRAMTurnShelf.entry sparse seats f a) ∧
      ∀z : ProtocolRAMTurnShelf.Live sparse,(seats z).1.val=
      ((ProtocolRAMDateSpillPosition.sparseSpine v.sampler π B pad
        ((B.datedLayout inj pad).num (ProtocolRAMDateSpillPosition.positionOrder v.sampler π B pad z.val).1)).visit
        (ProtocolRAMDateSpillPosition.positionOrder v.sampler π B pad z.val).2).val := by
  intro R keep sparse seats
  have live (i) (on : R.columns i 4≠0) : ∃g,(names) ((raw) i).1=.inr (.inl g) := by
    have widths : R.columns i 4=(words m).width ((raw) i).1.val :=
      ProtocolRAMPaidTurnPlacement.Canonical.widths B inj pad o roles (words m) (vals m)
        (fun t=>(words m).width t.val) (fun _=>rfl) i
    let a := ((raw) i).1
    have source : used m a = (words m).width a.val :=
      congrArg (fun t => (words m).width t.val) ((num).apply_symm_apply a)
    have pos : 0<used m ((raw) i).1 :=
      Nat.pos_of_ne_zero (fun z=>on (widths.trans (source.symm.trans z)))
    obtain ⟨g,hg,_⟩:=active ((raw) i).1 pos
    exact ⟨g,hg⟩
  refine ⟨fun f a=>ProtocolRAMDateSpillPosition.chart_word v.sampler π B pad R.columns live R.put f a,?_⟩
  exact fun z=>(R.loc (ProtocolRAMTurnShelf.restrictedLive R.columns keep z)).1.trans
    (ProtocolRAMDateSpillPosition.chart_site v.sampler π B pad z.val)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
