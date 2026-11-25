import OAI.Hierarchy.TaggedWireFundedBoundaryData
import OAI.Hierarchy.ProbeFixedCatalystBirth

namespace OAI
/-! # Every geometric sampler read avoids the private selector words at all dates -/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets
open WireTelescope Tagged ThreeFlat.RAM
open scoped Classical Fin.CommRing
private theorem extendRight {a b d : ℕ} (bound : a ≤ b) : a ≤ b + d :=
  bound.trans (Nat.le_add_right _ _)

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "E" => v.publicHeader P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "num" => Fintype.card (Columns h D)*k
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "decl" => declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A)
local notation "cnt" => rowOnlyCount v.mesh decl
local notation "stride" => ownerRowFactor D k v.sampler.degree v.depth
  (max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k)))*2^h


local notation "page" => v.wideSignedPage h width
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "f" => v.nativeFormats P h width


local notation "stock" => v.fixedTerminalStock P h width
local notation "bits" => page stock
local notation "banks" => TerminalLayout.settlement bits stock
local notation "source" => TerminalLayout.source bits
local notation "table" => TerminalLayout.table bits
local notation "target" => TerminalLayout.destination bits
local notation "C" => v.wideSignedChart h width stock
local notation "g" => v.stamp P h width r banks source table target owners
local notation "order" => wideRouteOrder h D k


variable (size : ℕ) (extent : (A).endAddress v.mesh≤ size) (M : ℕ) (π : Equiv.Perm (Fin (2^h)))
  (seed : Boot.Tape h D) (age : v.wideStockHeight≤h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
local notation "reader" => v.wideSelector h width age budget small
local notation "es" => events v.mesh
local notation "L" => (reader).format.windows
local notation "mid" => v.wideSignedMidAt h width size stock M π order

local notation "funded" => v.wideFundedRaw h width v.maxBits seed
local notation "original" => v.wideSignedWords h width stock v.radius π.symm order funded
local notation "V" => v.catalystMarkets P h width
local notation "input" => fun _ : Equiv.Perm (Row h)=>original
local notation "dims" => v.wide_stock_sizes h width age budget small
local notation "base" => v.wideOrigin h width size seed π
local notation "origin" b => v.wideOrigin h width size ((L).header es b seed) π
local notation "slots" => (reader).format.slot
local notation "auth" => v.wide_signed_words_authentic h width stock v.radius π.symm order funded
local notation "heap" => (v.wideGeometryPrefix h width).2.1

local notation "slab" => v.slab (v.seed P h width) P width
local notation "EF" => Slab.effects slab s F v.mesh (P).joint.initial width v.keepLimit v.finish (v.basePhase width)
  (P).catalogue banks source table target owners
local notation "pageRoom" => v.original_selector_room P h width (dims).words.addresses
local notation "copyRoom" => v.original_copy_room P h width r banks source table target owners (dims).copies
local notation "floorE" e => (A).base v.mesh e
local notation "ceilE" e => (A).base v.mesh e+(A).stride
local notation "top" => (A).endAddress v.mesh


local notation "sized" => v.sized (v.seed P h width) width
local notation "span" => Slab.selectorSpan sized
local notation "floorAt" e:arg => (A).base v.mesh e

/-- Each physical private histogram page ends inside the selector prefix
of its own event. This bounds the whole page even for padded dormant rows. -/
theorem selector_span_at (e : Event) :
    (L).base e+(L).cells e≤floorAt e+span := by
  cases e with
  | feed b=>exact Nat.zero_le _
  | attempt a=>
    have rowEq : ((f) a).market.rows = Slab.rows sized := by
      rw [Slab.rows_eq sized]
      exact candidate_count F v.mesh A (P).joint.initial s a
    have inner := Slab.selector_room sized
    rw [Nat.mul_comm, ←rowEq] at inner
    exact Nat.add_le_add_left inner ((A).base v.mesh (.attempt a))

/-- Any genuine interval after its private prefix and contained in its
event's allocation is disjoint from every selector, including future ones. -/
theorem after_selector_public (e : Event) (q : Bank)
    (lo : floorAt e+span≤q.base) (hi : q.base+q.size≤floorAt e+(A).stride)
    (tail : List Event) : ReadBanks.PublicBank ((reader).hidden tail) q := by
  intro u qu uq
  rintro ⟨ev,_,inside⟩
  rcases ev with f₀|b
  · have atStart : floorAt (.attempt f₀)≤u:=inside.1
    have atEnd:=inside.2.trans_le (v.selector_span_at h width age budget small (.attempt f₀))
    rcases lt_trichotomy (position v.mesh (.attempt f₀)) (position v.mesh e) with early|eqn|later
    · have enough : span≤(A).stride := by
        change Slab.selectorSpan sized≤Slab.stride slab sized
        simp only [Slab.stride,PostLayout.column,PostLayout.startColumns,Slab.mask,Slab.flags,Slab.first,Nat.zero_add]
        repeat' first | rfl | apply extendRight
      have gap:=(A).apart v.mesh early
      omega
    · have root : floorAt (.attempt f₀)=floorAt e:=by simp only [Arena.base,eqn]
      omega
    · have gap:=(A).apart v.mesh later
      omega
  · have impossible:=inside.2
    change u<0 at impossible
    omega

theorem outer_source_public (p t : Nat) (i : PurchaseFrozen.Key h D k) (tail : List Event) :
    let sh:=((s).outer p t).market.shelf
    ReadBanks.PublicBank ((reader).hidden tail) (sh.L v.sampler v.depth i).source := by
  intro sh
  let stage:=(f) (.outer p t)
  let ev:=Event.attempt (.outer p t)
  let L₀:=sh.L v.sampler v.depth i
  let r₀:=L₀.regions
  have slabStart :=((Slab.sizes slab sized F v.mesh (P).joint.initial (.outer p t)).2.2.2.1)
  have start' : sh.firstBase=Slab.first slab sized (floorAt ev):=slabStart
  have address : L₀.start=sh.firstBase+i.val*PurchaseFrozen.blockSize h D v.sampler.degree v.depth:=rfl
  have reach : L₀.endAddress≤ stage.market.flags :=
    (sh.end_le v.sampler v.depth i Nat.one_le_two_pow).trans ((sh.final_after v.sampler v.depth i).trans (Nat.le_add_right ..))
  have endRoom:=(v.catalyst_birth_room P h width (.outer p t)).2.2
  obtain ⟨d₁,d₂,d₃,d₄,d₅,d₆,d₇,d₈,d₉⟩:=r₀
  apply v.after_selector_public h width age budget small ev L₀.source _ _ tail
  · have afterFirst : floorAt ev + span ≤ sh.firstBase := by
      rw [start']
      exact extendRight (extendRight (Nat.le_refl _))
    have afterOffset : sh.firstBase ≤ L₀.start := by
      rw [address]
      exact Nat.le_add_right _ _
    have sourceAfter : L₀.start ≤ L₀.source.base := by
      rw [←d₅,←d₄,←d₃,←d₂]
      exact extendRight (extendRight (extendRight (extendRight d₁)))
    exact afterFirst.trans (afterOffset.trans sourceAfter)
  · change stage.market.flags+stage.market.rows≤floorAt ev+(A).stride at endRoom
    omega

theorem actual_shelf_public (j : Fin v.wideJobs) (i : PurchaseFrozen.Key h D k) (tail : List Event) :
    ReadBanks.PublicBank ((reader).hidden tail) (((v.wideSources h width).2.shelf j).L v.sampler v.depth i).source := by
  let p:=(v.sourceOuter j).1
  let t:=(v.sourceOuter j).2
  have actual:=v.sourcePair_uses h width (WideMemory.K h v.W) (WideMemory.dir h v.W k v.wideJobs).groups
    (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k) (CoreCatalogue.pointBits h v.W) 0
    (v.wideJoint h width) r banks source table target owners p t
  have jp : finProdFinEquiv (p,t)=j:=finProdFinEquiv.apply_symm_apply j
  have eqShelf : (v.wideSources h width).2.shelf j=((s).outer p t).market.shelf:=by
    have one:=actual.1
    rw [jp] at one
    exact one
  rw [eqShelf]
  exact v.outer_source_public h width age budget small p t i tail

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
