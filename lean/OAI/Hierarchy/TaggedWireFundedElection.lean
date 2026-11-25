import OAI.Hierarchy.TaggedWireFundedExecution
import OAI.Hierarchy.ProbeFixedWideAlphabetOrigin
import OAI.Hierarchy.ProtocolRAMCalendarStripChoices

namespace OAI
/-! # Actual signed packet ordinals before and after writing a selector word -/

noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 3500000
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets
open WireTelescope Tagged ThreeFlat.RAM
open scoped Classical Fin.CommRing
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


variable (size : ℕ) (extent : (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh ≤ size) (M : ℕ) (π : Equiv.Perm (Fin (2^h)))
  (seed : Boot.Tape h (2^v.W)) (age : v.wideStockHeight≤h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
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

open StripDirectory
local notation "slab" => v.slab (v.seed P h width) P width

include extent in
theorem funded_ballot_views {a : Attempt} {tail : List Event} {x : Memory w}
    (t : CalendarTape.Prefix slots es base (.attempt a::tail) x)
    (c : (slots (.attempt a)).choice x) :
    let y:=(reader).patch (.attempt a) x c
    let before:=HistogramShelf.snapshot C a x
    let after:=HistogramShelf.snapshot C a y
    let b:=PurchaseStage.enabledBatch ((C).layout a) (repair C a)
    (reader).format.observed a x x ∧ (reader).format.observed a x y ∧
      ∀i : Fin ((C).layout a).candidates,
        b.packet.eval before (i.val:Word w)=b.packet.eval after (i.val:Word w) ∧
        b.termCount.read before (b.packet.eval before (i.val:Word w))=
          b.termCount.read after (b.packet.eval after (i.val:Word w)) ∧
        (b.selected before (i.val:Word w) ↔ b.selected after (i.val:Word w)) := by
  let y:=(reader).patch (.attempt a) x c
  obtain ⟨h₀,h₁⟩:=v.wide_funded_cuts h width size extent π seed age budget small t
  obtain ⟨r₀,p₀,U⟩:=h₀
  obtain ⟨r₁,p₁,V₁⟩:=h₁ c
  have admitted (raw : Bits (CalendarTape.bits slots es)) (prior : List Event) (m : Memory w)
      (cut : Calendar.Slot C (origin raw) (.attempt a) prior tail m) (i : Fin ((C).layout a).candidates) :
      CalendarTape.CounterROM.measured («C»:=C) a m i≤(StripChart.catalogue F (v.configured (v.seed P h width)) v.cost).alphabet := by
    have alph:=v.wide_alphabet_origin_at h width size extent stock v.radius π.symm order
      (v.wideFundedRaw h width v.maxBits ((L).header es raw seed))
    let capped (n : ℕ) := (E).menus.leftAlphabet.Capped n (origin raw) ∧
      (E).menus.rightAlphabet.Capped n (origin raw)
    have capAt : capped (StripChart.catalogue F (v.configured (v.seed P h width)) v.cost).alphabet :=
      (congrArg capped (v.catalogue_words (v.seed P h width) width).1.symm).mp alph
    exact cut.entry ▸ v.native_measured P h width r banks source table target owners prior a (origin raw)
      capAt cut.prefixReady (cut.entry.symm ▸ cut.currentReady) i
  have placed:=v.wideGeometryPrefix h width
  let coreStart:=CoreCatalogue.top h v.W (WideMemory.K h v.W) (WideMemory.dir h v.W k v.wideJobs).groups
    (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
  have keyEnd:=(Public.borders v.sampler coreStart h v.W k v.wideJobs v.depth).2
  have dir : (stratumHeader h D k v.sampler.degree v.depth (P).routes.directory.keysBase).stop≤(P).joint.initial :=
    keyEnd.trans ((Nat.le_add_right ..).trans placed.2.2)
  have hfit : h<2^w := (Nat.lt_two_pow_self (n:=h)).trans (v.date_prefix_fit h)
  have cap : v.menu.maximum<2^w :=
    (((Nat.le_max_left ..).trans ((Nat.le_max_right ..).trans (dims).market)).trans_lt hfit)
  have tables:=v.election_pages P h width a cap (dims).words.cut dir
  have wide : 4≤2^w:=calc
    4=2^2:=by decide
    _≤2^w:=Nat.pow_le_pow_right (by decide) (by unfold Native.wordBits;omega)
  have appears : Event.attempt a∈es :=by
    have eventsEq : es = p₀ ++ .attempt a :: tail := U.events
    rw [eventsEq]
    simp
  have fits : (A).base v.mesh (.attempt a)<2^w:=
    (Nat.le_add_right ..).trans_lt (((A).within v.mesh _ appears).trans_lt (dims).words.addresses)
  have low : Below ((A).base v.mesh (.attempt a)) x y := by
    intro u hu
    symm
    apply (L).install_off
    intro inside
    exact (Nat.not_le_of_lt hu) inside.1
  let obs:=Slab.choice_before slab s F v.mesh (P).joint.initial width v.keepLimit v.finish (v.basePhase width)
    (P).catalogue banks source table target owners reader a
  exact ⟨obs x x (fun _ _=>rfl) U.currentReady U.currentReady wide fits tables (admitted r₀ p₀ x U),
    obs x y low U.currentReady V₁.currentReady wide fits tables (admitted r₁ p₁ y V₁),
    Slab.ballot_before slab s F v.mesh (P).joint.initial width v.keepLimit v.finish (v.basePhase width)
      (P).catalogue banks source table target owners a x y low U.currentReady V₁.currentReady wide fits tables⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
