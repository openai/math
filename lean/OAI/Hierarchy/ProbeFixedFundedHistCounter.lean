import OAI.Hierarchy.TaggedWireFundedElectedReads
import OAI.Hierarchy.ProbeFixedWidePacketFields
import OAI.Hierarchy.ProbeSelectorShelf

namespace OAI
/-! # The archived counter of the actual elected branch in the extended ballot fields -/
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
set_option cleanup.letToHave false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets
open WireTelescope Tagged ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "boards" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "E" => v.publicHeader P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "num" => Fintype.card (Columns h D)*k
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "decl" => declaredRows v.mesh (ownerLedger boards v.mesh (P).catalogue (P).routes F A)
local notation "cnt" => rowOnlyCount v.mesh decl
local notation "stride" => ownerRowFactor D k v.sampler.degree v.depth
  (max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k)))*2^h


local notation "page" => v.wideSignedPage h width
local notation "owners" => sinkBank start cnt r (P).catalogue.rows


local notation "stock" => v.fixedTerminalStock P h width
local notation "bits" => page stock
local notation "banks" => TerminalLayout.settlement bits stock
local notation "source" => TerminalLayout.source bits
local notation "table" => TerminalLayout.table bits
local notation "target" => TerminalLayout.destination bits
local notation "C" => v.wideSignedChart h width stock
local notation "g" => v.stamp P h width r banks source table target owners
local notation "slots" => max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k))
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

open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open WireTelescope.ChosenPackets WireTelescope.PacketTurns

namespace FundedDate
variable {v h width size π seed age budget small} {a : Attempt} {tail x}
    {t : CalendarTape.Prefix (v.wideSelector h width age budget small).format.slot (events v.mesh)
      (v.wideOrigin h width size seed π) (.attempt a::tail) x} {c c' : ((v.wideSelector h width age budget small).format.slot (.attempt a)).choice x}
    (H : v.FundedDate h width size π seed age budget small t c)
    (H' : v.FundedDate h width size π seed age budget small t c')
local notation "initial" => origin H'.code
local notation "entry" => run C H'.prior initial
local notation "checkout" => checkedOut C ((A).endAddress v.mesh) initial
local notation "batch" => PurchaseStage.enabledBatch ((C).layout a) (repair C a)
local notation "snap" => HistogramShelf.snapshot C a x
local notation "fmt" => (reader).format
local notation "sig" => (catalogue F (v.configured (v.seed P h width)) v.cost).alphabet
local notation "root" => v.wideBallotRoot h a
local notation "K" => siteLast h D k+1
local notation "names" => (siteNumber h D k).toEmbedding
local notation "shape" => CatalogueRows.installedRows π.symm
  ((P).catalogue.physicalEnds (π:=π.symm)
    (marks:=v.birthMarks P h width r banks source table target owners (origin H.code)) (P).routes.directory
    (v.wideOrder h width) rfl) names (publicChord h D k)

local notation "degree" => v.widePacketDegree
local notation "M" => v.widePacketRoles h
local notation "extra" => ((M*3)*5+(degree+degree))
local notation "J" => v.wideBallotParties h a
local notation "middle" => PacketTurns.middleColumns M

theorem histCounter (extent : (A).endAddress v.mesh≤ size) (tall : v.ballotHeight≤h) (floor : v.widthFloor≤width)
    (siteROM selectorBits : ℕ) (strideBank : Bank) (preStart postStart : ℕ)
    (out : Memory w) (arch : PrefixAgreement.Low ((A).endAddress v.mesh) out checkout)
    (i : Fin ((C).layout a).candidates) (pick : (batch).selected snap (i.val:Word w)) (j : Fin J)
    (arity : (fmt).letters a x i=((H.packetAt extent tall floor i pick).menu root).data.terms)
    (mass : (fmt).copies a x i=(batch).copies)
    (atom : Fin ((H.packetAt extent tall floor i pick).menu root).data.terms) {B : ℕ} (bit : Fin B) :
    let bound : ((H.packetAt extent tall floor i pick).menu root).data.terms ≤ sig := arity ▸ (fmt).width a x i
    let hist:=cast (congrArg₂ (fun n b=>Histogram (Fin n) b) arity mass) (c' i)
    let fields:=v.widePacketFields h width selectorBits (.attempt a) siteROM strideBank preStart postStart
    let col:=(atom.castLE bound).succ.succ
    ((fields.value j (((col.castAdd extra).castAdd J).castAdd middle)).eval out (i.val:Word w)).val.testBit bit.val=
      Probe.SelectorShelf.bits hist B atom bit := by
  intro bound hist fields col
  have lower := v.widePacket_base h width selectorBits siteROM strideBank preStart postStart a j col
  have same := congrArg (fun f => Expr.eval out (i.val : Word w) f) lower
  have native:=v.wide_ballot_chosen P h width r banks source table target owners siteROM a H'.prior tail initial entry out
    H'.cut arch (dims).words.addresses (dims).copies j i (atom.castLE bound) x c' H'.ballot_word
  have equal:=native.trans (castCounter ((fmt).letters a x) ((fmt).copies a x) c' ((fmt).count a x) i arity mass bound atom)
  have enough : (hist.val atom).val<2^w:=(Nat.le_of_lt_succ (hist.val atom).isLt).trans_lt (mass ▸ (fmt).count a x i)
  exact congrArg (fun n:ℕ=>n.testBit bit.val) ((congrArg Fin.val (same.trans equal)).trans (Fin.val_cast_of_lt enough))

theorem hist_bit (extent : (A).endAddress v.mesh≤ size) (tall : v.ballotHeight≤h) (floor : v.widthFloor≤width)
    (siteROM selectorBits : ℕ) (strideBank : Bank) (preStart postStart : ℕ)
    (out : Memory w) (arch : PrefixAgreement.Low ((A).endAddress v.mesh) out checkout)
    (i : Fin ((C).layout a).candidates) (pick : (batch).selected snap (i.val:Word w)) (j : Fin J)
    (arity : (fmt).letters a x i=((H.packetAt extent tall floor i pick).menu root).data.terms)
    (mass : (fmt).copies a x i=(batch).copies)
    (atom : Fin ((H.packetAt extent tall floor i pick).menu root).data.terms) {B : ℕ} (bit : Fin B)
    (fetch : ℕ→ℕ→Bool) (read : ∀(f : Fin (v.widePacketShape h width (.attempt a)).columns) (d : ℕ),
      fetch f.val d=(((v.widePacketFields h width selectorBits (.attempt a) siteROM strideBank preStart postStart).value j f).eval out (i.val:Word w)).val.testBit d) :
    let hist:=cast (congrArg₂ (fun n b=>Histogram (Fin n) b) arity mass) (c' i)
    fetch (2+atom.val) bit.val=Probe.SelectorShelf.bits hist B atom bit := by
  let bound : ((H.packetAt extent tall floor i pick).menu root).data.terms ≤ sig := arity ▸ (fmt).width a x i
  let col:=(((atom.castLE bound).succ.succ.castAdd extra).castAdd J).castAdd middle
  have number : col.val=2+atom.val:=by
    change atom.val+1+1 = 2+atom.val
    omega
  rw [←number]
  exact (read col bit.val).trans (H.histCounter H' extent tall floor siteROM selectorBits strideBank preStart postStart
    out arch i pick j arity mass atom bit)

end FundedDate
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
