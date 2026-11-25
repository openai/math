import OAI.Hierarchy.ProbeFixedPartyIndex
import OAI.Hierarchy.TaggedWireFundedElectedReads

namespace OAI
/-! # The native one-based ballot word selects the genuine fixed signed party at its original site -/
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
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


variable (size : ℕ) (extent : (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh≤ size) (M : ℕ) (π : Equiv.Perm (Fin (2^h)))
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
local notation "origin" b:arg => v.wideOrigin h width size ((L).header es b seed) π
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

theorem packet_tag_on (extent : (A).endAddress v.mesh≤ size) (tall : v.ballotHeight≤h)
    (floor : v.widthFloor≤width) (siteROM : ℕ) (out : Memory w)
    (arch : PrefixAgreement.Low ((A).endAddress v.mesh) out checkout)
    (rom : HistoryRoles.RoleROM.Mounted siteROM (SiteDirectory.table h D k) out) (siteRoom : SiteDirectory.size h D k≤2^w)
    (codes : 1+v.menuCodes N≤2^w) (tags : v.menuCodes N*v.wideBallotParties h a+1≤2^w)
    (i : Fin ((C).layout a).candidates) (pick : (batch).selected snap (i.val:Word w)) (j : Fin (v.wideBallotParties h a)) :
    let u:=H.packetAt extent tall floor i pick
    let fd:=v.wideFields P h width siteROM (.attempt a)
    ((fd.value j (0 : Fin (sig+2))).eval out (i.val:Word w)).val=(v.partyIndex h a u.atom j).val+1 ∧
      (fd.site j).eval out (i.val:Word w)=((u.installed.site j).val:Word w) := by
  intro u fd
  let : Nonempty (Fin k) := ⟨⟨0, v.positive⟩⟩
  have occ : Event.attempt a∈es:=by
    change _ ∈ events (C).mesh
    rw [H'.cut.events]
    simp
  have before : (A).base v.mesh (.attempt a)≤(A).endAddress v.mesh:=
    (Nat.le_add_right ..).trans ((A).within v.mesh _ occ)
  let run':=H'.readbackRun extent tall floor
  have layout:=(run'.boards a occ).1
  have active:=H'.committed_at extent i pick
  let major:=v.majorIndex h a u.atom
  have saved:=v.wide_ballot_tag P h width r banks source table target owners siteROM a H'.prior tail initial entry out
    H'.cut arch layout.board (v.market_rows_fit P h width (dims).strip a) j i active major
    (((congrArg Fin.val (H'.ballot extent i).1).symm.trans u.nativeCode).trans (v.major_code h a u.atom).symm) codes tags
  have cols:=(Classical.choose_spec (Filter.eventually_atTop.1 v.wide_face_room) h
    (max_le_iff.mp (max_le_iff.mp tall).2).2).1
  have bounds := v.wide_earned_before h width a (before.trans_lt (dims).words.addresses)
  refine ⟨saved.trans (congrArg (·+1) (v.compact_party h a u.atom j)),?_⟩
  exact u.installed.site_at u.atom root siteROM j ((A).base v.mesh (.attempt a)) out
    (fun z hz=>(arch z (hz.trans_le before)).trans ((H.checkout_agree H') z hz).symm)
    (by cases a <;> exact bounds) rom siteRoom cols

end FundedDate
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
