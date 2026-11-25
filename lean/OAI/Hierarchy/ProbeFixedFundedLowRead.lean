import OAI.Hierarchy.ProbeFixedElectedLowRead
import OAI.Hierarchy.ProbeFixedFundedPartyTag
import OAI.Hierarchy.TaggedWireFundedElectedReads
import OAI.Hierarchy.TaggedWireFundedElectedEntry
import OAI.Hierarchy.TaggedWideActiveBits

namespace OAI
/-! # Both genuine posted low widths on every funded histogram branch -/
noncomputable section
set_option quotPrecheck false
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
local notation "ownerStride" => ownerRowFactor D k v.sampler.degree v.depth
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

open LinearAlgebra.SpectralBooks.SiteTensor HistoryRoles
local notation "chartAt" vv:arg hh:arg ww:arg =>
  (vv).wideSignedChart hh ww ((vv).fixedTerminalStock ((vv).widePlacement hh ww) hh ww)
local notation "wordSize" vv:arg hh:arg => Native.wordBits hh (2^(vv).W) Native.copies
variable (extent : (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh≤ size) (tall : v.ballotHeight≤h)
    (floor : v.widthFloor≤width)
    (i : Fin ((chartAt v h width).layout a).candidates)
    (hit : (PurchaseStage.enabledBatch ((chartAt v h width).layout a) (repair (chartAt v h width) a)).selected
      (HistogramShelf.snapshot (chartAt v h width) a x) (i.val:Word (wordSize v h)))
local notation "u" => H.packetAt extent tall floor i hit
local notation "pad" => publicChord h D k
local notation "J" => v.wideBallotParties h a
local notation "deg" => v.widePacketDegree
variable (siteROM selectorBits : ℕ) (stride : Bank) (preStart postStart : ℕ)
    (out : Memory (wordSize v h)) (j : Fin (v.wideBallotParties h a))
local notation "party" => v.wideBallotSite P h width siteROM a
local notation "s" => (u).installed.site j
local notation "fields" => v.widePacketFields h width selectorBits (.attempt a) siteROM stride preStart postStart
local notation "row" => (i.val:Word w)
local notation "before" l:arg => (H.row extent tall floor l).input
local notation "after" l:arg => (H.tender extent tall floor l).post (c' l)
variable (b : Bool) {cap : ℕ}
    {total : (portGraph (siteLast h (2^v.W) k+1)).Port ((H.packetAt extent tall floor i hit).installed.site j)→ℕ}
    (parts : PassiveWindow.Parts ((portGraph (siteLast h (2^v.W) k+1)).Port ((H.packetAt extent tall floor i hit).installed.site j)) (Fin (v.widePacketDegree)) cap total)
variable
    (arch : PrefixAgreement.Low ((v.privateArena (v.widePlacement h width) h width).endAddress v.mesh) out
      (checkedOut (chartAt v h width) ((v.privateArena (v.widePlacement h width) h width).endAddress v.mesh)
        (v.wideOrigin h width size ((v.wideSelector h width age budget small).format.windows.header (events v.mesh) H'.code seed) π)))
    (rom : HistoryRoles.RoleROM.Mounted siteROM (SiteDirectory.table h (2^v.W) k) out)
    (siteRoom : SiteDirectory.size h (2^v.W) k≤2^(wordSize v h))
    (sites : (siteLast h (2^v.W) k+1)≤2^(wordSize v h))
    (codes : 1+v.menuCodes (Stages h (2^v.W))≤2^(wordSize v h))
    (tags : v.menuCodes (Stages h (2^v.W))*(v.wideBallotParties h a)+1≤2^(wordSize v h))
    (dated : NeighborReads out (i.val:Word (wordSize v h)) parts
      (pageRead (DatedRoleSheets.bank (v.widePacketPhysical h width) (if b then postStart else preStart) (v.widePacketShelf h) selectorBits 0)
        stride ((v.wideBallotSite (v.widePlacement h width) h width siteROM a) j) (d:=v.widePacketDegree))
      (pageRead (DatedRoleSheets.bank (v.widePacketPhysical h width) (if b then postStart else preStart) (v.widePacketShelf h) selectorBits 2)
        stride ((v.wideBallotSite (v.widePlacement h width) h width siteROM a) j) (d:=v.widePacketDegree)))
    (q : Fin v.widePacketDegree)

attribute [local irreducible] wideStockHeight widePlacement wideSignedWords FundedDate.packetAt
set_option maxHeartbeats 1500000
include arch rom siteRoom sites codes tags dated

/-- The actual pre- and post-snapshot use the same immutable elected packet, even
on a different funded histogram branch. Both sides read their own dated pages. -/
theorem party_low_read :
    ((fields).value j (v.widePacketLowColumn h width a b q)).eval out row=
      ((parts.owner q).elim 0 (fun p=>if 0<parts.width q then (if b then after i else before i) p.val.1 else 0):Word w) := by
  have located (t : Fin J) : (party t).eval out row=(((u).installed.site t).val:Word w) :=
    (H.packet_tag_on H' extent tall floor siteROM out arch rom siteRoom codes tags i hit t).2
  obtain ⟨ar,co,entryShape,exitShape,entryEq⟩:=H.elected_entry extent tall floor i hit (c' i)
  let readWidth (widths : Widths K) : Word w :=
    (parts.owner q).elim 0 (fun p => if 0 < parts.width q then widths p.val.1 else 0)
  cases b with
  | false =>
    have occ : Event.attempt a∈es:=by
      change _ ∈ events (C).mesh
      rw [H'.cut.events]
      simp
    let run':=H'.readbackRun extent tall floor
    have layout:=(run'.boards a occ).1
    have chosen:=v.wide_ballot_code P h width r banks source table target owners siteROM a H'.prior tail initial entry out
      H'.cut arch layout.board (v.market_rows_fit P h width (dims).strip a) root i
    have activeCode :
        ((v.wideFields P h width siteROM (.attempt a)).selected root).eval out row =
          (batch).packet.eval (HistogramShelf.snapshot C a entry) row :=
      chosen.trans (ite_eq_left (H'.committed_at extent i hit))
    have tag : ((v.earnedTag P h width a).eval out row).val=v.widePacketNumber h a (u).atom :=
      (congrArg Fin.val activeCode).trans ((congrArg Fin.val (H'.ballot extent i).1).symm.trans (u).nativeCode)
    have posted := (u).installed.low_wanted (u).atom root siteROM selectorBits stride preStart postStart j out row parts sites codes tag located dated q
    exact posted.trans (congrArg readWidth entryShape.symm)
  | true =>
    obtain ⟨ar',co',geom⟩:=H.packet_reads_on H' extent tall floor siteROM out arch rom siteRoom sites i hit
    let hist:=cast (congrArg₂ (fun n m=>Histogram (Fin n) m) ar' co') (c' i)
    have posted := (u).installed.low_installed (u).atom root pad siteROM selectorBits stride preStart postStart j out row parts hist geom sites (located j) dated q
    exact posted.trans (congrArg readWidth exitShape.symm)

/-- At an occupied original party this candidate accounts for every incident
active digit. All other candidates have subsingleton incident states. -/
theorem party_low_sum :
    ((fields).value j (v.widePacketLowColumn h width a b q)).eval out row=
      ((parts.owner q).elim 0 (fun p=>if 0<parts.width q then (∑l,if b then after l else before l) p.val.1 else 0):Word w) := by
  refine (H.party_low_read H' extent tall floor i hit siteROM selectorBits stride preStart postStart out j b parts arch rom siteRoom sites codes tags dated q).trans ?_
  have alone (p : (portGraph K).Port s) : (∑l,if b then after l else before l) p.val.1=
      (if b then after i else before i) p.val.1 := by
    rw [Finsupp.finsetSum_apply]
    apply Finset.sum_eq_single i
    · intro l _ ne
      have off:=H.away_from_party extent tall floor l hit j ne (c' l)
      cases b with
      | false => exact PassMatrix.vacant_width (before l) s off.1 p
      | true => exact PassMatrix.vacant_width (after l) s off.2.1 p
    · simp
  simp only [alone]

end FundedDate
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
