import OAI.Hierarchy.ProbeFixedFundedLowRead
import OAI.Hierarchy.ProbeFixedFundedOccupiedRows

namespace OAI
/-! # Original pre- and post-ballot widths in every physical output cell -/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
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
local notation "dims" => v.wide_stock_sizes h width age budget small
local notation "base" => v.wideOrigin h width size seed π
local notation "origin" b:arg => v.wideOrigin h width size ((L).header es b seed) π
local notation "slots" => (reader).format.slot
local notation "auth" => v.wide_signed_words_authentic h width stock v.radius π.symm order funded
local notation "heap" => (v.wideGeometryPrefix h width).2.1

open StripDirectory
local notation "slab" => v.slab (v.seed P h width) P width

open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat.Diagonal.MotifOuterTerms
open WireTelescope.ChosenPackets WireTelescope.PacketTurns

open WideCPU

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


local notation "I" => Fin ((C).layout a).candidates
local notation "J" => Fin (v.wideBallotParties h a)
local notation "picked" i:arg => (batch).selected snap ((i : I).val:Word w)
local notation "ballots" => {i : I // picked i} × J
variable (extent : (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh ≤ size) (tall : v.ballotHeight≤h) (floor : v.widthFloor≤width)
local notation "chosen" u:arg => H.packetAt extent tall floor (u : ballots).1.val (u : ballots).1.property

local notation "atSite" => H.occupiedBallots extent tall floor
local notation "sh" => v.widePacketShape h width (.attempt a)
local notation "orig" => v.wideBallotRows h width r banks source table target owners a (entryMemory C initial a)
local notation "old" => (v.wideBallotShape P h width (.attempt a)).columns
local notation "extra" => ((v.widePacketRoles h*3)*5+(v.widePacketDegree+v.widePacketDegree))
local notation "middle" => PacketTurns.middleColumns (v.widePacketRoles h)
local notation "tagColumn" => ((((0 : Fin old).castAdd extra).castAdd (v.wideBallotParties h a)).castAdd middle)
variable (selectorBits siteROM : ℕ) (strideBank : Bank) (preStart postStart : ℕ) (processing : Memory (Native.wordBits h (2^v.W) Native.copies))
local notation "fd" => v.widePacketFields h width selectorBits (.attempt a) siteROM strideBank preStart postStart
local notation "words" => fun (u : ballots) (c : Fin (sh).columns)=>((fd).value u.2 c).eval processing (u.1.val.val:Word w)
private abbrev lowTableCheckout := checkout

variable (arch : PrefixAgreement.Low ((v.privateArena (v.widePlacement h width) h width).endAddress v.mesh)
      processing (lowTableCheckout H'))
    (rom : HistoryRoles.RoleROM.Mounted siteROM (SiteDirectory.table h (2^v.W) k) processing)
    (siteRoom : SiteDirectory.size h (2^v.W) k ≤ 2^(Native.wordBits h (2^v.W) Native.copies))
    (namesFit : siteLast h (2^v.W) k+1 ≤ 2^(Native.wordBits h (2^v.W) Native.copies))
    (codes : 1+v.menuCodes (Stages h (2^v.W)) ≤ 2^(Native.wordBits h (2^v.W) Native.copies))
    (tags : v.menuCodes (Stages h (2^v.W))*v.wideBallotParties h a+1 ≤ 2^(Native.wordBits h (2^v.W) Native.copies))

open LinearAlgebra.SpectralBooks.SiteTensor HistoryRoles
local notation "deg" => v.widePacketDegree
local notation "active" b:arg i:arg => if b then (H.tender extent tall floor i).post (c' i) else (H.row extent tall floor i).input
variable (shelfStart : ℕ) (out : Memory (Native.wordBits h (2^v.W) Native.copies))

private abbrev postedRows := printedSiteRows sh K shelfStart fd orig processing out

variable (printed : postedRows H' selectorBits siteROM strideBank preStart postStart processing shelfStart out)
    (s : Fin (siteLast h (2^v.W) k+1)) (b : Bool) {cap : ℕ} {total : (portGraph (siteLast h (2^v.W) k+1)).Port s→ℕ}
    (parts : PassiveWindow.Parts ((portGraph (siteLast h (2^v.W) k+1)).Port s) (Fin v.widePacketDegree) cap total)
    (q : Fin v.widePacketDegree)
local notation "sheet" f:arg => DatedRoleSheets.bank (v.widePacketPhysical h width) (if b then postStart else preStart) (v.widePacketShelf h) selectorBits f
local notation "page" u:arg f:arg => pageRead (sheet f) strideBank (v.wideBallotSite P h width siteROM a (u:ballots).2) (d:=deg)

private theorem guardedOwner {α : Type*} (wordSize : ℕ) (owner : Option α) (paid : ℕ) (digits : α → ℕ)
    (positive : ∀p, owner=some p → 0<paid) :
    (owner.elim 0 (fun p => if 0<paid then digits p else 0) : Word wordSize) =
      (owner.elim 0 (fun p => digits p) : Word wordSize) := by
  cases owner with
  | none => rfl
  | some p => simp only [Option.elim_some, ite_eq_left (positive p rfl)]

private theorem emptyOwner {α : Type*} (wordSize : ℕ) (owner : Option α) (digits : α → ℕ)
    (empty : ∀p, digits p=0) :
    (0 : Word wordSize) = (owner.elim 0 (fun p => digits p) : Word wordSize) := by
  cases owner with
  | none => rfl
  | some p => simp only [Option.elim_some, empty, Nat.cast_zero]

include arch rom siteRoom namesFit codes tags printed in
/-- A vacant output slot contains zero; at an occupied site the posted word is
the complete incident active width, using the actual earlier or later degree-bank. -/
theorem production_low_word
    (dated : ∀u : ballots, atSite u=s→NeighborReads processing (u.1.val.val:Word w) parts (page u 0) (page u 2))
    (owned : ∀p,parts.owner q=some p→0<parts.width q) :
    out (shelfStart+1+s.val*(sh).columns+(v.widePacketLowColumn h width a b q).val)=
      ((parts.owner q).elim 0 (fun p=>(∑l,active b l) p.val.1):Word w) := by
  refine (H.production_word H' extent tall floor selectorBits siteROM strideBank preStart postStart processing arch rom
    siteRoom namesFit codes tags shelfStart out printed s (v.widePacketLowColumn h width a b q)).trans ?_
  by_cases live : s∈Set.range atSite
  · obtain ⟨u,rfl⟩:=live
    refine (SiteScatter.active atSite words u (v.widePacketLowColumn h width a b q)).trans ?_
    have real:=H.party_low_sum H' extent tall floor u.1.val u.1.property siteROM selectorBits strideBank preStart postStart
      processing u.2 b parts arch rom siteRoom namesFit codes tags (dated u rfl) q
    exact real.trans (guardedOwner w (parts.owner q) (parts.width q)
      (fun p => (∑l,active b l) p.val.1) owned)
  · refine (SiteScatter.idle atSite words s (v.widePacketLowColumn h width a b q) live).trans ?_
    have zero (p : (portGraph K).Port s) : (∑i,active b i) p.val.1=0 := by
      rw [Finsupp.finsetSum_apply]
      refine Finset.sum_eq_zero fun i _=>?_
      have neither:=H.vacant extent tall floor s i (fun u eq=>(live ⟨u,eq⟩).elim) (c' i)
      cases b with
      | false => exact PassMatrix.vacant_width _ s neither.1 p
      | true => exact PassMatrix.vacant_width _ s neither.2.1 p
    exact emptyOwner w (parts.owner q) (fun p => (∑l,active b l) p.val.1) zero

end FundedDate
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
