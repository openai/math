import OAI.Hierarchy.ProbeFixedFundedPartyTag
import OAI.Hierarchy.TaggedWireFundedElectedEntry
import OAI.Hierarchy.ProbeFixedWideSparseBallot
import OAI.Hierarchy.ProbeSparsePrintedRows

namespace OAI
/-! # The printed original candidates and the signed parties at a funded attempt -/
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

/-- The place of a selected original candidate and a local party is uniquely
determined by the unpatched prefix and its chosen signed template. -/
def occupiedBallots : ballots ↪ Fin K where
  toFun u := (chosen u).installed.site u.2
  inj' := by
    intro u v' eq
    have same:=H.unique_party extent tall floor u.1.val u.1.property v'.1.property u.2 v'.2 eq
    exact Prod.ext (Subtype.ext same.1) same.2

local notation "atSite" => H.occupiedBallots extent tall floor
local notation "sh" => v.widePacketShape h width (.attempt a)
local notation "orig" => v.wideBallotRows h width r banks source table target owners a (entryMemory C initial a)
local notation "old" => (v.wideBallotShape P h width (.attempt a)).columns
local notation "extra" => ((v.widePacketRoles h*3)*5+(v.widePacketDegree+v.widePacketDegree))
local notation "middle" => PacketTurns.middleColumns (v.widePacketRoles h)
local notation "tagColumn" => ((((0 : Fin (sig+2)).castAdd extra).castAdd (v.wideBallotParties h a)).castAdd middle)
variable (selectorBits siteROM : ℕ) (strideBank : Bank) (preStart postStart : ℕ) (processing : Memory (Native.wordBits h (2^v.W) Native.copies))
local notation "fd" => v.widePacketFields h width selectorBits (.attempt a) siteROM strideBank preStart postStart
local notation "words" => fun (u : ballots) (c : Fin (sh).columns)=>((fd).value u.2 c).eval processing (u.1.val.val:Word w)
private abbrev checkoutWords := checkout

variable (arch : PrefixAgreement.Low ((v.privateArena (v.widePlacement h width) h width).endAddress v.mesh)
      processing (checkoutWords H'))
    (rom : HistoryRoles.RoleROM.Mounted siteROM (SiteDirectory.table h (2^v.W) k) processing)
    (siteRoom : SiteDirectory.size h (2^v.W) k ≤ 2^(Native.wordBits h (2^v.W) Native.copies))
    (namesFit : siteLast h (2^v.W) k+1 ≤ 2^(Native.wordBits h (2^v.W) Native.copies))
    (codes : 1+v.menuCodes (Stages h (2^v.W)) ≤ 2^(Native.wordBits h (2^v.W) Native.copies))
    (tags : v.menuCodes (Stages h (2^v.W))*v.wideBallotParties h a+1 ≤ 2^(Native.wordBits h (2^v.W) Native.copies))

include arch rom siteRoom codes tags in
theorem occupied_tag (u : ballots) :
    (words u tagColumn).val=(v.partyIndex h a (chosen u).atom u.2).val+1 := by
  change (((fd).value u.2 tagColumn).eval processing (u.1.val.val:Word w)).val=_
  have column := v.widePacket_base h width selectorBits siteROM strideBank preStart postStart a u.2 (0 : Fin (sig+2))
  exact (congrArg (fun e : Expr => (e.eval processing (u.1.val.val:Word w)).val) column).trans
    (H.packet_tag_on H' extent tall floor siteROM processing arch rom siteRoom codes tags u.1.val u.1.property u.2).1

include arch rom siteRoom codes tags in
theorem occupied_location (u : ballots) :
    ((fd).site u.2).eval processing (u.1.val.val:Word w)=((atSite u).val:Word w) := by
  rw [v.widePacket_site]
  exact (H.packet_tag_on H' extent tall floor siteROM processing arch rom siteRoom codes tags u.1.val u.1.property u.2).2

include extent tall floor selectorBits siteROM strideBank preStart postStart processing arch in
theorem occupied_iff (i : I) : i∈orig ↔ picked i := by
  have occ : Event.attempt a∈es := by
    change _ ∈ events (C).mesh
    rw [H'.cut.events]
    simp
  let layout:=((H'.readbackRun extent tall floor).boards a occ).1
  have fits:=v.market_rows_fit P h width (dims).strip a
  have native:=v.wide_packet_live_row h width r banks source table target owners siteROM a H'.prior tail initial entry processing
    H'.cut arch layout selectorBits strideBank preStart postStart layout.board fits i root
  rw [v.widePacket_selected] at native
  have flag:=v.wide_ballot_live P h width r banks source table target owners siteROM a H'.prior tail initial entry processing
    H'.cut arch layout.board fits root i
  rw [H'.cut.entryMemory]
  refine native.symm.trans (flag.trans ⟨fun receipt=>(H'.ballot extent i).2.2.mpr receipt.1,fun pickedAt=>?_⟩)
  exact H'.committed_at extent i pickedAt

include arch rom siteRoom namesFit codes tags in
/-- Every column of the replay, including the tag at offset zero. The elected
index set is taken from the common original choice, independently of its counters. -/
theorem production_table (shelfStart : ℕ) (out : Memory w) (printed : printedSiteRows sh K shelfStart fd orig processing out)
    (s : Fin K) (f : Fin (sh).columns) :
    out (shelfStart+1+(SiteScatter.pos s f).val)=SiteScatter.table atSite words s f := by
  obtain ⟨placed,whereAt,posted⟩:=printed
  have iffAt (i : I):=H'.occupied_iff extent tall floor selectorBits siteROM strideBank preStart postStart processing arch i
  let liftRow (u : ballots) : {i : I // i∈orig}×J:= (⟨u.1.val,(iffAt u.1.val).mpr u.1.property⟩,u.2)
  let dropRow (u : {i : I // i∈orig}×J) : ballots:= (⟨u.1.val,(iffAt u.1.val).mp u.1.property⟩,u.2)
  have placeEq (u : ballots) : placed (liftRow u)=atSite u := by
    have first:=whereAt (liftRow u)
    have second:=H.occupied_location H' extent tall floor selectorBits siteROM strideBank preStart postStart processing arch rom siteRoom codes tags u
    have digits:=congrArg Fin.val (first.symm.trans second)
    apply Fin.ext
    simpa only [Fin.val_cast_of_lt ((placed (liftRow u)).isLt.trans_le namesFit),Fin.val_cast_of_lt ((atSite u).isLt.trans_le namesFit)] using digits
  let emitted (u : {i : I // i∈orig}×J) (j : Fin (sh).columns) :=
    ((fd).value u.2 j).eval processing (u.1.val.val:Word w)
  rw [posted]
  by_cases active : s∈Set.range atSite
  · obtain ⟨u,rfl⟩:=active
    calc
      _ = SiteScatter.table placed emitted (placed (liftRow u)) f :=
        congrArg (fun z => SiteScatter.table placed emitted z f) (placeEq u).symm
      _ = emitted (liftRow u) f := SiteScatter.active placed emitted (liftRow u) f
      _ = _ := (SiteScatter.active atSite words u f).symm
  · have vacant : s∉Set.range placed := by
      rintro ⟨u,eq⟩
      exact active ⟨dropRow u,(placeEq (dropRow u)).symm.trans eq⟩
    rw [SiteScatter.idle _ _ _ _ vacant,SiteScatter.idle _ _ _ _ active]

include arch rom siteRoom namesFit codes tags in
/-- The native mode has its dense site/column address in site-major order. -/
theorem production_word (shelfStart : ℕ) (out : Memory w) (printed : printedSiteRows sh K shelfStart fd orig processing out)
    (s : Fin K) (f : Fin (sh).columns) :
    out (shelfStart+1+s.val*(sh).columns+f.val)=SiteScatter.table atSite words s f := by
  have native:=H.production_table H' extent tall floor selectorBits siteROM strideBank preStart postStart processing arch rom
    siteRoom namesFit codes tags shelfStart out printed s f
  have number : (SiteScatter.pos s f).val=s.val*(sh).columns+f.val := by
    simp [SiteScatter.pos,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
  simpa only [number,Nat.add_assoc] using native

/-- A row other than the selected packet at a site contributes the scalar one. -/
theorem vacant (s : Fin K) (i : I) (off : ∀u : ballots,atSite u=s→u.1.val≠i)
    (hist : Histogram (Fin ((fmt).letters a x i)) ((fmt).copies a x i)) :
    Subsingleton (State ((H.row extent tall floor i).input) s) ∧
    Subsingleton (State ((H.tender extent tall floor i).post hist) s) ∧
    ∀x y,(H.tender extent tall floor i).entry hist s x y=1 := by
  by_cases live : picked i
  · exact H.elected_away extent tall floor i live hist s (fun j eq=>off (⟨i,live⟩,j) eq rfl)
  · exact H.unelected extent tall floor i live hist s

end FundedDate
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
