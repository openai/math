import OAI.Hierarchy.TaggedWireElectedOperands
import OAI.Hierarchy.TaggedWireFundedEarnedAgreement
import OAI.Hierarchy.TaggedWireFundedBranchWord
import OAI.Hierarchy.TaggedWireFundedBallots

namespace OAI
/-! # One reference packet gate evaluated on every genuine histogram branch -/
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
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
local notation "slots" => max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k))
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

open StripDirectory
local notation "slab" => v.slab (v.seed P h width) P width

open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open WireTelescope.ChosenPackets WireTelescope.PacketTurns

theorem castCounter {n W q l b : ℕ} (letters mass : Fin n→ℕ) (choice : BallChoices letters mass)
    (room : ∀i,mass i<2^W) (i : Fin n) (arity : letters i=l) (copies : mass i=b)
    (fit : l≤q) (j : Fin l) :
    counterRows letters mass choice room i (⟨j.val,j.isLt.trans_le fit⟩ : Fin q)=
      (((cast (congrArg₂ (fun a c=>Histogram (Fin a) c) arity copies) (choice i)).val j).val:Word W) := by
  subst l b
  apply Fin.ext
  simp only [counterRows,dite_eq_left j.isLt,cast_eq]
  exact (Fin.val_cast_of_lt ((Nat.lt_succ_iff.mp ((choice i).val j).isLt).trans_lt (room i))).symm

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

theorem packet_reads_on (extent : (A).endAddress v.mesh≤ size) (tall : v.ballotHeight≤h)
    (floor : v.widthFloor≤width) (siteROM : ℕ) (out : Memory w)
    (arch : PrefixAgreement.Low ((A).endAddress v.mesh) out checkout)
    (rom : HistoryRoles.RoleROM.Mounted siteROM (SiteDirectory.table h D k) out)
    (siteRoom : SiteDirectory.size h D k≤2^w) (room : K≤2^w)
    (i : Fin ((C).layout a).candidates) (pick : (batch).selected snap (i.val:Word w)) :
    let u:=H.packetAt extent tall floor i pick
    let T:=u.route root (publicChord h D k)
    let terms:=(fmt).letters a x i
    let copies:=(fmt).copies a x i
    ∃(arity : terms=(u.menu root).data.terms) (mass : copies=(batch).copies),
      let hist:=cast (congrArg₂ (fun l b=>Histogram (Fin l) b) arity mass) (c' i)
      Reads (Installs.starts («source»:=T.source) T.order) shape (T.install.steps T.order)
        (Installs.numbered T.order (T.bits hist)) (u.installed.operands u.atom root (publicChord h D k) siteROM) out (i.val:Word w) := by
  let : Nonempty (Fin k) := ⟨⟨0, v.positive⟩⟩
  intro u T terms copies
  let old:=(v.funded_ballot_views h width size extent π seed age budget small t c).1
  have arity : terms=(u.menu root).data.terms:=(old.1 i).trans (u.arity root).symm
  have mass : copies=(batch).copies:=(old.2 i).trans (ite_eq_left pick)
  refine ⟨arity,mass,?_⟩
  let hist:=cast (congrArg₂ (fun l b=>Histogram (Fin l) b) arity mass) (c' i)
  let cutAddress:=(A).base v.mesh (.attempt a)
  have occ : Event.attempt a∈es:=by
    change _ ∈ events (C).mesh
    rw [H'.cut.events]
    simp
  have before : cutAddress≤(A).endAddress v.mesh:=(Nat.le_add_right ..).trans ((A).within v.mesh _ occ)
  have lowAgree : PrefixAgreement.Low cutAddress out (checkedOut C ((A).endAddress v.mesh) (origin H.code)) :=
    fun z hz=>(arch z (hz.trans_le before)).trans ((H.checkout_agree H') z hz).symm
  let run':=H'.readbackRun extent tall floor
  have layout:=(run'.boards a occ).1
  have active:=H'.committed_at extent i pick
  have cols:=(Classical.choose_spec (Filter.eventually_atTop.1 v.wide_face_room) h
    (max_le_iff.mp (max_le_iff.mp tall).2).2).1
  have bounds:=v.wide_earned_before h width a (before.trans_lt (dims).words.addresses)
  have code : 1+v.menuCodes N≤2^w:=by
    rw [show N = publicStages v.W from fixed_stage_count h v.W]
    have threshold : v.stripPorts (publicStages v.W)+v.menu.alphabet+(1+v.menuCodes (publicStages v.W))+v.menu.maximum ≤ h :=
      (le_max_left ..).trans (dims).strip
    exact (show 1+v.menuCodes (publicStages v.W)≤h by omega).trans
      ((Nat.lt_two_pow_self (n:=h)).le.trans (v.date_prefix_fit h).le)
  have lanes : (u.menu root).data.terms≤ sig:=arity ▸ (fmt).width a x i
  apply u.installed.reads u.atom root (publicChord h D k) siteROM hist out cutAddress lowAgree (by cases a <;> exact bounds) rom siteRoom cols room code lanes
  · have raw:=v.wide_ballot_code P h width r banks source table target owners siteROM a H'.prior tail initial entry out
      H'.cut arch layout.board (v.market_rows_fit P h width (dims).strip a) root i
    have raw' := raw.trans (ite_eq_left active)
    exact (congrArg Fin.val raw').trans ((congrArg Fin.val (H'.ballot extent i).1).symm.trans u.nativeCode)
  · intro j
    have val:=v.wide_ballot_chosen P h width r banks source table target owners siteROM a H'.prior tail initial entry out
      H'.cut arch (dims).words.addresses (dims).copies root i (⟨j.val,j.isLt.trans_le lanes⟩:Fin sig) x c' H'.ballot_word
    exact val.trans (castCounter ((fmt).letters a x) ((fmt).copies a x) c' ((fmt).count a x) i arity mass lanes j)

end FundedDate
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
