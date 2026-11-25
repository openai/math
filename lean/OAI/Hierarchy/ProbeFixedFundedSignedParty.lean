import OAI.Hierarchy.ProbeFixedElectedPartyRead
import OAI.Hierarchy.ProbeFixedFundedHistCounter
import OAI.Hierarchy.ProbeFixedFundedSocket
import OAI.Hierarchy.TaggedWideCalendarPartyWords

namespace OAI
/-! # The signed matrix entry at a genuinely occupied original ballot site -/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 3600000
set_option cleanup.letToHave false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets
open PurchaseStage WireTelescope Tagged ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "w" => Native.wordBits h D Native.copies
local notation "C" => v.wideSignedChart h width (v.fixedTerminalStock P h width)
variable (size : ℕ) (π : Equiv.Perm (Fin (2^h))) (seed : Boot.Tape h (2^v.W))
    (age : v.wideStockHeight≤h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
local notation "reader" => v.wideSelector h width age budget small
local notation "origin" b:arg => v.wideOrigin h width size ((reader).format.windows.header (events v.mesh) b seed) π

open StripDirectory
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat.Diagonal.MotifOuterTerms
open WireTelescope.ChosenPackets WireTelescope.PacketTurns WireTelescope.PacketNeighbor HistoryRoles

namespace FundedDate
variable {v h width size π seed age budget small}
variable {a : Attempt} {tail : List Event} {x : Memory (Native.wordBits h (2^v.W) Native.copies)}
    {t : CalendarTape.Prefix (v.wideSelector h width age budget small).format.slot (events v.mesh)
      (v.wideOrigin h width size seed π) (.attempt a::tail) x} {c : ((v.wideSelector h width age budget small).format.slot (.attempt a)).choice x}
    (H : v.FundedDate h width size π seed age budget small t c)
    (extent : (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh ≤ size) (tall : v.ballotHeight≤h) (floor : v.widthFloor≤width)

local notation "batch" => enabledBatch ((C).layout a) (repair C a)
local notation "fmt" => (reader).format
local notation "root" => v.wideBallotRoot h a
local notation "K" => siteLast h D k+1
variable (i : Fin ((v.wideSignedChart h width (v.fixedTerminalStock (v.widePlacement h width) h width)).layout a).candidates)
local notation "u" proof:arg => H.packetAt extent tall floor i proof

local notation "left" => H.row extent tall floor i
local notation "right" => H.tender extent tall floor i

variable (hit :
    let chart := v.wideSignedChart h width (v.fixedTerminalStock (v.widePlacement h width) h width)
    (enabledBatch (chart.layout a) (repair chart a)).selected (HistogramShelf.snapshot chart a x)
      (i.val : Word (Native.wordBits h (2^v.W) Native.copies)))
local notation "Q" => (u hit).menu root
local notation "chosen" => (u hit).installed
local notation "demand" => fun l=> (H.row extent tall floor l).input
local notation "J" => v.wideBallotParties h a
local notation "deg" => v.widePacketDegree

local notation "pad" => publicChord h D k
local notation "raw" elect:arg => (u elect).route root pad
local notation "G" => Commodity (Fin (2^h)) N k
open scoped BigOperators
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open WireTelescope.PassMatrix PartyPins
open ThreeFlat.Routing
variable {c' : ((v.wideSelector h width age budget small).format.slot (.attempt a)).choice x} (H' : v.FundedDate h width size π seed age budget small t c')
    (unitCost siteROM selectorBits : ℕ) (stride : Bank) (preStart postStart : ℕ) (out : Memory (Native.wordBits h (2^v.W) Native.copies))
    (j : Fin ((H.packetAt extent tall floor i hit).menu (v.wideBallotRoot h a)).sites) {V : Type} [Fintype V] (env : V→Bool) (read : ℕ→ℕ→V⊕Bool)
local notation "nj" z:arg => (z : Fin (Q).sites).cast ((chosen).parties (u hit).atom root)
local notation "site" => (Q).place j
local notation "cap" => v.wideNeighborCap width unitCost
local notation "before" => ∑l,demand l
local notation "offer" => fun l=>(H.tender extent tall floor l).post (c' l)
local notation "after" => ∑l,offer l
local notation "party" => v.wideBallotSite P h width siteROM a (nj j)
local notation "fd" => v.widePacketFields h width selectorBits (.attempt a) siteROM stride preStart postStart
local notation "sh" addr:arg f:arg => DatedRoleSheets.bank (v.widePacketPhysical h width) addr (v.widePacketShelf h) selectorBits f
local notation "page" start:arg f:arg => pageRead (sh start f) stride party (d:=deg)
local notation "final" => checkedOut C ((A).endAddress v.mesh) (origin H'.code)
local notation "fetch" n:arg b:arg => Sum.elim env id (read n b)
local notation "beforeBits" parts_:arg state_:arg => Function.uncurry (ChordAperture.canonical parts_ (fun p d=>(state_ p).val.testBit d))
local notation "afterBits" parts_:arg state_:arg => Function.uncurry (ChordAperture.canonical parts_ (fun p d=>(state_ p).val.testBit d))
local notation "socketInput" rest_:arg old_:arg => blockPortState demand site ((splitPortState rest_ before site old_).2) i
local notation "socketOutput" rest_:arg new_:arg => blockPortState offer site ((splitPortState rest_ after site new_).2) i

private theorem spent_below_socket {S count : ℕ} (residual : Widths S) (offered : Fin count → Widths S)
    (pick : Fin count) (bound : ℕ) (budget : ∀ e, (residual + ∑ t, offered t) e ≤ bound)
    (edge : Chord S) : offered pick edge ≤ bound := by
  have one : offered pick edge ≤ (∑ l, offered l) edge := by
    simpa only [Finsupp.finsetSum_apply] using
      (Finset.single_le_sum (s:=Finset.univ) (f:=fun l=>offered l edge)
        (fun _ _=>Nat.zero_le _) (Finset.mem_univ pick))
  exact one.trans ((Nat.le_add_left ..).trans (budget edge))

attribute [local irreducible] FundedDate.packetAt wideStockHeight widePlacement wideSignedWords
  siteNumber permutationFabric ProbeStage.rounds ElectedSource.site TypedWiring.value signedPartyAt
  widePacketFields DatedRoleSheets.bank

theorem signed_party_entry (rest : Widths K) (old : State (rest+before) site) (new : State (rest+after) site)
    (l : PassiveWindow.Parts ((portGraph K).Port site) (Fin deg) cap (fun p=>(rest+before) p.val.1))
    (r' : PassiveWindow.Parts ((portGraph K).Port site) (Fin deg) cap (fun p=>(rest+after) p.val.1))
    (arch : PrefixAgreement.Low ((A).endAddress v.mesh) out final)
    (rom : HistoryRoles.RoleROM.Mounted siteROM (SiteDirectory.table h D k) out)
    (siteRoom : SiteDirectory.size h D k≤2^w) (namesFit : K≤2^w)
    (rowsFit : Fintype.card G+(P).catalogue.rows≤2^w) (degreeFit : deg<2^w)
    (codes : 1+v.menuCodes N≤2^w) (tags : v.menuCodes N*J+1≤2^w)
    (word : v.PartyWordBounds h width unitCost)
    (preFit : ∀q : (portGraph K).Port site,(rest+before) q.val.1≤cap)
    (postFit : ∀ e : Chord K,(rest+after) e≤cap)
    (earlier : NeighborReads out (i.val:Word w) l (page preStart 0) (page preStart 2))
    (later : NeighborReads out (i.val:Word w) r' (page postStart 0) (page postStart 2))
    (field : ∀ (f : Fin (v.widePacketShape h width (.attempt a)).columns) (d : ℕ),fetch f.val d=(((fd).value (nj j) f).eval out (i.val:Word w)).val.testBit d) :
    TypedWiring.value (F := F) («P» := PassMatrix.Gathered V deg cap) (v.signedPartyAt h width a cap (v.partyRoleBits h) (v.partyLaneBits h width a unitCost)
      v.partyKeyBits read (u hit).atom (nj j)) (Sum.elim (Sum.elim env (beforeBits l old)) (afterBits r' new))=(right).entry (c' i) site (socketInput rest old) (socketOutput rest new) := by
  let readings := FundedDate.packet_reads_on (v := v) (h := h) (width := width) (size := size) (π := π) (seed := seed)
    (age := age) (budget := budget) (small := small) (a := a) (tail := tail) (x := x) (t := t) (c := c) (c' := c') H H' extent tall floor siteROM out arch rom siteRoom namesFit i hit
  let arity := readings.choose
  let mass := readings.choose_spec.choose
  have amounts := readings.choose_spec.choose_spec
  let hist:=cast (congrArg₂ (fun n b=>Histogram (Fin n) b) arity mass) (c' i)
  let elected := FundedDate.elected_entry (v := v) (h := h) (width := width) (size := size) (π := π) (seed := seed)
    (age := age) (budget := budget) (small := small) (a := a) (tail := tail) (x := x) (t := t) (c := c) H extent tall floor i hit (c' i)
  let shapes := elected.choose_spec.choose_spec
  let entryShape := shapes.choose
  let exitShape := shapes.choose_spec.choose
  have rowEq := shapes.choose_spec.choose_spec
  have atSite : (party).eval out (i.val:Word w)=((site).val:Word w) := by
    rw [H.socket_party extent tall floor i hit j]
    exact (H.packet_tag_on H' extent tall floor siteROM out arch rom siteRoom codes tags i hit (nj j)).2
  have restOf (l') (ne : l'≠i) : Subsingleton (State (offer l') site) := by
    rw [H.socket_party extent tall floor i hit j]
    exact (H.away_from_party extent tall floor l' hit (nj j) ne (c' l')).2.1
  have paid (e) : (raw hit).post hist e≤2^(v.partyLaneBits h width a unitCost) := by
    exact (congrArg (fun d : Widths K => d e) exitShape.symm).le.trans
      ((spent_below_socket rest offer i cap postFit e).trans (v.party_lane_room h width a unitCost).1.le)
  have native:=(chosen).selected_value (u hit).atom root pad siteROM unitCost selectorBits stride
    preStart postStart (nj j) read env out (i.val:Word w) hist rest offer i r' (beforeBits l old) (afterBits r' new) exitShape restOf
    (cast (congrArg (fun Z=>State Z site) entryShape) (socketInput rest old)) new amounts atSite namesFit rowsFit later
    field word.role (word.lane a) paid (fun q=>postFit _) (fun _ _=>rfl)
    (signedKey (Q).place j l v.party_key_room)
  have reevaluate := congrArg (fun matrix : SiteMatrix (State (left).input) (State ((right).post (c' i))) F =>
    matrix site (socketInput rest old) (socketOutput rest new)) rowEq
  have transported := FundedDate.transport_at entryShape.symm exitShape.symm ((raw hit).entry hist)
    site (socketInput rest old) (socketOutput rest new)
  refine Eq.trans ?_ (reevaluate.trans transported).symm
  apply native
  · intro k' d
    exact H.wanted_key_bit (H':=H') (extent:=extent) (tall:=tall) (floor:=floor) (i:=i) (hit:=hit)
      (siteROM:=siteROM) (selectorBits:=selectorBits) (preStart:=preStart) (postStart:=postStart)
      (strideBank:=stride) (out:=out) (arch:=arch) (rom:=rom) (siteRoom:=siteRoom) (namesFit:=namesFit)
      (codes:=codes) (tags:=tags) (j:=j) (parts:=l) (actual:=earlier)
      v.party_key_room degreeFit k' d (fun n b=>fetch n b) field
  · intro a' d
    exact H.hist_bit H' extent tall floor siteROM selectorBits stride preStart postStart out arch i hit
      (nj j) arity mass a' d (fun x b=>fetch x b) field
  · intro t d
    exact H.wanted_socket_entry extent tall floor i hit rest j l v.party_key_room preFit old entryShape t d

end FundedDate
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
