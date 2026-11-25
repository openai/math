import OAI.Hierarchy.TaggedWireFundedElectedEntry
import OAI.Hierarchy.ProbeFixedFundedPartyTag
import OAI.Hierarchy.ProbeFixedWideSocketWords

namespace OAI
/-! # The genuine dated signed input at each elected party, after the full before-state gather -/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
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

theorem socket_party (j : Fin (Q).sites) : (Q).place j=(chosen).site (j.cast ((chosen).parties (u hit).atom root)) := by
  let same := (chosen).parties (u hit).atom root
  have roundtrip : j = (j.cast same).cast same.symm := Fin.ext rfl
  exact (congrArg (fun l => (Q).place l) roundtrip).trans
    ((chosen).placed_site (u hit).atom root (j.cast same))

theorem socket_shape : (left).input=Probe.placeWidths (Q).place ((Q).data.inputWidths (batch).copies) := by
  let _ : Nonempty (Fin k) := ⟨⟨0, v.positive⟩⟩
  let view:=(v.funded_ballot_views h width size extent π seed age budget small t c).1
  exact ((fmt).electedRow_source a x x view (fun l sel => (H.packetAt extent tall floor l sel).menu root)
    (fun l sel => (H.packetAt extent tall floor l sel).arity root) i hit).trans (Q).placedInput.symm

theorem wanted_socket (rest : Widths K) (j : Fin (Q).sites) {cap keyBits socketCap : ℕ}
    (parts : PassiveWindow.Parts ((portGraph K).Port ((Q).place j)) (Fin deg) cap
      (fun p=>(rest+∑l,demand l) p.val.1))
    (wide : deg<2^keyBits) (room : ∀t : (portGraph K).Port ((Q).place j),(rest+∑l,demand l) t.val.1≤cap)
    (old : State (rest+∑l,demand l) ((Q).place j)) (port : (portGraph (Q).sites).Port j) (b : Fin socketCap) :
    let physical:=blockPortState demand ((Q).place j) ((splitPortState rest (∑l,demand l) ((Q).place j) old).2) i
    let shape:=H.socket_shape extent tall floor i hit
    let gather:=Function.uncurry (ChordAperture.canonical parts (fun p d=>(old p).val.testBit d))
    Sum.elim gather id (wantedSocket ((Q).data.inputWidths (batch).copies) j (signedKey (Q).place j parts wide) id port b)=
      ((PhysicalMatrix.read (Q).place ((Q).data.inputWidths (batch).copies) j (cast (congrArg (fun U=>State U ((Q).place j)) shape) physical)) port).val.testBit b.val := by
  have others (l) (off : l≠i) : Subsingleton (State (demand l) ((Q).place j)) := by
    rw [H.socket_party extent tall floor i hit j]
    exact (H.away_from_party extent tall floor l hit _ off (c l)).1
  exact selected_socket (Q).place j ((Q).data.inputWidths (batch).copies) rest demand i (H.socket_shape extent tall floor i hit)
    others parts wide room old port b

private theorem input_twice {S : ℕ} {U V Z : Widths S} (s : Fin S) (h₁ : U=V) (h₂ : V=Z)
    (x : State U s) : cast (congrArg (fun T=>State T s) h₂) (cast (congrArg (fun T=>State T s) h₁) x)=
      cast (congrArg (fun T=>State T s) (h₁.trans h₂)) x := by subst V Z; rfl

/-- The same socket on the state already transported by `H.elected_entry`. -/
theorem wanted_socket_entry (rest : Widths K) (j : Fin (Q).sites) {cap keyBits socketCap : ℕ}
    (parts : PassiveWindow.Parts ((portGraph K).Port ((Q).place j)) (Fin deg) cap (fun p=>(rest+∑l,demand l) p.val.1))
    (wide : deg<2^keyBits) (room : ∀t : (portGraph K).Port ((Q).place j),(rest+∑l,demand l) t.val.1≤cap)
    (old : State (rest+∑l,demand l) ((Q).place j)) (input : (left).input=(Q).wants (batch).copies)
    (port : (portGraph (Q).sites).Port j) (bit : Fin socketCap) :
    let physical:=blockPortState demand ((Q).place j) ((splitPortState rest (∑l,demand l) ((Q).place j) old).2) i
    let x:=cast (congrArg (fun U=>State U ((Q).place j)) input) physical
    let gather:=Function.uncurry (ChordAperture.canonical parts (fun p d=>(old p).val.testBit d))
    Sum.elim gather id (wantedSocket ((Q).data.inputWidths (batch).copies) j (signedKey (Q).place j parts wide) id port bit)=
      ((PhysicalMatrix.read (Q).place ((Q).data.inputWidths (batch).copies) j (cast (congrArg (fun U=>State U ((Q).place j)) (Q).placedInput.symm) x)) port).val.testBit bit.val := by
  dsimp only
  rw [input_twice ((Q).place j) input (Q).placedInput.symm]
  exact H.wanted_socket extent tall floor i hit rest j parts wide room old port bit

variable {c' : ((v.wideSelector h width age budget small).format.slot (.attempt a)).choice x} (H' : v.FundedDate h width size π seed age budget small t c')
    (siteROM selectorBits preStart postStart : ℕ) (strideBank : Bank) (out : Memory (Native.wordBits h (2^v.W) Native.copies))
local notation "final" => checkedOut C ((A).endAddress v.mesh) (origin H'.code)
local notation "party" => v.wideBallotSite P h width siteROM a
local notation "fd" => v.widePacketFields h width selectorBits (.attempt a) siteROM strideBank preStart postStart
local notation "offset" => (v.wideBallotShape P h width (.attempt a)).columns+((v.widePacketRoles h*3)*5+(deg+deg))
local notation "shelf" => DatedRoleSheets.bank (v.widePacketPhysical h width) preStart (v.widePacketShelf h) selectorBits
local notation "nativeParty" j:arg => (j : Fin (Q).sites).cast ((chosen).parties (u hit).atom root)

theorem wanted_key
    (arch : PrefixAgreement.Low ((A).endAddress v.mesh) out final)
    (rom : HistoryRoles.RoleROM.Mounted siteROM (SiteDirectory.table h D k) out)
    (siteRoom : SiteDirectory.size h D k≤2^w) (namesFit : K≤2^w)
    (codes : 1+v.menuCodes N≤2^w) (tags : v.menuCodes N*J+1≤2^w)
    (j : Fin (Q).sites) {cap keyBits : ℕ} {total : (portGraph K).Port ((Q).place j)→ℕ}
    (parts : PassiveWindow.Parts ((portGraph K).Port ((Q).place j)) (Fin deg) cap total)
    (actual : NeighborReads out (i.val:Word w) parts (pageRead (shelf 0) strideBank (party (nativeParty j)))
      (pageRead (shelf 2) strideBank (party (nativeParty j))))
    (wide : deg<2^keyBits) (full : deg<2^w) (opposite : Fin (Q).sites) (bit : Fin keyBits) :
    (((fd).value (nativeParty j) ((Fin.natAdd offset (nativeParty opposite)).castAdd (PacketTurns.middleColumns (v.widePacketRoles h)))).eval
      out (i.val:Word w)).val.testBit bit.val=(signedKey (Q).place j parts wide opposite).val.testBit bit.val := by
  have recorded := (FundedDate.packet_tag_on
    (v := v) (h := h) (width := width) (size := size) (π := π) (seed := seed)
    (age := age) (budget := budget) (small := small) (a := a) (tail := tail)
    (x := x) (t := t) (c := c) (c' := c')
    H H' extent tall floor siteROM out arch rom siteRoom codes tags i hit (nativeParty opposite)).2
  have located : (party (nativeParty opposite)).eval out (i.val : Word w) =
      (((Q).place opposite).val : Word w) :=
    recorded.trans (congrArg (fun site : Fin K => (site.val : Word w))
      (FundedDate.socket_party (v := v) (h := h) (width := width) (size := size)
        (π := π) (seed := seed) (age := age) (budget := budget) (small := small)
        (a := a) (tail := tail) (x := x) (t := t) (c := c)
        H extent tall floor i hit opposite).symm)
  have socketKey := congrArg (fun e : Expr => e.eval out (i.val : Word w))
    (v.widePacket_socket h width selectorBits siteROM strideBank preStart postStart a (nativeParty j) (nativeParty opposite))
  have readKey := key_read parts _ _ out (i.val : Word w) actual
    (party (nativeParty opposite)) ((Q).place opposite) namesFit located
  exact (congrArg (fun word : Word w => word.val.testBit bit.val) (socketKey.trans readKey)).trans
    (congrArg (fun n : ℕ => n.testBit bit.val) (Fin.val_cast_of_lt ((index_le parts ((Q).place opposite)).trans_lt full)))

/-- The numeric field address used by the signed finite menu program reaches the
same socket key after the ballot has been replayed at its elected site. -/
theorem wanted_key_bit
    (arch : PrefixAgreement.Low ((A).endAddress v.mesh) out final)
    (rom : HistoryRoles.RoleROM.Mounted siteROM (SiteDirectory.table h D k) out)
    (siteRoom : SiteDirectory.size h D k≤2^w) (namesFit : K≤2^w)
    (codes : 1+v.menuCodes N≤2^w) (tags : v.menuCodes N*J+1≤2^w)
    (j : Fin (Q).sites) {cap keyBits : ℕ} {total : (portGraph K).Port ((Q).place j)→ℕ}
    (parts : PassiveWindow.Parts ((portGraph K).Port ((Q).place j)) (Fin deg) cap total)
    (actual : NeighborReads out (i.val:Word w) parts (pageRead (shelf 0) strideBank (party (nativeParty j)))
      (pageRead (shelf 2) strideBank (party (nativeParty j))))
    (wide : deg<2^keyBits) (full : deg<2^w) (opposite : Fin (Q).sites) (bit : Fin keyBits)
    (fetch : ℕ→ℕ→Bool) (read : ∀(f : Fin (v.widePacketShape h width (.attempt a)).columns) (d : ℕ),
      fetch f.val d=(((fd).value (nativeParty j) f).eval out (i.val:Word w)).val.testBit d) :
    fetch (offset+opposite.val) bit.val=(signedKey (Q).place j parts wide opposite).val.testBit bit.val := by
  let col := (Fin.natAdd offset (nativeParty opposite)).castAdd (PacketTurns.middleColumns (v.widePacketRoles h))
  exact (read col bit.val).trans (FundedDate.wanted_key
    (v := v) (h := h) (width := width) (size := size) (π := π) (seed := seed)
    (age := age) (budget := budget) (small := small) (a := a) (tail := tail) (x := x)
    (t := t) (c := c) (c' := c') (H := H) (H' := H') (extent := extent)
    (tall := tall) (floor := floor) (i := i) (hit := hit)
    (siteROM := siteROM) (selectorBits := selectorBits) (preStart := preStart) (postStart := postStart)
    (strideBank := strideBank) (out := out) (arch := arch) (rom := rom) (siteRoom := siteRoom)
    (namesFit := namesFit) (codes := codes) (tags := tags) (j := j) (parts := parts)
    (actual := actual) wide full opposite bit)

end FundedDate
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
