import OAI.Hierarchy.ProbeFixedWideSettlement
import OAI.Hierarchy.ProtocolRAMCatalystMasterUpper
import OAI.Hierarchy.TaggedWireRoleFiniteBoot

namespace OAI
/-! # Signed roles on the same initial tape as the charged physical calendar -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires
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
  (max (Fintype.card (StripDirectory.PayloadRole N k)) (Fintype.card (StripDirectory.PurchasedRole v.depth k)))*2^h


/-- All root permutation entries in the actual charged tape have their prescribed values. -/
theorem wide_signed_words_authentic (stock : Bank) (M : ℕ) (π : Equiv.Perm (Fin (2^h))) (o : Orders h D k)
    (raw : Boot.Tape h D) (i : Fin (2^h)) :
    v.wideSignedWords h width stock M π o raw i.val=((π i).val:Word w) := by
  unfold wideSignedWords
  apply chargedMasterWords_authentic
  exact (v.wideGeometryPrefix h width).1

/-- Construction of the actual charged tape leaves every high raw input word intact. -/
theorem wide_signed_words_above (stock : Bank) (M : ℕ) (π : Equiv.Perm (Fin (2^h))) (o : Orders h D k)
    (raw : Boot.Tape h D) (x : ℕ) (wordRoom : (A).first<2^w) (above : (A).first≤x) :
    v.wideSignedWords h width stock M π o raw x=raw x := by
  let : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
  let : Nonempty (StripDirectory.PurchasedRole v.depth k) := ⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩
  have endAt:=v.catalyst_static_end P h width A
  have ord : (E).Ordered:=economic_ordered F (v.sized (v.seed P h width) width) v.cost v.mesh (P).joint
    (P).catalogue (P).routes v.finish (v.basePhase width) v.digitRadix v.digitRadix v.precision v.precision
  unfold wideSignedWords
  apply chargedMasterWords_above (ord:=ord) (firstCharge:=rfl) (secondCharge:=rfl) (reserveBase:=rfl)
    (space:=allocated_space _ _ _ _ _ _ _ (endAt.le.trans_lt wordRoom))
    (tail:=v.reserve_before_catalystStaticStart P h width) (first:=(v.wideGeometryPrefix h width).1)
    (scoreEnd:=le_rfl) (board:=(v.wideGeometryPrefix h width).2.2)
  exact endAt.le.trans above

/-- The genuine CT program on the finite charged master tape preserves every high
signed word, from the end of the calendar to the last included input cell. -/
theorem wide_signed_boot_above (stock : Bank) (M : ℕ) (π : Equiv.Perm (Fin (2^h))) (o : Orders h D k)
    (raw : Boot.Tape h D) (size : ℕ) (fits : (A).endAddress v.mesh ≤ size) (room : (A).first<2^w) :
    let markets:=v.catalystMarkets P h width
    let words:=v.wideSignedWords h width stock M π o raw
    let m:=Boot.booted markets size words
    (Native.subdivisionProgram h D).Exec (Boot.initial markets size words) m (Native.subdivisionConstant D*2^h) ∧
      ∀x,(A).endAddress v.mesh≤x → x<size → m x=raw x := by
  intro markets words m
  have layout:=v.catalyst_market_layout P h width (v.wideGeometryPrefix h width).2.1
  have run:=Boot.start markets (layout.extend fits) (Nat.two_pow_pos _) π words
    (v.wide_signed_words_authentic h width stock M π o raw)
  refine ⟨run.1,?_⟩
  intro x above included
  exact (run.2.high included (layout.subdivision.trans above) (fun j=>(layout.extent j).trans above)).trans
    (v.wide_signed_words_above h width stock M π o raw x room ((Nat.le_add_right ..).trans above))

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
