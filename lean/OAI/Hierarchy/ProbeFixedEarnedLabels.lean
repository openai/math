import OAI.Hierarchy.ProbeFixedEarnedMate
import OAI.Hierarchy.TaggedWireEarnedMeasuredRow

namespace OAI
/-! # The three physical charged operands on an elected occurrence -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native AdaptiveProbe Strip
open CatalogueRows PortPadding StripChart StripDirectory StockCommit CoreBoard
open ThreeFlat.RAM
open scoped Classical Fin.CommRing

namespace CatalogueRows
theorem earned_primary_lt {S : PurchaseSampler} {h d k n w : ℕ} {A B : Type} {b : Board}
    {p : StripPorts S h d k (TreeColumn n) (Fin n) B} {m : Memory w} {reg : Word w}
    {col : TreeColumn n → Columns h d} {extra : A⊕B → DistinctPair (TreeSite n k)}
    {ends : Fin b.rows → Site h d k × Site h d k}
    (placed : EarnedPlacement p b m reg col extra ends)
    (r : ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k) (paid : paidRole r) :
    ((p.primary b r).eval m reg).val<b.rows := by
  obtain ⟨idx,mate,primary,_⟩ := placed.2
  rw [primary r paid]
  exact (idx r).isLt

theorem catalystBit_nonzero {n k w : ℕ} {A B : Type}
    (r : ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k) (wide : 0<w) :
    (catalystBit r:Word w)≠0 ↔ EarnedInstall.usesMate r := by
  have nonzero : (1:Word w)≠0 := by
    intro zero
    have same := congrArg Fin.val zero
    rw [show (1:Word w).val=1 from Fin.val_cast_of_lt (Nat.one_lt_two_pow wide.ne'),Fin.val_zero] at same
    omega
  cases r <;> simp [catalystBit,EarnedInstall.usesMate,nonzero]
end CatalogueRows

namespace FixedProtocolFormat
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owner : Bank)
local notation "sz" => Native.wordBits z (2^v.W) Native.copies
local notation "N" => Stages z (2^v.W)
local notation "n₀" => Fintype.card (PayloadRole N k)
local notation "n₁" => Fintype.card (PurchasedRole v.depth k)
local notation "count" => max n₀ n₁
local notation "cat" => P.catalogue
local notation "format" => v.nativeBoards P z width
local notation "head" => StripChart.header F format
local notation "geo" => v.stamp P z width r banks src tab dst owner
local notation "occ" => v.roleOccurrence P z width
local notation "flag" => v.earnedClass P z width
local notation "mate" => v.earnedMate P z width

theorem payload_earned_labels (phase trial : ℕ) (out : Memory sz)
    (row : Fin (head (.outer phase trial)).rows) (role : PayloadRole N k)
    (hdr : (head (.outer phase trial)).Loaded out) (slots : count≤2^sz) (room : P.catalogue.rows<2^sz) :
    let a:=Attempt.outer phase trial
    let f:=inject (Nat.le_max_left n₀ n₁) (Fintype.equivFin _ role)
    let i:=((occ a row f).val:Word sz)
    let pt:=v.payloadPricePorts P z width
    (geo a).edge.eval out i=(pt.primary cat role).eval out (row.val:Word sz) ∧
      ((flag a).eval out i≠0 ↔ EarnedInstall.usesMate role) ∧
      (mate a).eval out i=(pt.mate cat role).eval out (row.val:Word sz) := by
  intro a f i pt
  obtain ⟨on,second⟩:=v.payload_mate_at P z width phase trial out row role hdr slots room
  exact ⟨v.payload_stamp P z width r banks src tab dst owner phase trial out row role hdr slots room,
    by rw [on];exact catalystBit_nonzero role (by unfold Native.wordBits;omega),second⟩

/-- A paid role has a genuine index in the original earned installation.
The original born bit is inspected only at its retained purchased candidate. -/
theorem purchased_earned_labels (phase trial tick inner : ℕ) (out original : Memory sz)
    (row : Fin (head (.inner phase trial tick inner)).rows) (role : PurchasedRole v.depth k)
    {col : ChainStrip.Columns v.depth → Columns z (2^v.W)}
    {extra : ChainStrip.Axes v.depth k ⊕ Unit → DistinctPair (TreeSite (ChainStrip.edgeCount v.depth) k)}
    {ends : Fin P.catalogue.rows → Site z (2^v.W) k × Site z (2^v.W) k}
    (placed : EarnedPlacement (v.purchasedPricePorts P z width phase trial) cat original
      (row.val:Word sz) col extra ends) (paid : paidRole role)
    (hdr : (head (.inner phase trial tick inner)).Loaded out) (slots : count≤2^sz) (room : P.catalogue.rows<2^sz)
    (cut : ℕ) (low : PrefixAgreement.Low cut out original)
    (fits : ((v.purchasedPricePorts P z width phase trial).primary cat role).Fits sz cut) :
    let a:=Attempt.inner phase trial tick inner
    let f:=inject (Nat.le_max_right n₀ n₁) (Fintype.equivFin _ role)
    let i:=((occ a row f).val:Word sz)
    let pt:=v.purchasedPricePorts P z width phase trial
    (role=.extra (.inr ()) → (retainedAt F format a).eval out i≠0) →
    (geo a).edge.eval out i=(pt.primary cat role).eval out (row.val:Word sz) ∧
      ((flag a).eval out i≠0 ↔ EarnedInstall.usesMate role) ∧
      (mate a).eval out i=(pt.mate cat role).eval out (row.val:Word sz) := by
  intro a f i pt born
  have same : (pt.primary cat role).eval out (row.val:Word sz)=(pt.primary cat role).eval original (row.val:Word sz) :=
    PrefixAgreement.expr _ _ _ _ (PrefixAgreement.inputEnd_of_fits _ fits) low _
  have bound : ((pt.primary cat role).eval out (row.val:Word sz)).val≤P.catalogue.rows := by
    rw [same]
    exact (earned_primary_lt placed role paid).le
  obtain ⟨on,second⟩:=v.purchased_mate_at P z width phase trial tick inner out row role hdr slots room
  exact ⟨v.purchased_stamp P z width r banks src tab dst owner phase trial tick inner out row role
    hdr slots room bound born,by rw [on];exact catalystBit_nonzero role (by unfold Native.wordBits;omega),second⟩

end FixedProtocolFormat
end Hierarchy.ProtocolRAM.Calendar
end

end OAI
