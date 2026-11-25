import OAI.Hierarchy.TaggedWireGuardedPortRead
import OAI.Hierarchy.ProbeFixedPrintedRole
import OAI.Hierarchy.ProbeFixedFailureWords

namespace OAI
/-! # Original stamped physical edge at each fixed ballot's public row and role -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open StripChart StripDirectory CatalogueRows StockCommit PortPadding
open ThreeFlat.RAM DescriptorExpr
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owner : Bank)
local notation "N" => Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "n₀" => Fintype.card (PayloadRole N k)
local notation "n₁" => Fintype.card (PurchasedRole v.depth k)
local notation "D" => max n₀ n₁
local notation "bs" => v.nativeBoards P z width
local notation "H" => StripChart.header F bs
local notation "geo" => v.stamp P z width r banks src tab dst owner
local notation "occ" => v.roleOccurrence P z width

/-- Decode the actual edge used by the dated payment pass at the original
public occurrence. The lookup, native addition of idBase and subtraction
are performed at the same physical register. -/
theorem stamp_at_role (a : Attempt) (m : Memory W) (j : Fin (H a).rows) (f : Fin D)
    (header : (H a).Loaded m) (size : D≤2^W) :
    let o := occ a j f
    (geo a).edge.eval m (o.val:Word W)=
      (physicalEdge P.catalogue (retainedAt F bs a) (edge F bs P.catalogue.rows a f)).eval m (o.val:Word W) := by
  intro o
  have field : (H a).fieldTerm.eval m (o.val : Word W) = (f.val : Word W) :=
    (StripDirectory.header_pair (H a) m header j f).2
  have hit : ((H a).fieldTerm.eval m (o.val : Word W)).val = f.val :=
    (congrArg Fin.val field).trans (Fin.val_cast_of_lt (f.isLt.trans_le size))
  have selected := eval_chooseField D 0 (StripChart.id F bs P.catalogue a) (H a).fieldTerm
    m (o.val : Word W) f (by simpa only [Nat.zero_add] using size)
    (by simpa only [Nat.zero_add] using hit)
  exact (congrArg (fun x : Word W => x - (P.catalogue.idBase : Word W)) selected).trans
    (StripChart.actual_id F bs P.catalogue a f m (o.val : Word W))

private theorem source_role (a : Attempt) (m : Memory W) (j : Fin (H a).rows) (f : Fin D)
    (header : (H a).Loaded m) :
    (edge F bs P.catalogue.rows a f).eval m ((occ a j f).val:Word W)=(rawEdge bs P.catalogue.rows a f).eval m (j.val:Word W) := by
  change ((rawEdge bs P.catalogue.rows a f).atRow (H a).ballTerm).eval m _=_
  rw [eval_atRow]
  exact congrArg ((rawEdge bs P.catalogue.rows a f).eval m) (StripDirectory.header_pair (H a) m header j f).1

private theorem guarded_read {w : ℕ} (board : CatalogueRows.Board) (keep operand : Expr)
    (m : Memory w) (row value : Word w) (room : board.rows < 2^w)
    (read : operand.eval m row = value) (bound : value.val ≤ board.rows)
    (live : board.coreRows ≤ value.val → value.val < board.rows → keep.eval m row ≠ 0) :
    (physicalEdge board keep operand).eval m row = value := by
  apply (board.guarded_value (x := operand) (keep := keep) m row room ?_ ?_).trans read
  · simpa only [read] using bound
  · simpa only [read] using live

/-- Even a padding lookup has the same raw value after a payload guard.
There are no birth roles in the payload strip's empty extra alphabet. -/
theorem payload_stamp (phase trial : ℕ) (m : Memory W) (row : Fin (H (.outer phase trial)).rows)
    (role : PayloadRole N k) (hdr : (H (.outer phase trial)).Loaded m) (size : D≤2^W) (room : P.catalogue.rows<2^W) :
    let a := Attempt.outer phase trial
    let f := inject (Nat.le_max_left n₀ n₁) (Fintype.equivFin _ role)
    (geo a).edge.eval m ((occ a row f).val:Word W)=
      ((v.payloadPricePorts P z width).primary P.catalogue role).eval m (row.val:Word W) := by
  intro a f
  let value := ((v.payloadPricePorts P z width).primary P.catalogue role).eval m (row.val : Word W)
  have read : (edge F bs P.catalogue.rows a f).eval m ((occ a row f).val : Word W) = value :=
    (v.source_role P z width a m row f hdr).trans
      (congrArg (fun e : Expr => e.eval m (row.val : Word W))
        (v.payload_operand P z width phase trial role))
  obtain core | ⟨empty, _⟩ :=
    (v.payloadPricePorts P z width).primary_cases P.catalogue role m (row.val : Word W) room
  · change value.val < P.catalogue.coreRows ∨ value.val = P.catalogue.rows at core
    apply (v.stamp_at_role P z width r banks src tab dst owner a m row f hdr size).trans
    apply guarded_read P.catalogue (retainedAt F bs a) (edge F bs P.catalogue.rows a f)
      m ((occ a row f).val : Word W) value room read
    · rcases core with small | same
      · exact small.le.trans (Nat.le_add_right P.catalogue.coreRows P.catalogue.boughtRows)
      · exact same.le
    · intro left right
      rcases core with small | same
      · exact False.elim ((not_le_of_gt small) left)
      · exact False.elim (right.ne same)
  · exact empty.elim

/-- Only the dated original purchased row consults the retained parent bit.
The earned installation itself supplies a bounded physical ID for a paid
role, and the producer reads the accepted birth flag at that same ballot. -/
theorem purchased_stamp (phase trial tick ordinal : ℕ) (m : Memory W)
    (row : Fin (H (.inner phase trial tick ordinal)).rows) (role : PurchasedRole v.depth k)
    (hdr : (H (.inner phase trial tick ordinal)).Loaded m) (size : D≤2^W) (room : P.catalogue.rows<2^W) :
    let a := Attempt.inner phase trial tick ordinal
    let f := inject (Nat.le_max_right n₀ n₁) (Fintype.equivFin _ role)
    let o := occ a row f
    let x := ((v.purchasedPricePorts P z width phase trial).primary P.catalogue role).eval m (row.val:Word W)
    x.val≤P.catalogue.rows →
    (role=.extra (.inr ()) → (retainedAt F bs a).eval m (o.val:Word W)≠0) →
    (geo a).edge.eval m (o.val:Word W)=x := by
  intro a f o x bounded born
  have read : (edge F bs P.catalogue.rows a f).eval m (o.val : Word W) = x :=
    (v.source_role P z width a m row f hdr).trans
      (congrArg (fun e : Expr => e.eval m (row.val : Word W))
        (v.purchased_operand P z width phase trial tick ordinal role))
  apply (v.stamp_at_role P z width r banks src tab dst owner a m row f hdr size).trans
  apply guarded_read P.catalogue (retainedAt F bs a) (edge F bs P.catalogue.rows a f)
    m (o.val : Word W) x room read bounded
  obtain core | ⟨t, roleEq, _⟩ :=
    (v.purchasedPricePorts P z width phase trial).primary_cases P.catalogue role m (row.val : Word W) room
  · change x.val < P.catalogue.coreRows ∨ x.val = P.catalogue.rows at core
    intro left right
    rcases core with small | same
    · exact False.elim ((not_le_of_gt small) left)
    · exact False.elim (right.ne same)
  · intro _ _
    cases t
    exact born roleEq

/-- The only extra input in an acquired probe's stamp is its own mode-gated
purchase word written at the parent date. This identifies exactly which
original occurrence to use with the chronological flag readback. -/
theorem retained_parent_word (phase trial tick inner : ℕ) (m : Memory W)
    (row : Fin (H (.inner phase trial tick inner)).rows) (f : Fin D)
    (header : (H (.inner phase trial tick inner)).Loaded m)
    (before : row.val<(StripChart.build F bs (.outer phase trial) 0).market.rows)
    (fits : (StripChart.build F bs (.outer phase trial) 0).market.rows≤2^W) :
    let a := Attempt.inner phase trial tick inner
    let origin := StripChart.build F bs (.outer phase trial) 0
    (retainedAt F bs a).eval m ((occ a row f).val:Word W)=m (origin.board.purchaseOut+row.val) := by
  intro a origin
  have ball : (H a).ballTerm.eval m ((occ a row f).val : Word W) = (row.val : Word W) :=
    (StripDirectory.header_pair (H a) m header row f).1
  change m (origin.board.purchaseOut+
    ((H a).ballTerm.eval m ((occ a row f).val:Word W)).val % ProtocolRAMPurchaseSampler.span origin.market.rows)=_
  rw [ball,Fin.val_cast_of_lt (before.trans_le fits),Nat.mod_eq_of_lt (before.trans (ProtocolRAMPurchaseSampler.lt_span _))]

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
