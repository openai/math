import OAI.Hierarchy.ProbeFixedStripQuotes
import OAI.Hierarchy.TaggedWireEarnedMeasuredRow
import OAI.Hierarchy.TaggedWireEarnedTreeMeasure

namespace OAI
/-! # Physical target coordinates of an elected strip and its recorded histogram -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard Strip WireTelescope CatalystArchive StockCommit RepairHistogram
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor Probe ChosenPackets RowRouting StripPaths PacketTurns
open ThreeFlat.Diagonal.MotifOuterTerms
open scoped BigOperators Classical Fin.CommRing

variable {sam : PurchaseSampler} {h d k n K w : ℕ} {A B Ball F : Type}
  [Field F] [Fintype A] [Fintype B] [Fintype Ball]
local notation "C" => TreeColumn n
local notation "R" => ColumnWires.Role C (Fin n) (A⊕B) k
local notation "T" => TreeLink n k
local notation "Good" => Commodity (Fin (2^h)) (Stages h d) k
variable {p : StripPorts sam h d k (TreeColumn n) (Fin n) B} {b : Board} {π : Equiv.Perm (Fin (2^h))}
  {extra : A⊕B→DistinctPair (TreeSite n k)} {place : Ball×TreeSite n k↪Fin K} {u : Ball}
  {endRow : Fin b.rows→Site h d k×Site h d k} {name : Site h d k↪Fin K} {addr : A → Commodity (Fin (2^h)) (Stages h d) k}
  {m archived : Memory w} {reg : Word w}
variable (g : EarnedInstall p b π extra place u endRow name addr m reg)
  (labels : TreeSite n k≃Fin (Fintype.card (TreeSite n k))) (rt : Fin (Fintype.card (TreeSite n k)))
  {N z rawD D : ℕ} [Nonempty (Fin (Fintype.card (TreeSite n k)))] [Nonempty (Fin k)]
  [Nonempty (ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k)]
  {M ε tree : ℝ} {len : Fin n→ℝ} {cap : A→ℝ}
local notation "req" => ColumnWires.demand (I:=C) (H:=Fin n) (k:=k) (Sum.inl (α:=A) (β:=B))
variable {menu : Probe.FixedMenu F
    (fun e : ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k =>
      @DistinctPair.chord _ _ ⟨labels⟩ (ColumnWires.ends (horizontal n) extra e))
    (ColumnWires.demand (I:=TreeColumn n) (H:=Fin n) (k:=k) (Sum.inl (α:=A) (β:=B)))
    ((fun y:A→ℝ => ColumnWires.quote (I:=TreeColumn n) (k:=k) M len (LocalCommodity.extraPrice (B:=B) y)) ''
      Set.Icc 0 cap) ε tree N}
  (i : menu.index) (spare : ℕ) (x : StripInput menu w z rawD ((menu.packet i).terms+spare) D)
  (j : Fin x.raw.market.rows) (live : j∈liveRows x.ballot x.mem x.raw.market.rows)
  (arity : (x.ballot.termCount.read x.mem (x.ballot.packet.eval x.mem (j.val:Word w))).val=(menu.packet i).terms)
  (selected : (x.ballot.packet.eval x.mem (j.val:Word w)).val=(Fintype.equivFin menu.index i).val+1)
  (pad : Chord K) (ordinal : Commodity (Fin (2^h)) (Stages h d) k ↪ Fin x.raw.coordinates)
  (slots : ∀a,(x.addr a).eval x.mem (j.val:Word w)=((ordinal (addr a)).val:Word w))
local notation "packet" => StripInput.packetAt i spare x j live arity selected
local notation "needs" => (fun z : PositiveDemand req i.val.val=>req z.val)
local notation "route" => g.tender labels needs rt (menu.packet i) x.ballot.copies pad
local notation "loaded" => (route).install.load ((route).bits (packet).h)
local notation "st" => fresh x.form.pricedArea x.form.stockSource
local notation "nativeTag" => kind (goods:=x.form.pricedArea.goods) (st).plan.bank (st).columns x.mem

include slots in
omit [Nonempty (Fin k)] in
private theorem packet_kind (r : R) :
    (nativeTag) (x.plan.enum ⟨j,(packet).ports r⟩)=ColumnWires.account (ordinal ∘ addr) r := by
  rw [StripInput.packetAt_port]
  apply x.role_kind j (ordinal ∘ addr) _ r
  intro a
  have bounded : (ordinal (addr a)).val<2^w :=
    (ordinal (addr a)).isLt.trans_le ((Nat.le_add_left ..).trans x.bankFit.le)
  simp only [Function.comp_apply,slots,Fin.val_cast_of_lt bounded]

include slots in
omit [Nonempty (Fin k)] in
/-- The stock credit is selected by the original destination word of each
real port, with the native histogram of the elected packet. -/
theorem EarnedInstall.elected_stock_target (good : Good) :
    loaded (stockRow (p:=b.rows) (stockOrder h d k good))=
      x.plan.rowCredit j (fun occ=>(nativeTag) occ=some (ordinal good)) :=
  g.measured_stock labels needs rt (menu.packet i) pad packet ordinal
    (packet_kind labels i spare x j live arity selected ordinal slots) good

variable (stamp : LabelSource) (mask mate : Expr) (cut : ℕ)
  (low : PrefixAgreement.Low cut archived m)
  (fits : ∀ r : ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k, (p.primary b r).Fits w cut)
  (primary : ∀ r : ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k, paidRole r →
    stamp.edge.eval archived ((x.plan.enum ⟨j, PortPadding.inject x.ports (Fintype.equivFin _ r)⟩).val:Word w)=
      (p.primary b r).eval archived reg)
  (on : ∀ r : ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k,
    mask.eval archived ((x.plan.enum ⟨j, PortPadding.inject x.ports (Fintype.equivFin _ r)⟩).val:Word w)≠0 ↔
      EarnedInstall.usesMate r)
  (second : ∀ c axis, mate.eval archived ((x.plan.enum ⟨j, PortPadding.inject x.ports
      (Fintype.equivFin (ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k) (.catalyst c axis))⟩).val:Word w)=
    (p.mate b (.catalyst c axis : ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k)).eval archived reg)
local notation "firstAt" e => x.plan.rowCredit j (primaryHit x.form.pricedArea x.form.stockSource stamp x.mem archived e)
local notation "secondAt" e => x.plan.rowCredit j (secondaryHit x.form.pricedArea x.form.stockSource mask mate x.mem archived e)

include slots low fits primary on second in
omit [Nonempty (Fin k)] in
/-- Each real port credits its measured primary edge and, when the posted mask
selects a catalyst, its actual opposite radius. The selector tree uses the same
chosen packet and the batch's actual copy count. -/
theorem EarnedInstall.elected_paid_target (e : Fin b.rows) :
    loaded (paidRow (g:=Fintype.card Good) e)=(firstAt e)+(secondAt e)+
      ∑ l:T,if ((p.primary b (treeRole n k l:R)).eval archived reg).val=e.val
        then x.ballot.copies*(menu.packet i).selectorBits else 0 := by
  apply g.measured_paid_at labels needs rt (menu.packet i) pad packet ordinal
    (packet_kind labels i spare x j live arity selected ordinal slots) stamp mask mate e cut low fits
  · simpa only [StripInput.packetAt_port] using primary
  · simpa only [StripInput.packetAt_port] using on
  · simpa only [StripInput.packetAt_port] using second

include slots low fits primary on second in
omit [Nonempty (Fin k)] in
/-- Express the same third summand in the physical forest numbering and
recorded broadcast-width field used by `measured_tree_load`. -/
theorem EarnedInstall.elected_forest_target (originalRow : reg=(j.val:Word w)) (pos : 0<b.coreRows)
    (selector : (archived (x.form.pricedArea.broadcast+j.val)).val=(menu.packet i).selectorBits) (e : Fin b.rows) :
    loaded (paidRow (g:=Fintype.card Good) e)=(firstAt e)+(secondAt e)+
      ∑ l:T,if b.coreIndex (treeTarget p b archived j.val l pos)=e
        then x.ballot.copies*(archived (x.form.pricedArea.broadcast+j.val)).val else 0 := by
  rw [g.elected_paid_target labels rt i spare x j live arity selected pad ordinal slots stamp mask mate
    cut low fits primary on second e]
  apply congrArg (((firstAt e)+(secondAt e))+·)
  apply Finset.sum_congr rfl
  intro l _
  have bounded := g.tree_range_at archived cut low fits l
  rw [originalRow] at bounded ⊢
  simp only [Fin.ext_iff,earned_tree_target (A:=A) p b archived pos j.val l g.wide bounded,selector]

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
