import OAI.Hierarchy.TaggedWireElectedStripTarget

namespace OAI
/-! # Measured original strip routes for the true signed histogram on a padded native board -/

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
  (i : menu.index) {q : ℕ} (x : StripInput menu w z rawD q D)
  (j : Fin x.raw.market.rows) (live : j∈liveRows x.ballot x.mem x.raw.market.rows)
  (arity : (x.ballot.termCount.read x.mem (x.ballot.packet.eval x.mem (j.val:Word w))).val=(menu.packet i).terms)
  (selected : (x.ballot.packet.eval x.mem (j.val:Word w)).val=(Fintype.equivFin menu.index i).val+1)
  (pad : Chord K) (ordinal : Commodity (Fin (2^h)) (Stages h d) k ↪ Fin x.raw.coordinates)
  (slots : ∀a,(x.addr a).eval x.mem (j.val:Word w)=((ordinal (addr a)).val:Word w))
variable (bound : (menu.packet i).terms≤q) (chosen : Histogram (Fin (menu.packet i).terms) x.ballot.copies)
  (digits : ∀t : Fin (menu.packet i).terms, ((x.ballot.field (t.castLE bound)).eval x.mem (j.val:Word w)).val=((chosen.val t).val))
local notation "needs" => (fun z : PositiveDemand req i.val.val=>req z.val)
local notation "route" => g.tender labels needs rt (menu.packet i) x.ballot.copies pad
local notation "loaded" => (route).install.load ((route).bits chosen)
local notation "st" => fresh x.form.pricedArea x.form.stockSource
local notation "nativeTag" => kind (goods:=x.form.pricedArea.goods) (st).plan.bank (st).columns x.mem
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


include live arity selected slots low fits primary on second digits in
omit [Nonempty (Fin k)] in
/-- The public menu alphabet can have fewer letters than the fixed machine.
The original low selector digits uniquely determine the histogram in both sum identities. -/
theorem EarnedInstall.chosen_strip_target :
    (∀good : Good,loaded (stockRow (p:=b.rows) (stockOrder h d k good))=
      x.plan.rowCredit j (fun occ=>(nativeTag) occ=some (ordinal good))) ∧
    (∀e : Fin b.rows,loaded (paidRow (g:=Fintype.card Good) e)=(firstAt e)+(secondAt e)+
      ∑ l:T,if ((p.primary b (treeRole n k l:R)).eval archived reg).val=e.val
        then x.ballot.copies*(menu.packet i).selectorBits else 0) := by
  obtain ⟨spare,hw⟩:=Nat.exists_eq_add_of_le bound
  subst q
  let read:=StripInput.packetAt i spare x j live arity selected
  have same : read.h=chosen := by
    apply Subtype.ext
    funext t
    apply Fin.ext
    have datum:=read.fields (t.castAdd spare)
    have eqn : ((x.ballot.field (t.castAdd spare)).eval x.mem (j.val:Word w)).val=
        ((read.h.val t).val) := by
      simpa only [padHistogram,Fin.addCases_left] using datum
    exact eqn.symm.trans (digits t)
  rw [←same]
  exact ⟨g.elected_stock_target labels rt i spare x j live arity selected pad ordinal slots,
    g.elected_paid_target labels rt i spare x j live arity selected pad ordinal slots stamp mask mate
      cut low fits primary on second⟩

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
