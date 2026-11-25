import OAI.Hierarchy.TaggedWireElectedStripDebit

namespace OAI
/-! # Original per-port debits on the full, padded signed repair board -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard Strip WireTelescope CatalystArchive StockCommit RepairHistogram PurchaseStage
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor Probe ChosenPackets RowRouting StripPaths PacketTurns
open ThreeFlat.Diagonal.MotifOuterTerms
open scoped Classical Fin.CommRing

variable {sam : PurchaseSampler} {h d k n K w : ℕ} {A B Ball F : Type} [Field F] [Fintype A] [Fintype B] [Fintype Ball]
local notation "C" => TreeColumn n
local notation "R" => ColumnWires.Role C (Fin n) (A⊕B) k
local notation "Good" => Commodity (Fin (2^h)) (Stages h d) k
variable {p : StripPorts sam h d k (TreeColumn n) (Fin n) B} {b : Board} {π : Equiv.Perm (Fin (2^h))}
    {extra : A⊕B→DistinctPair (TreeSite n k)} {place : Ball×TreeSite n k↪Fin K} {u : Ball}
    {endRow : Fin b.rows→Site h d k×Site h d k} {name : Site h d k↪Fin K} {addr : A → Commodity (Fin (2^h)) (Stages h d) k}
    {m : Memory w} {reg : Word w}
local notation "roles" => ColumnWires.ends (horizontal n) extra
local notation "line" => reportedRole place roles u
variable (g : EarnedInstall p b π extra place u endRow name addr m reg)
  {sites N z rawD D : ℕ} [Nonempty (Fin sites)] [Nonempty (Fin k)] [Nonempty (ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k)]
  {M ε tree : ℝ} {len : Fin n→ℝ} {cap : A→ℝ}
local notation "req" => ColumnWires.demand (I:=C) (H:=Fin n) (k:=k) (Sum.inl (α:=A) (β:=B))
variable {e : ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k → Chord sites}
    {menu : Probe.FixedMenu F e
      (ColumnWires.demand (I:=TreeColumn n) (H:=Fin n) (k:=k) (Sum.inl (α:=A) (β:=B)))
      ((fun y:A→ℝ => ColumnWires.quote (I:=TreeColumn n) (k:=k) M len (LocalCommodity.extraPrice (B:=B) y)) ''
        Set.Icc 0 cap) ε tree N}
    (i : menu.index) {q : ℕ} (x : StripInput menu w z rawD q D)
    (j : Fin x.raw.market.rows) (live : j∈liveRows x.ballot x.mem x.raw.market.rows)
    (arity : (x.ballot.termCount.read x.mem (x.ballot.packet.eval x.mem (j.val:Word w))).val=(menu.packet i).terms)
    (selected : (x.ballot.packet.eval x.mem (j.val:Word w)).val=(Fintype.equivFin menu.index i).val+1)
local notation "hdr" => (⟨x.start,x.raw.market.rows,D⟩ : PortHeader)
local notation "a" => x.form.pricedArea
local notation "s" => x.form.stockSource
local notation "st" => fresh a s
local notation "keyMap" => pairKeys (Columns h d) k
variable {payload : ℕ} {chart : Chart w q D} {ev : Attempt} {before : Memory w}
local notation "recover" col => CatalystArchive.select (D:=D) (hdr).fieldTerm (hdr).ballTerm
  (ownerExpr (H:=Fin n) (E:=A⊕B) (k:=k) col)

include g live arity selected in
set_option maxHeartbeats 2000000 in
omit [Fintype Ball] [Nonempty (Fin k)] in
theorem EarnedInstall.chosen_strip_debit (bound : (menu.packet i).terms≤q) (column : C→Expr)
    (date : CatalystArchive.Date chart ev before (recover column) ((a).direct+(a).occurrences) (a).occurrences
      (Fintype.card (Columns h d)*k) payload)
    (labels : LabelSource) (physical : chart.commit ev=pricedSegment a s labels w x.ballot)
    (ready : Calendar.ready chart (.attempt ev) before) (board : EventBoard st w)
    (stage : x.mem=stageInput a s labels (postOutput (chart.layout ev) (repair chart ev) (prepared chart ev before)))
    (wide : payload<2^w) (keyRoom : Fintype.card (Columns h d)*k≤2^w) (head : (hdr).Loaded before)
    (colWord : ∀c,(column c).eval before (j.val:Word w)=(p.column c).eval m reg)
    (code : Good≃Fin x.raw.coordinates) (slots : ∀u,(x.addr u).eval x.mem (j.val:Word w)=
      ((code (addr u)).val:Word w)) (pad : Chord K) (v : Fin D) :
    let occ:=x.plan.enum ⟨j,v⟩
    let debit:=consumedBits (st).columns x.mem occ
    Finsupp.single (stripDebitWire pad line v) debit=
      (kind (goods:=(a).goods) (st).plan.bank (st).columns x.mem occ).elim 0 (fun good=>(ordinalGoods π name code).chordWidth good debit)+
      (catalystGraph name).chordWidth ((keyMap).symm (date.entry.owner (Fin.cast date.shape.symm occ)))
        (date.entry.bits (Fin.cast date.shape.symm occ)) := by
  obtain ⟨spare,eqn⟩:=Nat.exists_eq_add_of_le bound
  subst q
  exact g.elected_debit i spare x j live arity selected column date labels physical ready board stage wide keyRoom head colWord code slots pad v

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
