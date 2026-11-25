import OAI.Hierarchy.TaggedWireStripDebitWire
import OAI.Hierarchy.TaggedWireElectedDebitRole

namespace OAI
/-! # The incoming widths of one original elected native strip -/
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
    (i : menu.index) (spare : ℕ) (x : StripInput menu w z rawD ((menu.packet i).terms+spare) D)
    (j : Fin x.raw.market.rows) (live : j∈liveRows x.ballot x.mem x.raw.market.rows)
    (arity : (x.ballot.termCount.read x.mem (x.ballot.packet.eval x.mem (j.val:Word w))).val=(menu.packet i).terms)
    (selected : (x.ballot.packet.eval x.mem (j.val:Word w)).val=(Fintype.equivFin menu.index i).val+1)
local notation "hdr" => (⟨x.start,x.raw.market.rows,D⟩ : PortHeader)
local notation "a" => x.form.pricedArea
local notation "s" => x.form.stockSource
local notation "st" => fresh a s
local notation "keyMap" => pairKeys (Columns h d) k
variable {payload : ℕ} {chart : Chart w ((menu.packet i).terms+spare) D} {ev : Attempt} {before : Memory w}
local notation "recover" col => CatalystArchive.select (D:=D) (hdr).fieldTerm (hdr).ballTerm
  (ownerExpr (H:=Fin n) (E:=A⊕B) (k:=k) col)

include g live arity selected in
omit [Fintype Ball] [Nonempty (Fin k)] in
theorem EarnedInstall.elected_debit (column : C→Expr)
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
  let packet:=StripInput.packetAt i spare x j live arity selected
  apply g.debit_port (fun z : PositiveDemand req i.val.val=>z.val) packet date code (wire:=stripDebitWire pad line) (v:=v)
  · intro r
    rw [show packet.ports r=PortPadding.inject x.ports (Fintype.equivFin R r) from rfl]
    exact x.checkedKinds j (code ∘ addr) slots r
  · intro occ
    simpa only [stage,StripInput.form] using! date.issued_at labels x.ballot physical ready board wide occ
  · intro c axis
    exact g.owner_port hdr x.ports j c axis before head x.portFit column (colWord c)
  · exact keyRoom
  · intro r
    change PortPadding.extend _ pad (PortPadding.inject x.ports (Fintype.equivFin R r))=_
    rw [PortPadding.extend_real,Equiv.symm_apply_apply]

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
