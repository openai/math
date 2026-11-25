import OAI.Hierarchy.TaggedWireStripNative
import OAI.Hierarchy.TaggedWireStripTender
import OAI.Hierarchy.TaggedWireEarnedReadCore
import OAI.Hierarchy.TaggedWirePacketMenu

namespace OAI
/-! # The selected packet and its actual route order from one dated CT receipt -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard AdaptiveProbe Strip WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph Probe ChosenPackets RowRouting StripPaths PacketTurns
open ThreeFlat.Diagonal.MotifOuterTerms
open scoped Classical Fin.CommRing
variable {sam : PurchaseSampler} {h d k n K w : ℕ} {A B Ball : Type} [Fintype A] [Fintype B] [Fintype Ball]
local notation "C" => TreeColumn n
local notation "X" => TreeSite n k
local notation "R" => ColumnWires.Role C (Fin n) (A⊕B) k
local notation "T" => TreeLink n k
local notation "U" => R⊕T
local notation "G" => Commodity (Fin (2^h)) (Stages h d) k
local notation "shift" => Fintype.card G
variable {p : StripPorts sam h d k (TreeColumn n) (Fin n) B} {b : Board} {π : Equiv.Perm (Fin (2^h))}
    {extra : A⊕B→DistinctPair (TreeSite n k)} {place : Ball×TreeSite n k↪Fin K} {u : Ball}
    {endRow : Fin b.rows→Site h d k×Site h d k} {name : Site h d k↪Fin K} {pad : Chord K}
    {addr : A → Commodity (Fin (2^h)) (Stages h d) k} {m : Memory w} {reg : Word w}
local notation "roles" => ColumnWires.ends (horizontal n) extra
local notation "own" => Sum.elim (reportedRole place roles u) (reportedRole place (treeEnds n k) u)
local notation "phys" => installedRows π endRow name pad
local notation "enum" => treeFirst R T
local notation "order" => (Fintype.equivFin ((i : Fin (Fintype.card U)) × Fin (menuLen (enum i)))).symm

/-- The chronological geometry has no histogram parameter. Later numeric
reports reuse these very walks for every possible local term count. -/
structure EarnedInstall (p : StripPorts sam h d k C (Fin n) B) (b : Board) (π : Equiv.Perm (Fin (2^h)))
    (extra : A⊕B→DistinctPair X) (place : Ball×X↪Fin K) (u : Ball)
    (endRow : Fin b.rows→Site h d k×Site h d k) (name : Site h d k↪Fin K) (addr : A→G)
    (m : Memory w) (reg : Word w) where
  lookup : Fin b.coreRows≃Edges sam h d k
  loaded : CoreLookup.Loaded p.directory lookup m
  wide : b.rows<2^w
  col : C → Columns h d
  placed : EarnedPlacement p b m reg col extra endRow
  core : ∀f,endRow (b.coreIndex (lookup.symm f))=CoreBoard.ends π f
  mapped : ∀x,place (u,x)=name (Prod.map col id x)
  goods : ∀a,commodityEnds π (addr a)=(Prod.map col id (extra (.inl a)).left,Prod.map col id (extra (.inl a)).right)

namespace EarnedInstall
variable (g : EarnedInstall p b π extra place u endRow name addr m reg)

def index := g.placed.2.choose
def mate := g.placed.2.choose_spec.choose
local notation "stamp" => g.placed.2.choose_spec.choose_spec
def retained (addr : A→G) (a : A) := stockRow (p:=b.rows) (stockOrder h d k (addr a))
local notation "old" => retained (b:=b) addr
local notation "fwd" => Fin.natAdd shift
local notation "pr" => primaryRow (b:=b) old fwd g.index
local notation "ma" => fun c j=>fwd (g.mate c j)
local notation "tr" => fun j:T=>fwd (g.index (treeRole n k j))
local notation "walk" => Sum.elim (links (horizontal n) extra place u pr ma) (fun j:T=>[tr j]) ∘ enum

include g in
omit [Fintype A] [Fintype B] [Fintype Ball] in
theorem stock_face (a : A) : phys (old a)=reportedRole place roles u (.extra (.inl a)) := by
  apply installed_stock π endRow name pad place u (fun a=>extra (.inl a)) a (addr a)
  · rw [g.mapped,g.goods]
  · rw [g.mapped,g.goods]

omit [Fintype Ball] [Fintype A] [Fintype B] in
theorem faces (pad : Chord K) :
    (∀r,installedRows π endRow name pad (pr r)=reportedRole place roles u (firstRole r)) ∧
    (∀c j,installedRows π endRow name pad (fwd (g.mate c j))=reportedRole place roles u (.radius c j true)) ∧
    (∀j,installedRows π endRow name pad (fwd (g.index (treeRole n k j)))=reportedRole place (treeEnds n k) u j) :=
  p.install_faces extra place u (installedRows π endRow name pad) b m reg g.lookup g.loaded g.wide π g.col g.placed.1 endRow
    g.core (stamp).2.2.1 (stamp).2.2.2 name g.mapped old fwd g.index g.mate (g.stock_face (pad:=pad))
    (stamp).1 (stamp).2.1 (installed_paid π endRow name pad)

def installation (pad : Chord K) : Installs own (installedRows π endRow name pad) :=
  p.install (extra:=extra) (place:=place) (u:=u) («phys»:=installedRows π endRow name pad)
    b m reg g.lookup g.loaded g.wide π g.col g.placed.1 endRow g.core (stamp).2.2.1 (stamp).2.2.2
    name g.mapped old fwd g.index g.mate (g.stock_face (pad:=pad)) (stamp).1 (stamp).2.1
    (installed_paid π endRow name pad)

omit [Fintype Ball] in
theorem install_steps (pad : Chord K) : (g.installation pad).steps enum=walk := rfl

def ordinal (pad : Chord K) : Fin (Fintype.card ((i : Fin (Fintype.card U)) × Fin (menuLen (enum i))))≃
    Σi,Fin (((g.installation pad).steps enum) i).length :=
  menuOrder extra place u pr ma tr enum order

variable {F J : Type} [Field F] [Fintype J] (labels : TreeSite n k≃Fin (Fintype.card (TreeSite n k))) (req : J → ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k)
    (rt : Fin (Fintype.card (TreeSite n k))) (P : Packet F (fun e=>@DistinctPair.chord _ _ ⟨labels⟩ (ColumnWires.ends (Strip.horizontal n) extra e)) req)
    (copies : ℕ)
local notation "row" => Row.packet (stripPacket labels roles req place u rt P) copies

def tender (pad : Chord K) : RowRouting row (installedRows π endRow name pad) :=
  stripTender labels roles req place u rt P copies (installedRows π endRow name pad) (g.installation pad) (g.ordinal pad)

variable (pad : Chord K)
local notation "chosen" => g.tender labels req rt P copies pad
def operands (site : X→Expr) (stock : A→Expr) (qty : U→Expr) :=
  packetInputs extra place u pr ma tr enum site (readPrimary stock shift (p.primary b))
  (emitterMate (A:=A) p b shift) (emitterTree (A:=A) p b shift) qty

theorem tender_reads (hist : Histogram (Fin P.terms) copies) (site : X→Expr) (stock : A→Expr) (qty : U→Expr)
    (room : K≤2^w) (mounted : ∀x,(site x).eval m reg=((place (u,x)).val:Word w))
    (held : ∀a,(stock a).eval m reg=(PurchaseInventory.slot (addr a):Word w))
    (amount : ∀i,(qty (enum i)).eval m reg=((Sum.elim (histWidth P.count hist)
      (fun _ : T=>copies*P.selectorBits) (enum i) : ℕ) : Word w)) :
    Reads (Installs.starts (source:=(chosen).source) (chosen).order) (installedRows π endRow name pad) ((chosen).install.steps (chosen).order)
      (Installs.numbered (chosen).order ((chosen).bits hist)) (g.operands site stock qty) m reg := by
  apply p.packet_reads (extra:=extra) (place:=place) (u:=u) (b:=b) («shift»:=shift) («phys»:=installedRows π endRow name pad)
    m reg g.lookup g.loaded g.wide π g.col g.placed.1 endRow g.core (stamp).2.2.1 (stamp).2.2.2
    name g.mapped old g.index g.mate (g.stock_face (pad:=pad)) (stamp).1 (stamp).2.1 (installed_paid π endRow name pad)
    site stock qty enum _ room mounted _ amount
  exact held

end EarnedInstall
end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

end
end OAI
