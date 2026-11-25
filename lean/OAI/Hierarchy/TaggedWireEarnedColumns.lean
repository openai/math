import OAI.Hierarchy.TaggedWireEarnedTender
import OAI.Hierarchy.TaggedWidePacketPhysicalFields

namespace OAI
/-! # Dated ballot columns on the fixed installation of the actual elected packet -/
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
    {endRow : Fin b.rows→Site h d k×Site h d k} {name : Site h d k↪Fin K}
    {addr : A → Commodity (Fin (2^h)) (Stages h d) k} {m : Memory w} {reg : Word w}
local notation "roles" => ColumnWires.ends (horizontal n) extra
local notation "own" => Sum.elim (reportedRole place roles u) (reportedRole place (treeEnds n k) u)
local notation "enum" => treeFirst R T
local notation "order" => (Fintype.equivFin ((i : Fin (Fintype.card U)) × Fin (menuLen (enum i)))).symm

namespace EarnedInstall
variable (g : EarnedInstall p b π extra place u endRow name addr m reg)

local notation "old" => retained (b:=b) addr
local notation "fwd" => Fin.natAdd shift
local notation "pr" => primaryRow (b:=b) old fwd (EarnedInstall.index g)
local notation "ma" => (fun c j=>fwd (EarnedInstall.mate g c j))
local notation "tr" => (fun j:T=>fwd (EarnedInstall.index g (treeRole n k j)))
local notation "walk" => Sum.elim (links (horizontal n) extra place u pr ma) (fun j:T=>[tr j]) ∘ enum

variable {F J : Type} [Field F] [Fintype J] (labels : TreeSite n k≃Fin (Fintype.card (TreeSite n k))) (req : J → ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k)
    (rt : Fin (Fintype.card (TreeSite n k))) (P : Packet F (fun e=>@DistinctPair.chord _ _ ⟨labels⟩ (ColumnWires.ends (Strip.horizontal n) extra e)) req)
    (copies : ℕ)
local notation "row" => Row.packet (stripPacket labels roles req place u rt P) copies

variable (pad : Chord K)
local notation "phys" => installedRows π endRow name pad
local notation "chosen" => EarnedInstall.tender g labels req rt P copies pad
open LinearAlgebra.SpectralBooks.SiteTensor
open HistoryRoles Tagged
variable {D cap : ℕ} (M outerRows start shelf bits : ℕ) (stride : Bank) (participant : TreeSite n k)
    (site : TreeSite n k→Expr) (stock : A→Expr)
    (qty : (ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k ⊕ TreeLink n k)→Expr)
local notation "here" => site participant
local notation "s" => place (u,participant)
local notation "up" => pageRead (DatedRoleSheets.bank outerRows start shelf bits 0) stride here (d:=D)
local notation "nbr" => pageRead (DatedRoleSheets.bank outerRows start shelf bits 2) stride here (d:=D)
local notation "op" => EarnedInstall.operands g site stock qty
local notation "col" => StripPorts.catalogueControls p extra b shift site stock qty M outerRows start shelf bits stride participant (D:=D)
local notation "rows" => Fintype.card U

theorem tender_column (enough : rows≤M) (slot : Fin (rows*3)) (f : Fin 5) :
    col (Fin.castAdd D ((finProdFinEquiv (slot,f)).castLE (by omega)))=
      (op).column ((op).gatheredWords (chosen).ordinal up nbr) here (finProdFinEquiv (slot,f)) := by
  rw [p.catalogueControls_eq extra b shift site stock qty place u pr ma tr]
  exact (op).turn_at (chosen).ordinal enough up nbr here slot f

theorem tender_short (i : Fin rows) : (((chosen).install.steps (chosen).order) i).length≤2 :=
  earned_route_short extra place u pr ma tr i

variable {out : Memory w} {reg' : Word w} (hist : Histogram (Fin P.terms) copies)
local notation "route" => (chosen).install.steps (chosen).order
local notation "width" => Installs.numbered (chosen).order ((chosen).bits hist)
local notation "oldRows" => Installs.starts (source:=(chosen).source) (chosen).order

theorem tender_low (receipt : Reads oldRows phys route width op out reg') (sites : K≤2^w)
    {outside : (portGraph K).Port s→ℕ} (parts : PassiveWindow.Parts ((portGraph K).Port s) (Fin D) cap outside)
    (dated : NeighborReads out reg' parts up nbr) (correct : (here).eval out reg'=((s).val:Word w)) (q : Fin D) :
    (col (Fin.natAdd ((M*3)*5) q)).eval out reg'=
      ((parts.owner q).elim 0 (fun a=>if 0<parts.width q then (chosen).post hist a.val.1 else 0):Word w) := by
  rw [p.catalogueControls_eq extra b shift site stock qty place u pr ma tr]
  have read:=active_low_read oldRows phys route width (chosen).ordinal op out reg' receipt sites parts up nbr dated here correct (M:=M) q
  change ((op).controls (chosen).ordinal M up nbr here (Fin.natAdd ((M*3)*5) q)).eval out reg' = _
  refine read.trans ?_
  unfold RowRouting.post
  rw [(chosen).install.counted (chosen).order ((chosen).bits hist)]

end EarnedInstall
end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

end
end OAI
