import OAI.Hierarchy.TaggedWirePacketCatalogueControls

namespace OAI
/-! # Authenticated candidate rows are the very words of the installed two-radius table -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph Probe AdaptiveProbe Strip
open Computability.VPVNP.BurstRAM PrivateRAM WireTelescope StripPaths PacketTurns TurnShelf ChosenPackets.RowRouting Tagged
open ProbeStage.CoreBoard.HistoryRoles
open scoped Classical Fin.CommRing

/-- The shifted and unshifted catalogues have the same live rows because column four
is the role width in both. Form this dependent entry while its route is abstract. -/
private abbrev shiftedTurnWord {sites roles edges hops visits wordWidth : ℕ}
    (old : Fin roles → Chord sites) (edge : Fin edges → Chord sites)
    (paths : Fin roles → List (Fin edges)) (width : Fin roles → ℕ)
    (ord : Fin hops ≃ Σ i, Fin (paths i).length) (base : Fin edges → ℕ)
    (before : Fin roles → Bool → ℕ) (after : Fin edges → Bool → ℕ)
    (short : ∀ i, (paths i).length ≤ 2) (turns : Fin visits ≃ Positions paths)
    (f : Fin 5) (seat : Fin sites × Fin (roles*3)) : Word wordWidth :=
  ProtocolRAMTurnShelf.entry (shiftedFields old edge paths width ord base before after short turns)
    (put old edge paths width ord before after short turns) f seat

variable {sam : ProbeStage.PurchaseSampler} {h d k n D S m W cap count : ℕ} {A B Ball : Type} [Fintype A] [Fintype B]
local notation "C" => TreeColumn n
local notation "X" => TreeSite n k
local notation "R" => ColumnWires.Role C (Fin n) (A⊕B) k
local notation "T" => TreeLink n k
local notation "U" => R⊕T
local notation "rows" => Fintype.card U
local notation "enum" => treeFirst R T
local notation "order" => (Fintype.equivFin ((i : Fin rows) × Fin (menuLen (enum i)))).symm
variable (p : StripPorts sam h d k (TreeColumn n) (Fin n) B) (extra : A⊕B→DistinctPair (TreeSite n k))
    (b : Board) (shift : ℕ) (site : TreeSite n k→Expr) (stock : A→Expr)
    (qty : (ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k ⊕ TreeLink n k) → Expr)
    (place : Ball×TreeSite n k↪Fin S) (center : Ball)
    (primary : ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k → Fin m)
    (mate : TreeColumn n→Fin k→Fin m) (tree : TreeLink n k→Fin m)
local notation "actual" => packetInputs extra place center primary mate tree enum site (readPrimary stock shift (p.primary b))
  (emitterMate (A:=A) p b shift) (emitterTree (A:=A) p b shift) qty
local notation "rank" => menuOrder extra place center primary mate tree enum order
local notation "route" => Sum.elim (links (AdaptiveProbe.Strip.horizontal n) extra place center primary mate) (fun j:T=>[tree j]) ∘ enum
variable (M originalRows start total bits : ℕ) (siteBase : Bank) (participant : TreeSite n k)
local notation "here" => site participant
local notation "s" => place (center,participant)
local notation "up" => pageRead (DatedRoleSheets.bank originalRows start total bits 0) siteBase here (d:=D)
local notation "nbr" => pageRead (DatedRoleSheets.bank originalRows start total bits 2) siteBase here (d:=D)
local notation "emitted" => p.catalogueControls extra b shift site stock qty M originalRows start total bits siteBase participant (D:=D)

theorem StripPorts.catalogueControls_eq : emitted=(actual).controls rank M up nbr here :=
  menuControls_eq extra enum order site _ _ _ qty place center primary mate tree M originalRows start total bits siteBase here

theorem StripPorts.vacant_gate (f : Fin ((M*3)*5)) (absent : (rows*3)*5≤f.val) :
    emitted (f.castAdd D)=.lit 0 := by
  exact Operands.vacant_turn _ _ _ _ _ _ absent

theorem earned_route_short (i : Fin rows) : (route i).length≤2 := by
  rw [show (route i).length=menuLen (enum i) from
    length_menu (AdaptiveProbe.Strip.horizontal n) extra place center primary mate tree (enum i)]
  rcases e:enum i with r|t
  · change (if _ then 2 else 1)≤2;split <;> decide
  · change 1 ≤ 2
    decide

set_option maxHeartbeats 800000
variable (old : Fin (Fintype.card (ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k ⊕ TreeLink n k)) → Chord S)
    (edge : Fin m→Chord S)
    (width : Fin (Fintype.card (ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k ⊕ TreeLink n k)) → ℕ)
    (mem : Memory W) (reg : Word W)
    (receipt : Reads old edge
      (Sum.elim (links (AdaptiveProbe.Strip.horizontal n) extra place center primary mate) (fun j : TreeLink n k => [tree j]) ∘ (treeFirst (ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k) (TreeLink n k)))
      width (StripPaths.packetInputs (n:=n) (k:=k) («K»:=S) («N»:=m)
        extra place center primary mate tree (treeFirst (ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k) (TreeLink n k)) site
        (readPrimary stock shift (p.primary b)) (emitterMate (A:=A) p b shift) (emitterTree (A:=A) p b shift) qty)
      mem reg)
    (fit : S≤2^W) (paid : m≤2^W)
    {outside : (portGraph S).Port (place (center,participant)) → ℕ}
    (parts : PassiveWindow.Parts ((portGraph S).Port (place (center,participant))) (Fin D) cap outside)
    (dated : NeighborReads mem reg parts
      (pageRead (DatedRoleSheets.bank originalRows start total bits 0) siteBase (site participant))
      (pageRead (DatedRoleSheets.bank originalRows start total bits 2) siteBase (site participant)))
    (correct : (site participant).eval mem reg=((place (center,participant)).val:Word W))
local notation "prior" => fun (i : Fin rows) (x : Bool)=>(halfCode i x).val
local notation "post" => fun (e : Fin m) (x : Bool)=>rows*2+PacketNeighbor.index parts ((rowGraph edge).vertex e (!x))
local notation "offset" => AggregatePrefix.paidShift route width rank edge

include receipt fit paid dated correct in
theorem StripPorts.published_turn (enough : rows≤M) (short : ∀i,(route i).length≤2) (turns : Fin count≃Positions route)
    (bounded : ∀i,width i<2^W) (slot : Fin (rows*3)) (f : Fin 5) :
    (emitted (Fin.castAdd D ((finProdFinEquiv (slot,f)).castLE (by omega)))).eval mem reg=
      shiftedTurnWord (sites:=S) (roles:=rows) (edges:=m) (visits:=count) (wordWidth:=W)
        old edge route width rank offset prior post short turns f (s,slot) := by
  rw [p.catalogueControls_eq extra b shift site stock qty place center primary mate tree]
  exact active_turn_read old edge route width rank actual mem reg receipt fit parts up nbr dated here correct paid enough
    short turns bounded slot f

include receipt fit dated correct in
theorem StripPorts.published_low (q : Fin D) :
    (emitted (Fin.natAdd ((M*3)*5) q)).eval mem reg=
      ((parts.owner q).elim 0 (fun v=>if 0<parts.width q then installedWidths edge (routeLoad route width) v.val.1 else 0):Word W) := by
  rw [p.catalogueControls_eq extra b shift site stock qty place center primary mate tree]
  exact active_low_read old edge route width rank actual mem reg receipt fit parts up nbr dated here correct q

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

end
end OAI
