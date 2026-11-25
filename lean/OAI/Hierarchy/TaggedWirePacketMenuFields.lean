import OAI.Hierarchy.TaggedWirePacketMenu
import OAI.Hierarchy.TaggedWirePacketGatheredOpcode

namespace OAI
/-! # The same opcode tree for all runtime choices of anchors, acquired IDs and positive histograms -/
noncomputable section
namespace Hierarchy.WireTelescope.PacketTurns
open ProtocolRAM
variable {n D t : ℕ} {len actual : Fin n→ℕ}

theorem gathered_menu (format : Operands len) (same : len=actual) (ord : Fin t≃Σi,Fin (len i))
    (width nbr : Fin D→Expr) (site : Expr) :
    let o:=format.toLength same
    o.column (o.gatheredWords (moveOrder same ord) width nbr) site=
      format.column (format.gatheredWords ord width nbr) site := by
  subst actual
  cases format
  rfl

theorem low_menu (format : Operands len) (same : len=actual) (ord : Fin t≃Σi,Fin (len i)) (x y : Expr) :
    (format.toLength same).aggregateWidth (moveOrder same ord) x y=format.aggregateWidth ord x y := by
  subst actual
  cases format
  rfl

end Hierarchy.WireTelescope.PacketTurns

namespace Hierarchy.WireTelescope.StripPaths
open LinearAlgebra.SpectralBooks ChordGraph Probe AdaptiveProbe AdaptiveProbe.Strip
open ProtocolRAM PacketTurns
variable {n k N K Rn Tn D : ℕ} {A B Ball : Type}
local notation "C" => TreeColumn n
local notation "X" => TreeSite n k
local notation "R" => ColumnWires.Role C (Fin n) (A⊕B) k
local notation "T" => TreeLink n k
local notation "U" => R⊕T
variable (extra : A⊕B→DistinctPair (TreeSite n k)) (place : Ball×TreeSite n k↪Fin K) (u : Ball)
    (pr : ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k→Fin N) (ma : TreeColumn n→Fin k→Fin N)
    (tr : TreeLink n k→Fin N) (enum : Fin Rn≃(ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k⊕TreeLink n k))
    (ord : Fin Tn≃Σi,Fin (menuLen (enum i)))
    (site : TreeSite n k→Expr) (primary : ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k→Expr)
    (mate : TreeColumn n→Fin k→Expr) (tree : TreeLink n k→Expr)
    (qty : (ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k⊕TreeLink n k)→Expr)
local notation "actual" => packetInputs extra place u pr ma tr enum site primary mate tree qty
local notation "menuOp" => menuInputs extra enum site primary mate tree qty
local notation "rank" => menuOrder extra place u pr ma tr enum ord

theorem same_field (width nbr : Fin D→Expr) (here : Expr) :
    (actual).column ((actual).gatheredWords rank width nbr) here=
      (menuOp).column ((menuOp).gatheredWords ord width nbr) here := by
  exact gathered_menu menuOp (menu_shape extra place u pr ma tr enum) ord width nbr here

theorem same_low (x y : Expr) : (actual).aggregateWidth rank x y=(menuOp).aggregateWidth ord x y :=
  low_menu menuOp (menu_shape extra place u pr ma tr enum) ord x y

end Hierarchy.WireTelescope.StripPaths

end
end OAI
