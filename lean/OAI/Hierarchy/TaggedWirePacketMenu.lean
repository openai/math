import OAI.Hierarchy.TaggedWirePacketInputs

namespace OAI
/-! # One immutable occurrence order and native operand array for each original strip menu -/
noncomputable section
namespace Hierarchy.WireTelescope.PacketTurns
variable {n t : ℕ} {len len' : Fin n→ℕ}

def Operands.toLength (o : Operands len) (same : len=len') : Operands len' where
  oldSite:=o.oldSite
  width:=o.width
  edge i q:=o.edge i (q.cast (congrFun same i).symm)
  endSite i q:=o.endSite i (q.cast (congrFun same i).symm)

def moveOrder (same : len=len') (ord : Fin t≃Σi,Fin (len i)) : Fin t≃Σi,Fin (len' i) :=
  same ▸ ord

end Hierarchy.WireTelescope.PacketTurns

namespace Hierarchy.WireTelescope.StripPaths
open LinearAlgebra.SpectralBooks ChordGraph Probe AdaptiveProbe AdaptiveProbe.Strip
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM PacketTurns
open scoped Classical
variable {n k K N Rn Tn : ℕ} {A B Ball : Type}
local notation "C" => TreeColumn n
local notation "X" => TreeSite n k
local notation "R" => ColumnWires.Role C (Fin n) (A⊕B) k
local notation "T" => TreeLink n k
local notation "U" => R⊕T
variable (extra : A⊕B→DistinctPair (TreeSite n k))
local notation "ends" => ColumnWires.ends (horizontal n) extra
variable (place : Ball×TreeSite n k↪Fin K) (u : Ball)
    (pr : ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k→Fin N) (ma : TreeColumn n→Fin k→Fin N)
    (tr : TreeLink n k→Fin N)
    (enum : Fin Rn≃(ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k⊕TreeLink n k))
local notation "run" => Sum.elim (links (horizontal n) extra place u pr ma) (fun j=>[tr j]) ∘ enum
local notation "lengths" => fun i=>menuLen (enum i)

theorem menu_shape : lengths=(fun i=>(run i).length) := by
  funext i
  exact (length_menu (horizontal n) extra place u pr ma tr (enum i)).symm

/-- The public menu chooses ordinals once for its one- or two-hop positions,
independently of which ballot currently occupies those paid rows. -/
def menuOrder (ord : Fin Tn≃Σi,Fin (menuLen (enum i))) : Fin Tn≃Σi,Fin (run i).length :=
  moveOrder (menu_shape extra place u pr ma tr enum) ord

def menuInputs (site : X→Expr) (primary : R→Expr) (mate : C→Fin k→Expr) (tree : T→Expr) (qty : U→Expr) :
    Operands lengths where
  oldSite i b:=face site ((enum i).elim ends (treeEnds n k)) b
  width i:=qty (enum i)
  edge i j:=routedWord extra site primary mate tree (enum i) j.val
  endSite i j b:=routedWord extra site (fun v=>face site (ends (firstRole v)) b)
    (fun c a=>face site (ends (.radius c a true)) b) (fun t=>face site (treeEnds n k t) b) (enum i) j.val

theorem menuInputs_eq (site : X→Expr) (primary : R→Expr) (mate : C→Fin k→Expr) (tree : T→Expr) (qty : U→Expr) :
    (menuInputs extra enum site primary mate tree qty).toLength (menu_shape extra place u pr ma tr enum)=
      packetInputs extra place u pr ma tr enum site primary mate tree qty := rfl

end Hierarchy.WireTelescope.StripPaths

end
end OAI
