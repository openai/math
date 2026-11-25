import OAI.Hierarchy.TaggedWidePacketFields
import OAI.Hierarchy.TaggedWideDatedAddresses

namespace OAI
/-! # Immutable party program using the actual width and opposite pages of the dated ballot -/
noncomputable section
namespace Hierarchy.WireTelescope.StripPaths
open LinearAlgebra.SpectralBooks ChordGraph Probe AdaptiveProbe AdaptiveProbe.Strip
open ProtocolRAM PacketTurns ProbeStage.CoreBoard.HistoryRoles
variable {n k N K Rn Tn D : ℕ} {A B Ball : Type}
variable (extra : A⊕B→DistinctPair (TreeSite n k))
    (enum : Fin Rn≃(ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k⊕TreeLink n k))
    (ord : Fin Tn≃Σi,Fin (menuLen (enum i)))
    (site : TreeSite n k→Expr) (primary : ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k→Expr)
    (mate : TreeColumn n→Fin k→Expr) (tree : TreeLink n k→Expr)
    (qty : (ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k⊕TreeLink n k)→Expr)
local notation "menuOp" => menuInputs extra enum site primary mate tree qty
variable (place : Ball×TreeSite n k↪Fin K) (u : Ball)
    (pr : ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k→Fin N)
    (ma : TreeColumn n→Fin k→Fin N) (tr : TreeLink n k→Fin N)
local notation "actual" => packetInputs extra place u pr ma tr enum site primary mate tree qty
local notation "rank" => menuOrder extra place u pr ma tr enum ord

theorem same_control (M : ℕ) (width nbr : Fin D→Expr) (here : Expr) :
    (actual).controls rank M width nbr here=(menuOp).controls ord M width nbr here := by
  funext f
  unfold Operands.controls
  split
  · split
    · apply congrFun (same_field extra place u pr ma tr enum ord site primary mate tree qty width nbr here)
    · rfl
  · simp only [Operands.lowAfter,same_low extra place u pr ma tr enum ord site primary mate tree qty]

/-- The two charts share all numeric positions. Here is the party's emitted
suffix, with both port metadata arrays read from its completed dated replay. -/
def menuControls (M : ℕ) (originalRows pageStart shelfSize pageBits : ℕ) (siteBase : Bank) (here : Expr) :
    Fin ((M*3)*5+D)→Expr := (menuOp).controls ord M
      (pageRead (DatedRoleSheets.bank originalRows pageStart shelfSize pageBits 0) siteBase here)
      (pageRead (DatedRoleSheets.bank originalRows pageStart shelfSize pageBits 2) siteBase here) here

theorem menuControls_eq (M : ℕ) (nrows start total bits : ℕ) (siteBase : Bank) (here : Expr) :
    menuControls (D:=D) extra enum ord site primary mate tree qty M nrows start total bits siteBase here=
      (actual).controls rank M
        (pageRead (DatedRoleSheets.bank nrows start total bits 0) siteBase here)
        (pageRead (DatedRoleSheets.bank nrows start total bits 2) siteBase here) here :=
  (same_control extra enum ord site primary mate tree qty place u pr ma tr M _ _ here).symm

variable {native out budget : ℕ} (M nrows start total bits : ℕ) (siteBase : Bank) (here : Expr)
local notation "bank" => DatedRoleSheets.bank nrows start total bits

theorem menuControls_fits (resident : (actual).Resident native out)
    (room : ∀f : Fin 3,(bank f).Fits native out) (stride : siteBase.Fits native out) (loc : here.Fits native out)
    (f : Fin ((M*3)*5+D)) :
    (menuControls extra enum ord site primary mate tree qty M nrows start total bits siteBase here f).Fits native out := by
  rw [menuControls_eq extra enum ord site primary mate tree qty place u pr ma tr]
  apply Operands.controls_fits _ _ resident _ _ here _ _ loc
  · intro q;exact page_fits _ _ _ _ (room 0) stride loc
  · intro q;exact page_fits _ _ _ _ (room 2) stride loc

theorem menuControls_work (budgeted : (actual).Bound budget) (loc : here.work+12≤budget)
    (f : Fin ((M*3)*5+D)) :
    (menuControls extra enum ord site primary mate tree qty M nrows start total bits siteBase here f).work≤
      128*(Tn+D+1)*(budget+1) := by
  rw [menuControls_eq extra enum ord site primary mate tree qty place u pr ma tr]
  apply le_trans _ (Operands.controlWork_le Tn D budget)
  apply Operands.controls_work _ _ budgeted _ _ here _ _ (by omega)
  all_goals intro q;simpa only [page_work] using loc

end Hierarchy.WireTelescope.StripPaths

end
end OAI
