import OAI.Hierarchy.ProbeCatalystPortSupport
import OAI.Hierarchy.ProbeCatalystPlacedDebit

namespace OAI
/-! # Physical inputs of a posted strip and its finite menu -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.CatalystArchive
open AdaptiveProbe ColumnWires Computability.VPVNP.BurstRAM PrivateRAM Calendar Calendar.StockCommit PurchaseStage RepairHistogram
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped BigOperators Classical Fin.CommRing

variable {A B C H F : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype H] [Field F]
  {k sites N : ℕ} [Nonempty (Fin sites)] [Nonempty (Fin k)] [Nonempty (Role C H (A⊕B) k)]
  {M ε tree : ℝ} {len : H→ℝ} {cap : A→ℝ}
local notation "Roles" => Role C H (A⊕B) k
local notation "needRoles" => demand (I:=C) (H:=H) (k:=k) (Sum.inl (α:=A) (β:=B))
local notation "prices" => (fun y:A→ℝ => quote (I:=C) (k:=k) M len (LocalCommodity.extraPrice (B:=B) y)) '' Set.Icc 0 cap

variable {e : Role C H (A⊕B) k → Chord sites}

set_option maxHeartbeats 1200000
/-- These are the integer and address-room requirements on the actual physical
input. In particular no resulting catalyst, sign, debit, or amount is a field. -/
structure StripInput (menu : Probe.FixedMenu F e needRoles prices ε tree N) (w z d q D : ℕ) where
  addr : A→Expr
  active : Expr
  board : StripDirectory.Boards z d k q (Fintype.card A) (Fintype.card Roles)
  prior : ℕ
  start : ℕ
  mem : Memory w
  ports : Fintype.card Roles≤D
  loaded : (⟨start,(nativeStrip (A:=A) (B:=B) (C:=C) (H:=H) (k:=k) (z:=z) (d:=d) (q:=q) menu addr active board prior).market.rows,D⟩ : PortHeader).Loaded mem
  portFit : D≤2^w
  termFit : q≤2^w
  copyFit : board.copies<2^w
  sumFit : q*board.copies<2^w
  codeFit : 1+Fintype.card menu.index≤2^w
  maximum : (PacketWidths.ofMenu menu).maximum≤board.maxWidth
  fieldFit : board.maxWidth<2^w
  wide : board.copies*board.maxWidth<2^w
  bankFit :
    (PortPadding.format D start (nativeSlot (B:=B) (H:=H) (C:=C) (k:=k) addr active)
      (nativeStrip (A:=A) (B:=B) (C:=C) (H:=H) (k:=k) (z:=z) (d:=d) (q:=q)
        menu addr active board prior)).pricedArea.start +
      (nativeStrip (A:=A) (B:=B) (C:=C) (H:=H) (k:=k) (z:=z) (d:=d) (q:=q)
        menu addr active board prior).coordinates < 2^w

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
