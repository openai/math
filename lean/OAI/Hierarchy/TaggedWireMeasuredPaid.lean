import OAI.Hierarchy.TaggedWireRowCredit
import OAI.Hierarchy.ProtocolRAMFinalInstalledWidths
import OAI.Hierarchy.ProtocolRAMCalendarCommitLayout

namespace OAI
/-! # Original row decomposition of both archives of paid installation widths -/

namespace Hierarchy.ProtocolRAM.Calendar.StockCommit
open Computability.VPVNP.BurstRAM PrivateRAM RepairHistogram
open scoped BigOperators Classical Fin.CommRing
noncomputable section

variable {W q d rows edges : ℕ} (a : Area) (s : Sources) (g : LabelSource)
    (mask mate : Expr) (v m : Memory W) (e : Fin edges)

def primaryHit (i : Fin a.occurrences) : Prop :=
  kind (goods:=a.goods) (fresh a s).plan.bank (fresh a s).columns v i=none ∧
    (g.edge.eval m (i.val:Word W)).val=e.val

def secondaryHit (i : Fin a.occurrences) : Prop :=
  kind (goods:=a.goods) (fresh a s).plan.bank (fresh a s).columns v i=none ∧
    mask.eval m (i.val:Word W)≠0 ∧ (mate.eval m (i.val:Word W)).val=e.val

variable {b : Batch q d} (L : PortPlan (fresh a s) b v rows)
  (wide : a.occurrences≤2^W)
  (archive : ∀i : Fin a.occurrences,
    (m (a.direct+i.val)).val =
      if kind (goods:=a.goods) (fresh a s).plan.bank (fresh a s).columns v i=none then
        installedBits (fresh a s).columns v i else 0)

include wide archive in
theorem primary_load :
    (PaidWidths.paidDirect a s g).load m e =
      ∑ j, L.rowCredit j (primaryHit a s g v m e) := by
  refine Eq.trans ?_ (L.sum_rowCredit (primaryHit a s g v m e)).symm
  change (∑ i : Fin a.occurrences, if (g.edge.eval m (i.val : Word W)).val = e.val then
    ((PaidWidths.paidDirect a s g).amount.eval m (i.val : Word W)).val else 0) =
    ∑ i : Fin a.occurrences, if primaryHit a s g v m e i then installedBits (fresh a s).columns v i else 0
  apply Finset.sum_congr rfl
  intro i _
  rw [PaidWidths.paidDirect_bits _ _ _ m i wide,archive]
  unfold primaryHit
  split_ifs <;> simp_all

include wide archive in
theorem secondary_load :
    (PaidWidths.paidMate a s mask mate).load m e =
      ∑ j, L.rowCredit j (secondaryHit a s mask mate v m e) := by
  refine Eq.trans ?_ (L.sum_rowCredit (secondaryHit a s mask mate v m e)).symm
  change (∑ i : Fin a.occurrences, if (mate.eval m (i.val : Word W)).val = e.val then
    ((PaidWidths.paidMate a s mask mate).amount.eval m (i.val : Word W)).val else 0) =
    ∑ i : Fin a.occurrences, if secondaryHit a s mask mate v m e i then installedBits (fresh a s).columns v i else 0
  apply Finset.sum_congr rfl
  intro i _
  rw [PaidWidths.paidMate_bits _ _ _ _ m i wide,archive]
  unfold secondaryHit
  split_ifs <;> simp_all

end
end Hierarchy.ProtocolRAM.Calendar.StockCommit

end OAI
