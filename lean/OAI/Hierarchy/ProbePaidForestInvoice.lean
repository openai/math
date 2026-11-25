import OAI.Hierarchy.ProbePaidActualForest
import OAI.Hierarchy.ProbeFixedOriginalPrice

namespace OAI
/-! # The native tree walk's exact charge on its original dense core IDs -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard AdaptiveProbe Strip StockCommit
open LinearAlgebra.SpectralBooks ChordGraph
open scoped Classical Fin.CommRing BigOperators

variable {h d k n w : ℕ} {S : PurchaseSampler} {Extra : Type}
local notation "Link" => TreeLink n k
local notation "Ports" => StripPorts S h d k (TreeColumn n) (Fin n) Extra

/-- Parallel hops keep their multiplicity in the actual traversal List.
For each native ID, the original scalar width tariff is used. -/
theorem original_tree_invoice (p : Ports) (b : Board) (order : Fin b.coreRows≃Edges S h d k)
    (m : Memory w) (row : ℕ) (pos : 0<b.coreRows) (wide : b.rows<2^w)
    (loaded : CoreLookup.Loaded p.directory order m) (col : TreeColumn n → Columns h d)
    (column : ∀c,((p.column c).eval m (row:Word w)).val=((Fintype.equivFin _) (col c)).val)
    (M : ℕ) (horizontal : ∀e,∃f : Edges S h d k,
      (p.horizontal e none).eval m (row:Word w)=((order.symm f).val:Word w) ∧ (coreCode S M f:ℝ)≤1)
    (len : Fin b.rows→ℝ) (cost : ∀f,len (b.coreIndex (order.symm f))=(coreCode S M f : ℝ)) :
    ((broadcastWalk p b m row pos).map len).sum≤(Fintype.card Link : ℝ)*max (M:ℝ) 1 := by
  have bound (l : Link) : len (b.coreIndex (treeTarget p b m row l pos))≤ max (M:ℝ) 1 := by
    have code (f : Edges S h d k) (hit : (treeTerm p b l).eval m (row:Word w)=((order.symm f).val:Word w)) :
        len (b.coreIndex (treeTarget p b m row l pos))=(coreCode S M f:ℝ) := by
      rw [treeTarget_true p b m row l (order.symm f) pos ((congrArg Fin.val hit).trans
        (Fin.val_cast_of_lt ((b.coreIndex (order.symm f)).isLt.trans wide))),cost]
    rcases l with e|⟨c,j,side⟩
    · obtain ⟨f, hit, cheap⟩ := horizontal e
      have read := b.coreOnly_read (p.horizontal e none) m (row : Word w) (order.symm f) wide hit
      exact (code f read).le.trans (cheap.trans (le_max_right _ _))
    · let f : Edges S h d k := .inl (.inl (col c, j, side))
      let key : Fin (CoreLookup.positions h d) :=
        ⟨_, ((Fintype.equivFin _) (col c)).isLt.trans_le (Nat.le_max_left _ _)⟩
      have hit := loaded.read (CoreLookup.radius j side) (p.column c) (row : Word w) key (column c) f
        (CoreLookup.resolve_radius (col c) j side)
      have read := b.coreOnly_read (p.radiusAt c j side) m (row : Word w) (order.symm f) wide hit
      exact (code f read).le.trans (le_max_left (M : ℝ) 1)
  simp only [broadcastWalk,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  exact (Finset.sum_le_sum (fun i _=>bound ((Fintype.equivFin Link).symm i))).trans_eq (by simp)

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
