import OAI.ThreeFlat.Diagonal.PhysicalLocalTariff
import OAI.ThreeFlat.Diagonal.ShrinkAssemblyOrder
import OAI.ThreeFlat.Diagonal.ShrinkActiveCopyBudget

namespace OAI
/-! # Tariff, sorter height and census of the elected shrink tiles -/

namespace ThreeFlat.Diagonal.PhysicalStage.Block
open LinearAlgebra.SpectralBooks Computability.VPVNP.Compression CompressorPacking PhysicalShrink HistoryContraction MotifKernel
open MotifOuterTerms
open scoped Classical BigOperators
noncomputable section

variable {F : Type} [Field F] [Fintype F] (B : Block F)
  {V H Tag L : Type} [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
  [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
  {d c : ℕ} (P : PackingData V H Tag L d c) (old : Arc V H Tag L d c → ℕ)
  (code : Arc V H Tag L d c ↪ ℕ) (hc : 2≤c)

private def tileChoice (m : P.Motif) :=
  RefreshDemandRows.tileNumber (PhysicalShrink.b P old code hc m) (B.shrink.base ∘ B.shrink.row)

omit [Fintype F] in
private theorem choice_row (m : P.Motif) :
    B.shrink.row (tileChoice B P old code hc m) = picked B.shrink P old code hc m :=
  B.shrink.row_chosen _

omit [Fintype F] in
theorem elected_tile_price (m : P.Motif) :
    shrinkTariff P (widths B.shrink P old code hc) (tile B.shrink P old code hc) m ≤ B.shrinkPrice := by
  let price (row : B.shrink.Row) := Tree.tileTariff demandGraph supplyGraph (B.shrink.base row)
    (B.shrink.block row).bits (Fintype.card (B.shrink.block row).Alphabet) (B.shrink.block row).bitCap
  exact (congrArg price (choice_row B P old code hc m)).symm.le.trans
    (B.shrink_tile_price (tileChoice B P old code hc m))

omit [Fintype F] in
theorem elected_tile_height (m : P.Motif) {K W : ℕ} (copies : r B.shrink P old code hc m≤K)
    (bitCaps : ∀ i, (B.shrink.block (B.shrink.row i)).bitCap≤K)
    (fitsWord : K*max 1 K≤2^W) :
    HistogramTileNetwork.siteHeight (r B.shrink P old code hc m) (tile B.shrink P old code hc m).bitCap≤W := by
  have maximum : (tile B.shrink P old code hc m).bitCap≤K := by
    exact (congrArg (fun row => (B.shrink.block row).bitCap) (choice_row B P old code hc m)).symm.le.trans
      (bitCaps (tileChoice B P old code hc m))
  apply Nat.clog_le_of_le_pow
  apply le_trans _ fitsWord
  refine max_le ?_ (Nat.mul_le_mul copies (maximum.trans (le_max_right ..)))
  exact copies.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left K (le_max_left 1 K))

theorem elected_count_bound (layout : Bool) (v : Site V Tag L) :
    Local.assemblyCount P layout v ≤ 8*d^2*2^c := by
  have count := Fintype.card_congr (Local.assemblyOrder P layout v)
  have bound := (Local.active_copies_bound P layout (fun _ => 1) (R:=1) (fun _ => le_rfl)).2 v
  simp only [Local.activeCopiesAt,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.mul_one] at bound
  simpa only [Fintype.card_fin] using count.trans_le bound

end
end ThreeFlat.Diagonal.PhysicalStage.Block

end OAI
