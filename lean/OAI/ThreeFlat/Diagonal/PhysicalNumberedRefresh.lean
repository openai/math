import OAI.ThreeFlat.Diagonal.PhysicalRefreshBranches
import OAI.ThreeFlat.Diagonal.RefreshWidthPhysical
import OAI.ThreeFlat.Diagonal.RefreshGraphChart

namespace OAI
/-! # The emitted arc widths are the exact next state's labels in its numerical chart -/

namespace ThreeFlat.Diagonal.PhysicalStage

open Computability.VPVNP.Compression CompressorPacking Native RefreshDemandRows RefreshTies Expander
open scoped Classical BigOperators
noncomputable section

variable {F : Type} [Field F] {s rem h pad : ℕ} {c : Fin (2^s) → Fin (2^s) → ℕ} {C γ : ℝ}
    (T : RefreshMotif.Table F c (1+h+pad) C) (A : State (2^s) (s+rem))
    (rows : ∀ i,∑ j,c i j=h)

def numFreshEdge : LiveSlot A.Base (BitWord rem) (2^s) (1+h+pad) ≃
    LiveSlot (Fin (Fintype.card A.Base)) (BitWord rem) (2^s) (1+h+pad) :=
  SlotImage.baseEdges (A.order.prodCongr (Equiv.refl _))

theorem width_numeric (x : refreshBinaryBranches T A) (e : LiveSlot A.Base (BitWord rem) (2^s) (1+h+pad)) :
    freshWidth c rows (termWidth c (SlotImage.demandWidth (numberedRefreshWidths A))
      (T.widths (numberedRefreshGraph A) (tagOrdinal s).symm (SlotImage.demandWidth (numberedRefreshWidths A))
        (numBranches T A x))) pad (numFreshEdge A e) =
    freshWidth c rows (termWidth c (refreshBinaryInput A)
      (T.widths (refreshBinaryGraph A) (tagOrdinal s).symm (refreshBinaryInput A) x)) pad e := by
  obtain ⟨⟨⟨v,p⟩,i⟩,l⟩ := e
  let z := (v,l)
  rw [←numbered_width_eq,←numbered_width_eq]
  apply congrArg₂ (numberedWidth p i.val)
  · funext q
    apply Finset.sum_congr rfl
    intro j _
    exact numWidth A (z,j,q)
  · funext q t
    have h := numBranches_width T A x (numBlock A z) ((numbering c rows).symm (q,t))
    have back : (numBlockEquiv A).symm (numBlock A z) = z :=
      (numBlockEquiv A).symm_apply_apply z
    rw [back] at h
    exact h

theorem refreshBinary_width_numeric
    (hm : 2≤2^s) (hh : 0<h) (sym : ∀ i j,c i j=c j i) (zero : ∀ i,c i i=0)
    (conn : Expander.Bound (Expander.transition c h) ℝ γ)
    (j : Fin (refreshBinary T A hm hh sym rows zero conn).rules.count)
    (e : LiveSlot A.Base (BitWord rem) (2^s) (1+h+pad)) :
    let x := refreshBinaryBranchOrder T A hm hh sym rows zero conn j
    freshWidth c rows (termWidth c (SlotImage.demandWidth (numberedRefreshWidths A))
      (T.widths (numberedRefreshGraph A) (tagOrdinal s).symm (SlotImage.demandWidth (numberedRefreshWidths A))
        (numBranches T A x))) pad (numFreshEdge A e) =
    ((refreshBinary T A hm hh sym rows zero conn).next j).width e :=
  width_numeric T A rows _ e

/-- The public output slot image describes the exact graph, in the
physical branch's mixed-radix base order, and its dependent width labels. -/
theorem refreshBinary_next_image
    (hm : 2≤2^s) (hh : 0<h) (sym : ∀ i j,c i j=c j i) (zero : ∀ i,c i i=0)
    (conn : Expander.Bound (Expander.transition c h) ℝ γ)
    (j : Fin (refreshBinary T A hm hh sym rows zero conn).rules.count)
    (col : SlotImage.Columns) (mem : ℕ→ℕ) :
    let x := refreshBinaryBranchOrder T A hm hh sym rows zero conn j
    let w := freshWidth c rows (termWidth c (SlotImage.demandWidth (numberedRefreshWidths A))
      (T.widths (numberedRefreshGraph A) (tagOrdinal s).symm (SlotImage.demandWidth (numberedRefreshWidths A))
        (numBranches T A x))) pad
    let N := (refreshBinary T A hm hh sym rows zero conn).next j
    SlotImage.Stored (outputGraph (numberedRefreshGraph A) c sym rows zero hm pad) finProdFinEquiv
      (tagOrdinal rem) col mem w →
    SlotImage.Stored N.graph N.order (tagOrdinal rem) col mem N.width := by
  dsimp only
  intro stored
  have changeBase := (SlotImage.ownChart (refreshBinaryGraph A) A.order).refresh
    (DoublePorts.ofMatrix (Equiv.refl _) c sym rows zero) hm pad
  apply changeBase.pull_stored _ finProdFinEquiv _ _
    (fun p=>by rfl) col mem _ _ (fun e=>refreshBinary_width_numeric T A rows hm hh sym zero conn j e) stored
  change Fintype.card (A.Base × Fin (2^s)) = Fintype.card A.Base * 2^s
  simp


end

end ThreeFlat.Diagonal.PhysicalStage

end OAI
