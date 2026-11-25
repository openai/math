import OAI.ThreeFlat.Diagonal.PhysicalRefreshBranches

namespace OAI
/-! # The decoded canonical histogram is the numeric publisher's count array -/

namespace ThreeFlat.Diagonal.PhysicalStage

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression CompressorPacking Native RefreshDemandRows RefreshTies
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {F : Type} [Field F] {s rem h pad : ℕ} {c : Fin (2^s) → Fin (2^s) → ℕ} {C γ : ℝ}
    (T : RefreshMotif.Table F c (1+h+pad) C) (A : State (2^s) (s+rem))
    (hm : 2≤2^s) (hh : 0<h) (sym : ∀ i j,c i j=c j i) (rows : ∀ i,∑ j,c i j=h)
    (zero : ∀ i,c i i=0) (conn : Expander.Bound (Expander.transition c h) ℝ γ)
set_option quotPrecheck false
local notation "Q" => refreshBinaryFamily T A hm hh sym rows zero conn
local notation "N" => numberedRefreshGraph A
local notation "NW" => SlotImage.demandWidth (numberedRefreshWidths A)

open private digits from OAI.ThreeFlat.Diagonal.PhysicalRefreshBranches

private theorem symbolAt_live (b : RefreshMotif.Ties (2^s) → ℕ) (xs : digits T b)
    (k : Fin (Fintype.card (T.block (RefreshMotif.selected b T.base)).Alphabet)) :
    symbolAt T b xs k.val = (xs.val ((Fintype.equivFin _).symm k)).val := by
  unfold symbolAt
  rw [dite_eq_left k.isLt]

theorem parsed_native {W K : ℕ} (mem : Memory W) (first : ℕ) (fit : (Q).Fits K W)
    (branch : Fin (refreshBinary T A hm hh sym rows zero conn).rules.count)
    (stored : ∀ (i : Fin (Q).motifs) (j : Fin K),
      (mem (first+i.val*K+j.val)).val = (HistogramRegister.words ((Q).rows fit) ((Q).sequence fit branch) i j).val)
    (u : Block (Fintype.card A.Base) rem) (j : Fin (Fintype.card (T.entry N (tagOrdinal s).symm NW u).Alphabet)) :
    let x := refreshBinaryBranchOrder T A hm hh sym rows zero conn branch
    (mem (first+blockId u*K+j.val)).val=((numBranches T A x u).val ((Fintype.equivFin _).symm j)).val := by
  let z := (numBlockEquiv A).symm u
  let i := refreshBlockOrder A z
  let : Fintype ((Q).alphabet i) := (Q).finiteAlphabet i
  let x := refreshBinaryBranchOrder T A hm hh sym rows zero conn branch
  have idU : numBlock A z=u := (numBlockEquiv A).apply_symm_apply u
  have idI : i.val=blockId u := (blockOrder_numeric A z).trans (congrArg blockId idU)
  have inv : (refreshBlockOrder A).symm i=z := (refreshBlockOrder A).symm_apply_apply z
  have eqn := numProfile_inv A u
  have sizeI : Fintype.card ((Q).alphabet i)=Fintype.card (T.entry N (tagOrdinal s).symm NW u).Alphabet := by
    change Fintype.card (T.block (RefreshMotif.selected
      (profile (refreshBinaryGraph A) (tagOrdinal s).symm (refreshBinaryInput A) ((refreshBlockOrder A).symm i)) T.base)).Alphabet = _
    rw [inv]
    rw [show profile (refreshBinaryGraph A) (tagOrdinal s).symm (refreshBinaryInput A) z=
        profile N (tagOrdinal s).symm NW u from eqn.symm]
  let iSymbol : Fin (Fintype.card ((Q).alphabet i)) := ⟨j.val,by rw [sizeI]; exact j.isLt⟩
  let v := (Fintype.equivFin ((Q).alphabet i)).symm iSymbol
  let slot := (Fintype.equivFin _ v).castLE (fit.1 i)
  have slotId : slot.val=j.val := congrArg Fin.val ((Fintype.equivFin _).apply_symm_apply iSymbol)
  let count := fun zz : A.Base × BitWord rem =>
    symbolAt T (profile (refreshBinaryGraph A) (tagOrdinal s).symm (refreshBinaryInput A) zz)
      (x zz) j.val
  calc
    _ = (HistogramRegister.words ((Q).rows fit) ((Q).sequence fit branch) i slot).val := by
      simpa only [idI,slotId] using stored i slot
    _ = ((x ((refreshBlockOrder A).symm i)).val v).val := refreshBinaryFamily_words T A hm hh sym rows zero conn fit branch i v
    _ = count ((refreshBlockOrder A).symm i) :=
      (symbolAt_live T _ (x ((refreshBlockOrder A).symm i)) iSymbol).symm
    _ = count z := congrArg count inv
    _ = _ := (numBranches_symbol T A x u j.val).symm.trans (by
      unfold symbolAt
      rw [dite_eq_left (show j.val < _ from j.isLt)])


end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
