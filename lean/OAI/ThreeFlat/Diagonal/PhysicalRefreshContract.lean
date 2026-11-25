import OAI.ThreeFlat.Diagonal.PhysicalRefreshCounts
import OAI.ThreeFlat.Diagonal.PhysicalNumberedRefresh
import OAI.ThreeFlat.Diagonal.PhysicalMoveRefreshWidth
import OAI.ThreeFlat.Diagonal.RefreshPublicationImage
import OAI.ThreeFlat.Diagonal.RefreshPreparationImage

namespace OAI
/-! # Native refresh of a branch of the canonical binary physical history -/

namespace ThreeFlat.Diagonal.PhysicalStage

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression CompressorPacking Native RefreshDemandRows RefreshTies
open RefreshStageNav MotifIntegerChoice
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {F : Type} [Field F] {W s rem h pad : ℕ} {c : Fin (2^s) → Fin (2^s) → ℕ} {C γ : ℝ}
    (T : RefreshMotif.Table F c (1+h+pad) C) (A : State (2^s) (s+rem))
    (hm : 2≤2^s) (hh : 0<h) (sym : ∀ i j,c i j=c j i) (rows : ∀ i,∑ j,c i j=h)
    (zero : ∀ i,c i i=0) (conn : Expander.Bound (Expander.transition c h) ℝ γ)
set_option quotPrecheck false
local notation "Q" => refreshBinaryFamily T A hm hh sym rows zero conn
local notation "M" => refreshBinary T A hm hh sym rows zero conn
local notation "G" => numberedRefreshGraph A
local notation "w" => numberedRefreshWidths A
local notation "E" => DoublePorts.ofMatrix (Equiv.refl _) c sym rows zero

def refreshBaseBound := Finset.univ.sup (fun j=>Finset.univ.sup (T.base j))

theorem refresh_prepare_tile (room : 1+2*2^s*2^s*A.maxWidth+refreshBaseBound T<2^W)
    (u : Block (Fintype.card A.Base) rem) (j : Fin (T.last+1)) (i : RefreshMotif.Ties (2^s)) :
    sentinel (fun e=>SlotImage.demandWidth w (addr (arrival G (tagOrdinal s).symm) u e))+T.base j i<2^W := by
  let z := (numBlockEquiv A).symm u
  have profileEq : profile G (tagOrdinal s).symm (SlotImage.demandWidth w) u =
      profile (refreshBinaryGraph A) (tagOrdinal s).symm (refreshBinaryInput A) z := numProfile_inv A u
  change sentinel (profile G (tagOrdinal s).symm (SlotImage.demandWidth w) u) + T.base j i<_
  rw [profileEq]
  have entry (e) : profile (refreshBinaryGraph A) (tagOrdinal s).symm (refreshBinaryInput A) z e≤A.maxWidth :=
    A.width_le_maxWidth ((StageAddress.refreshEdge (splitWord s rem) (tagOrdinal s).symm).symm
      (addr (arrival (refreshBinaryGraph A) (tagOrdinal s).symm) z e))
  have row : (∑ e,profile (refreshBinaryGraph A) (tagOrdinal s).symm (refreshBinaryInput A) z e)≤
      (2*2^s*2^s)*A.maxWidth := by
    calc
      _ ≤ ∑ _e : Bool × Fin (2^s) × Fin (2^s), A.maxWidth := Finset.sum_le_sum fun e _=>entry e
      _ = _ := by simp [Fintype.card_prod,Nat.mul_assoc]
  have bj : T.base j i≤refreshBaseBound T := by
    unfold refreshBaseBound
    exact (Finset.le_sup (f:=T.base j) (Finset.mem_univ i)).trans
      (Finset.le_sup (f:=fun n => Finset.univ.sup (T.base n)) (Finset.mem_univ j))
  unfold sentinel
  omega

theorem refresh_prepare_physical (cur : Word W) (mem : Memory W) (old : SlotImage.Columns) (split desc : ℕ)
    (st : SlotImage.Stored A.graph A.order (tagOrdinal (s+rem)) old (fun i=>(mem i).val) A.width)
    (layout : PreparationLayout cur mem (Fintype.card A.Base) s rem old split desc)
    (radix : 2^s<2^W) (lanes : 2^rem<2^W) (tiles : T.last+1≤2^W)
    (room : 1+2*2^s*2^s*A.maxWidth+refreshBaseBound T<2^W) :
    let p := preparation cur T.base (fun j=>Fintype.card (T.block j).Alphabet)
    Source cur (p.run mem) G old split w ∧
    ∀ (i : Fin (Q).motifs) (f : Fin 3),
      p.run mem (desc+(i.val*3+f.val))=
        ((if f.val=0 then (Q).copies i else if f.val=1 then
          (T.winner (refreshBinaryGraph A) (tagOrdinal s).symm (refreshBinaryInput A) ((refreshBlockOrder A).symm i)).val
        else Fintype.card ((Q).alphabet i):ℕ):Word W) := by
  obtain ⟨src,rd⟩ := preparation_image cur mem G old split desc w (refreshImage A _ _ st) layout T.base
    (fun j=>Fintype.card (T.block j).Alphabet) radix lanes tiles (refresh_prepare_tile T A room)
  refine ⟨src,?_⟩
  intro i f
  let z := (refreshBlockOrder A).symm i
  have id : blockId (numBlock A z)=i.val := (blockOrder_numeric A z).symm.trans
    (congrArg Fin.val ((refreshBlockOrder A).apply_symm_apply i))
  have read := rd (numBlock A z) f
  rw [id] at read
  exact read.trans (congrArg (fun n : ℕ => (n : Word W))
    (descriptor_real_record T A hm hh sym rows zero conn i f))

def refreshNumericWidths (branch : Fin (M).rules.count) :=
  let x := refreshBinaryBranchOrder T A hm hh sym rows zero conn branch
  freshWidth c rows (termWidth c (SlotImage.demandWidth w)
    (T.widths G (tagOrdinal s).symm (SlotImage.demandWidth w) (numBranches T A x))) pad

theorem refresh_publish_physical (cur : Word W) (mem : Memory W) (old fresh : SlotImage.Columns)
    (split K sparse : ℕ) (st : Source cur mem G old split w)
    (branch : Fin (M).rules.count) (fit : (Q).Fits K W)
    (parsed : ∀ (i : Fin (Q).motifs) (j : Fin K),
      (mem (info (fun x=>(mem x).val) cur 1+i.val*K+j.val)).val=
        (HistogramRegister.words ((Q).rows fit) ((Q).sequence fit branch) i j).val)
    (z : Archive cur mem (Fintype.card A.Base) s rem h pad old fresh split K sparse)
    (bases : Fintype.card A.Base*2^s≤2^W) (lanes : 2^rem<2^W) (deg : 1+h+pad<2^W)
    (rom : 2^s*h≤2^W) (rot : 2*2^s<2^W) (tiles : T.last+1≤2^W)
    (alphabet : refreshSymbolBound T≤K)
    (room : 1+2*2^s*2^s*A.maxWidth+refreshBaseBound T<2^W)
    (widthFit : refreshWidthFactor T*(1+A.maxWidth)<2^W) :
    let p := tablePublish cur E K T rows
    let out := p.run mem
    let next := (M).next branch
    SlotImage.Stored next.graph next.order (tagOrdinal rem) fresh (fun i=>(out i).val) next.width ∧
    SlotImage.Stored (CompressorRefresh.graph G E hm pad) finProdFinEquiv (tagOrdinal rem) fresh
      (fun i=>(out i).val) (refreshNumericWidths T A hm hh sym rows zero conn branch) ∧
    ∀ (u : A.Base × BitWord rem) (pt : Fin (2^s)) (slot : Fin h),
      (out (sparse+(blockId (numBlock A u)*2^s+pt.val)*h+slot.val)).val=
        T.widths (refreshBinaryGraph A) (tagOrdinal s).symm (refreshBinaryInput A)
          (refreshBinaryBranchOrder T A hm hh sym rows zero conn branch) u ((numbering c rows).symm (pt,slot)) := by
  let x := refreshBinaryBranchOrder T A hm hh sym rows zero conn branch
  have output := publication_image cur mem G E hm old fresh split K sparse w st T rows (numBranches T A x) z
    bases lanes deg rom rot tiles (fun j => (Finset.le_sup (Finset.mem_univ j)).trans alphabet)
    (refresh_prepare_tile T A room) (parsed_native T A hm hh sym rows zero conn mem _ fit branch parsed) (by
      intro e
      obtain ⟨u,rfl⟩ := (numFreshEdge A).surjective e
      rw [refreshBinary_width_numeric T A rows hm hh sym zero conn]
      exact (((M).next branch).width_le_maxWidth u).trans_lt ((refreshBinary_width T A hm hh sym rows zero conn branch).trans_lt widthFit))
  refine ⟨refreshBinary_next_image T A rows hm hh sym zero conn branch fresh _ output.1,output.1,?_⟩
  intro u pt slot
  apply (output.2 (numBlock A u) pt slot).trans
  have numbered : numBlockEquiv A u=numBlock A u := by cases u; rfl
  have back : (numBlockEquiv A).symm (numBlock A u)=u := by
    rw [←numbered,Equiv.symm_apply_apply]
  have width := numBranches_width T A x (numBlock A u) ((numbering c rows).symm (pt,slot))
  rw [back] at width
  exact width

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
