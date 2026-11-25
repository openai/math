import OAI.ThreeFlat.Diagonal.RefreshWidthNative
import OAI.ThreeFlat.Diagonal.RefreshImageScan

namespace OAI
/-! # The source-major width array equals the actual histogram successor -/

namespace ThreeFlat.Diagonal.RefreshStageNav

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HeaderScan RAM.DescriptorScan
open RAM.MotifRows RefreshDemandRows RefreshTies CompressorPacking.Native MotifIntegerChoice Expander
open scoped Fin.CommRing BigOperators Classical
noncomputable section

variable {W v a t h pad : ℕ} {F : Type} [Field F]
  {c : Fin (mPort a) → Fin (mPort a) → ℕ} {H : ℝ}
  (current : Word W) (m : Memory W)
set_option quotPrecheck false
local notation "N" => fun i=>(m i).val

def numberedWidths (current : Word W) (stride : ℕ)
    (T : RefreshMotif.Table F c (1+h+pad) H) (rows : ∀ p,∑ j,c p j=h) : DescriptorExpr.Term W 0 1 :=
  closed (generateWidth (input current) (field current 8) (index current 19) (field current 1)
    pad stride T.base (fun j => Fintype.card (T.block j).Alphabet) (fun j=>(T.block j).bits) (poolOf T rows))

theorem width_run (G : LiftedSlots (Fin v) (mPort a) (BitWord a × BitWord t))
    (C : SlotImage.Columns) (split : ℕ) (w : SlotImage.RefreshInput v a t → ℕ)
    (s : Source current m G C split w)
    (T : RefreshMotif.Table F c (1+h+pad) H) (rows : ∀ p,∑ j,c p j=h)
    (x : T.Branch G (tagOrdinal a).symm (SlotImage.demandWidth w)) (stride newBase : ℕ)
    (src : info N current 19=newBase) (length : info N current 17=v*mPort a*(1+h+pad)*2^t)
    (capacity : newBase+v*mPort a*(1+h+pad)*2^t<2^W)
    (laneFit : 2^t<2^W) (portFit : mPort a<2^W) (degreeFit : 1+h+pad<2^W) (rowsFit : T.last+1≤2^W)
    (countSpan : info N current 1+v*2^t*stride≤2^W) (alphabet : ∀ j,Fintype.card (T.block j).Alphabet≤ stride)
    (tileFit : ∀ z j i,sentinel (fun l=>SlotImage.demandWidth w (addr (arrival G (tagOrdinal a).symm) z l))
      +T.base j i<2^W)
    (hist : ∀ (u : Block v t) (j : Fin (Fintype.card (T.entry G (tagOrdinal a).symm (SlotImage.demandWidth w) u).Alphabet)),
      (m (info N current 1+blockId u*stride+j.val)).val=((x u).val ((Fintype.equivFin _).symm j)).val)
    (protect : ∀ i, sourceCell current.val (m current.val).val C split (v*mPort a*(mPort a*2^t)) i ∨
      info N current 1≤ i ∧ i< info N current 1+v*2^t*stride →
      i<newBase ∨ newBase+v*mPort a*(1+h+pad)*2^t≤ i) :
    let word := fun (e : LiveSlot (Fin v) (BitWord t) (mPort a) (1+h+pad)) =>
      (freshWidth c rows (termWidth c (SlotImage.demandWidth w) (T.widths G (tagOrdinal a).symm
        (SlotImage.demandWidth w) x)) pad e : Word W)
    (Pipeline.scan current 19 17 (numberedWidths current stride T rows)).run m =
      fillSegment newBase (v*mPort a*(1+h+pad)*2^t) (tableWord RefreshStageLayout.newWords newBase word) m := by
  dsimp only
  have cap := s.headerBound
  apply scan_table current m RefreshStageLayout.newWords _ _ _ _ _ (by omega) src length capacity
  intro e reg m' address frame
  have src' := s.frame m' (fun i hi=>frame _ (protect i (.inl hi)))
  have ptr := frame _ (protect current.val (.inl (Or.inl rfl)))
  have f (off : ℕ) (between : off≤19) :
      info (fun i=>(m' i).val) current off=info N current off := by
    dsimp only [info]
    rw [ptr,frame _ (protect _ (.inl (Or.inr (Or.inl ⟨by omega,by omega⟩))))]
  have atEdge : reg.val=info (fun i=>(m' i).val) current 19+nextIndex e := by
    rw [f 19 (by decide),src,address,RefreshStageLayout.new_index]
    rfl
  apply width_native current m' (fun _=>reg) G C split w src' stride T rows e x atEdge laneFit
    (by omega) portFit degreeFit rowsFit (by rw [f 1 (by decide)]; exact countSpan) alphabet
    (tileFit (e.1.1.1,e.2))
  intro z j
  have b : blockId z<v*2^t := (RefreshStageLayout.block_index z) ▸ (RefreshStageLayout.blocks z).isLt
  have h := Nat.mul_le_mul_right stride b
  rw [Nat.succ_mul] at h
  have jf : j.val<stride := j.isLt.trans_le (alphabet _)
  rw [f 1 (by decide),frame _ (protect _ (.inr ⟨by omega,by omega⟩))]
  exact hist z j

end
end ThreeFlat.Diagonal.RefreshStageNav

end OAI
