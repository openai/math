import OAI.ThreeFlat.Diagonal.RefreshArchiveLayout
import OAI.ThreeFlat.Diagonal.RefreshStageRuns

namespace OAI
/-! # Successor image of the complete native refresh publication program -/

namespace ThreeFlat.Diagonal.RefreshStageNav

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HeaderScan RAM.DescriptorScan
open RefreshDemandRows RefreshTies CompressorPacking.Native MotifIntegerChoice
open scoped Classical Fin.CommRing BigOperators
noncomputable section

variable {W v a t h pad : ℕ} {F : Type} [Field F]
    {c : Fin (mPort a) → Fin (mPort a) → ℕ} {H : ℝ}
    (current : Word W) (m : Memory W)

def tablePublish (current : Word W) (E : SlotGraph (Fin (mPort a)) h) (stride : ℕ)
    (T : RefreshMotif.Table F c (1+h+pad) H) (rows : ∀ p,∑ j,c p j=h) :=
  publication current E pad stride T.base (fun j=>Fintype.card (T.block j).Alphabet)
    (fun j=>(T.block j).bits) (poolOf T rows)

private theorem tablePublish_run (E : SlotGraph (Fin (mPort a)) h) (stride : ℕ)
    (T : RefreshMotif.Table F c (1+h+pad) H) (rows : ∀ p,∑ j,c p j=h) :
    (tablePublish current E stride T rows).run m =
      (Pipeline.scan current 3 20 (closed (sparseCopy (mPort a) h pad current))).run
        ((Pipeline.scan current 19 17 (numberedWidths current stride T rows)).run
          ((Pipeline.scan current 14 16 (graphWords current E pad)).run m)) := rfl

private theorem sparse_fill_at {v t d h : ℕ} (pad sparse : ℕ)
    (labels : (Block v t × Fin d) × Fin h → Word W)
    (u : Block v t) (p : Fin d) (j : Fin h) :
    fillSegment sparse (v*2^t*d*h)
        (tableWord (RefreshStageLayout.sparseEntries (pad:=pad)) sparse labels) m
        (sparse+(blockId u*d+p.val)*h+j.val) = labels ((u,p),j) := by
  let entry := RefreshStageLayout.sparseEntries (pad:=pad) ((u,p),j)
  have index : entry.val=(blockId u*d+p.val)*h+j.val := RefreshStageLayout.sparse_index u p j
  have bound : entry.val<v*2^t*d*h := entry.isLt
  have address : sparse+(blockId u*d+p.val)*h+j.val=sparse+entry.val := by rw [index]; omega
  rw [address]
  have inside : sparse ≤ sparse+entry.val ∧ sparse+entry.val < sparse+v*2^t*d*h :=
    ⟨Nat.le_add_right _ _,Nat.add_lt_add_left bound sparse⟩
  rw [fillSegment,ite_eq_left inside]
  exact tableWord_at _ _ _ _

attribute [local irreducible] Pipeline.scan tablePublish graphWords numberedWidths

set_option maxHeartbeats 800000 in
/-- All three native sweeps publish one successor. The only supplied input
values are the old graph image, the parsed histogram, and header addresses. -/
theorem publication_image (G : LiftedSlots (Fin v) (mPort a) (BitWord a × BitWord t))
    (E : SlotGraph (Fin (mPort a)) h) (hm : 2≤ mPort a) (old fresh : SlotImage.Columns)
    (split stride sparse : ℕ) (w : SlotImage.RefreshInput v a t → ℕ) (s : Source current m G old split w)
    (T : RefreshMotif.Table F c (1+h+pad) H) (rows : ∀ p,∑ j,c p j=h)
    (x : T.Branch G (tagOrdinal a).symm (SlotImage.demandWidth w))
    (z : Archive current m v a t h pad old fresh split stride sparse)
    (bases : v*mPort a≤2^W) (lanes : 2^t<2^W) (deg : 1+h+pad<2^W)
    (rom : mPort a*h≤2^W) (rot : 2*mPort a<2^W) (tableFit : T.last+1≤2^W)
    (alphabet : ∀ j,Fintype.card (T.block j).Alphabet≤ stride)
    (tileFit : ∀ z j i,sentinel (fun l=>SlotImage.demandWidth w (addr (arrival G (tagOrdinal a).symm) z l))
      +T.base j i<2^W)
    (hist : ∀ (u : Block v t) (j : Fin (Fintype.card (T.entry G (tagOrdinal a).symm (SlotImage.demandWidth w) u).Alphabet)),
      (m (info (fun i => (m i).val) current 1+blockId u*stride+j.val)).val=((x u).val ((Fintype.equivFin _).symm j)).val)
    (safeWord : ∀ e,freshWidth c rows (termWidth c (SlotImage.demandWidth w) (T.widths G
      (tagOrdinal a).symm (SlotImage.demandWidth w) x)) pad e<2^W) :
    let next := fun e=>freshWidth c rows (termWidth c (SlotImage.demandWidth w)
      (T.widths G (tagOrdinal a).symm (SlotImage.demandWidth w) x)) pad e
    let program := tablePublish current E stride T rows
    let out := program.run m
    SlotImage.Stored (CompressorRefresh.graph G E hm pad) finProdFinEquiv (tagOrdinal t) fresh
      (fun i=>(out i).val) next ∧
    ∀ (u : Block v t) (p : Fin (mPort a)) (j : Fin h),
      (out (sparse+(blockId u*mPort a+p.val)*h+j.val)).val=
        T.widths G (tagOrdinal a).symm (SlotImage.demandWidth w) x u ((numbering c rows).symm (p,j)) := by
  let d := mPort a
  let nGraph := 6*(v*d*(1+h+pad))
  let nWidth := v*d*(1+h+pad)*2^t
  let nSparse := v*2^t*d*h
  let next := freshWidth c rows (termWidth c (SlotImage.demandWidth w)
      (T.widths G (tagOrdinal a).symm (SlotImage.demandWidth w) x)) pad
  let gr := Pipeline.scan current 14 16 (graphWords current E pad)
  let wr := Pipeline.scan current 19 17 (numberedWidths current stride T rows)
  let sr := Pipeline.scan current 3 20 (closed (sparseCopy d h pad current))
  let m1 := gr.run m
  let m2 := wr.run m1
  let m3 := sr.run m2
  dsimp only
  rw [tablePublish_run]
  have ge : m1=fillSegment fresh.graph nGraph (tableWord graphChart fresh.graph (outputFields G E hm pad)) m :=
    graph_run current m G E hm old split w s fresh z.graph z.rows z.edges z.count z.oldGraphFit z.splitFit
      z.graphFit deg rom rot (fun i h=>(z.oldSafe i (.inl h)).1)
  have gKeep (i : ℕ) (q : apart fresh.graph (6*fresh.rows) i) : m1 i=m i := by
    rw [ge]
    exact segment_other m _ _ _ _ (by simpa only [apart,nGraph,d,←z.count] using q)
  have source1 := s.frame m1 (fun i hi=>gKeep i (z.oldSafe i (.inl hi)).1)
  have f1 (off : ℕ) (ho : off≤20) := info_frame current m 20 (m':=m1)
    (fun i hi=>gKeep i (z.header_outside i hi).1) off ho
  have ptr1 := gKeep _ (z.header_outside current.val (.inl rfl)).1
  have wRun : m2=fillSegment fresh.widths nWidth
      (tableWord RefreshStageLayout.newWords fresh.widths (fun e=>(next e:Word W))) m1 := by
    apply width_run current m1 G old split w source1 T rows x stride fresh.widths
      ((f1 19 (by decide)).trans z.widths) ((f1 17 (by decide)).trans z.wires)
      z.widthFit lanes (by omega) deg tableFit (by rw [f1 1 (by decide)]; exact z.countFit) alphabet tileFit
    · intro u j
      rw [f1 1 (by decide),gKeep]
      · exact hist u j
      · exact (z.oldSafe _ (.inr (.inr (by
          have hu := (RefreshStageLayout.blocks u).isLt
          rw [RefreshStageLayout.block_index] at hu
          have hj := j.isLt.trans_le (alphabet _)
          have := (Nat.add_lt_add_left hj (blockId u*stride)).trans_le (by
            simpa only [Nat.succ_mul] using Nat.mul_le_mul_right stride hu)
          omega)))).1
    · intro i hi
      rw [ptr1,f1 1 (by decide)] at hi
      exact (z.oldSafe i (hi.imp_right Or.inr)).2
  have wKeep (i : ℕ) (q : apart fresh.widths nWidth i) : m2 i=m1 i := by
    rw [wRun]
    exact segment_other m1 _ _ _ _ q
  have keep2 (i : ℕ) (q : i=current.val ∨ (m current.val).val≤ i ∧ i≤(m current.val).val+20) : m2 i=m i :=
    (wKeep i (z.header_outside i q).2).trans (gKeep i (z.header_outside i q).1)
  have f2 (off : ℕ) (ho : off≤20) := info_frame current m 20 (m':=m2) keep2 off ho
  have ptr2 := keep2 _ (.inl rfl)
  have image2 : SlotImage.Stored (CompressorRefresh.graph G E hm pad) finProdFinEquiv (tagOrdinal t) fresh
      (fun i=>(m2 i).val) next := by
    rw [wRun,ge]
    exact successor_image m G E hm fresh next z.count z.separate bases deg.le lanes.le safeWord
  let labels := fun q : ((Block v t × Fin d) × Fin h)=>m2 (fresh.widths+nextIndex
    (sparseSlot (pad:=pad) q.1.1 q.1.2 q.2))
  have se : m3=fillSegment sparse nSparse
      (tableWord (RefreshStageLayout.sparseEntries (pad:=pad)) sparse labels) m2 := by
    apply sparse_run current m2 G E hm fresh next image2 sparse (by rw [ptr2]; exact z.head)
      ((f2 8 (by decide)).trans s.remaining) ((f2 19 (by decide)).trans z.widths)
      ((f2 3 (by decide)).trans z.supplies) ((f2 20 (by decide)).trans z.supplyWords)
      z.supplyFit z.widthFit.le (by omega) (by omega)
    intro i hi
    rw [ptr2] at hi
    exact z.lastSafe i (hi.imp_right (fun q=>q.imp_right Or.inr))
  have sKeep (i : ℕ) (q : apart sparse nSparse i) : m3 i=m2 i := by
    rw [se]
    exact segment_other m2 _ _ _ _ q
  constructor
  · apply image2.frame
    · intro i ha hb
      exact congrArg Fin.val (sKeep i (z.lastSafe i (.inr (.inr (.inl ⟨ha,hb⟩)))))
    · intro i ha hb
      exact congrArg Fin.val (sKeep i (z.lastSafe i (.inr (.inr (.inr ⟨ha,hb⟩)))))
  · intro u p j
    change (m3 _).val=_
    let e := sparseSlot (pad:=pad) u p j
    rw [se,sparse_fill_at m2 pad sparse labels u p j]
    change (m2 (fresh.widths+nextIndex e)).val=_
    have key : SlotImage.edgeOrdinal finProdFinEquiv (tagOrdinal t) e=nextIndex e := by
      change (((e.1.1.2.val+d*e.1.1.1.val)*(1+h+pad)+e.1.2.val)*2^t+(tagOrdinal t e.2).val)=_
      unfold nextIndex
      ac_rfl
    rw [←key,image2.widthWord]
    exact sparse_width c rows (SlotImage.demandWidth w) _ u p j


end
end ThreeFlat.Diagonal.RefreshStageNav

end OAI
