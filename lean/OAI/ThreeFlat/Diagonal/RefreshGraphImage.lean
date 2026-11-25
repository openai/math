import OAI.ThreeFlat.Diagonal.RefreshGraphNative
import OAI.ThreeFlat.Diagonal.RefreshImageScan
import OAI.ThreeFlat.Diagonal.RefreshPartyPorts

namespace OAI
/-! # Contiguous memory image of the two oriented successor adjacency maps -/

namespace ThreeFlat.Diagonal.RefreshStageNav

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HeaderScan RAM.DescriptorScan CompressorPacking.Native
open RefreshDemandRows
open scoped Fin.CommRing
noncomputable section

variable {W v a t h pad : ℕ} (current : Word W) (m : Memory W)
set_option quotPrecheck false
local notation "N" => fun i=>(m i).val

abbrev GraphRow (v m h pad : ℕ) := (Bool × Fin 3) × ((Fin v × Fin m) × Fin (1+h+pad))

def graphChart {m : ℕ} : GraphRow v m h pad ≃ Fin (6*(v*m*(1+h+pad))) :=
  ((RefreshParty.bankOrder 3).prodCongr (Equiv.refl _)).trans
    (RefreshStageLayout.pair (Equiv.refl _) RefreshStageLayout.newGraphRows)

theorem graphChart_value {m : ℕ} (C : SlotImage.Columns) (rows : C.rows=v*m*(1+h+pad))
    (q : GraphRow v m h pad) :
    C.graph+(graphChart q).val=SlotImage.cell C finProdFinEquiv q.2 q.1.1 q.1.2 := by
  obtain ⟨⟨b,f⟩,p⟩ := q
  simp only [graphChart,Equiv.trans_apply,Equiv.prodCongr_apply,Prod.map_apply,Equiv.refl_apply,RefreshStageLayout.pair_index,
    RefreshStageLayout.newGraphRows,RefreshStageLayout.oldGraphRows,RefreshParty.bank_index,SlotImage.cell,
    SlotImage.column,SlotImage.ordinal,rows]
  change _ = C.graph+(v*m*(1+h+pad))*((if b then 3 else 0)+f.val)+
    ((p.1.2.val+m*p.1.1.val)*(1+h+pad)+p.2.val)
  ac_rfl

theorem graph_run (G : LiftedSlots (Fin v) (mPort a) (BitWord a × BitWord t))
    (E : SlotGraph (Fin (mPort a)) h) (hm : 2≤ mPort a) (C : SlotImage.Columns)
    (split : ℕ) (w : SlotImage.RefreshInput v a t → ℕ) (s : Source current m G C split w)
    (next : SlotImage.Columns) (src : info N current 14=next.graph)
    (len : info N current 15=next.rows) (span : info N current 16=6*next.rows) (count : next.rows=v*mPort a*(1+h+pad))
    (oldCap : C.graph+6*C.rows<2^W) (shiftCap : split+3*C.rows<2^W)
    (inside : next.graph+6*next.rows<2^W) (deg : 1+h+pad<2^W) (rom : mPort a*h≤2^W) (rot : 2*mPort a<2^W)
    (protect : ∀ i, sourceCell current.val (m current.val).val C split (v*mPort a*(mPort a*2^t)) i →
      i<next.graph ∨ next.graph+6*next.rows≤ i) :
    let words := fun q : GraphRow v (mPort a) h pad =>
      ((SlotImage.fields (CompressorRefresh.graph G E hm pad) finProdFinEquiv (tagOrdinal t) q.2 q.1.1 q.1.2 : ℕ):Word W)
    (Pipeline.scan current 14 16 (graphWords current E pad)).run m =
      fillSegment next.graph (6*(v*mPort a*(1+h+pad))) (tableWord graphChart next.graph words) m := by
  dsimp only
  apply scan_table current m graphChart _ _ _ _ _ (by have := s.headerBound; omega) src
    (by rw [span,count]) (by rwa [←count])
  intro q x m' addr frame
  rw [←count] at frame
  have src' := s.frame m' (fun i hi=>frame _ (protect i hi))
  have ptr := frame _ (protect current.val (Or.inl rfl))
  have header (off : ℕ) (between : off≤19) :
      info (fun i=>(m' i).val) current off=info N current off := by
    dsimp only [info]
    rw [ptr,frame _ (protect _ (Or.inr (Or.inl ⟨by omega,by omega⟩)))]
  exact graph_native current m' G E hm C split w src' next ((header 14 (by decide)).trans src)
    ((header 15 (by decide)).trans len) count oldCap shiftCap inside deg rom rot q.2 q.1.1 q.1.2
    (fun _=>x) (addr.trans (graphChart_value next count q))

end
end ThreeFlat.Diagonal.RefreshStageNav

end OAI
