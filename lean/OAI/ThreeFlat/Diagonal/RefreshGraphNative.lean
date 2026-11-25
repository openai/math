import OAI.ThreeFlat.Diagonal.RefreshChoiceImage
import OAI.ThreeFlat.Diagonal.RefreshGraphInput

namespace OAI
/-! # The refresh publisher writes the successor's six physical columns -/

namespace ThreeFlat.Diagonal.RefreshStageNav

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HeaderScan RAM.DescriptorScan CompressorPacking.Native
open RefreshDemandRows
open scoped Fin.CommRing

variable {W v a t h pad : ℕ} (current : Word W) (m : Memory W)
set_option quotPrecheck false
local notation "N" => fun i=>(m i).val

private theorem natHeader (off value : ℕ) (cap : (m current.val).val+off<2^W)
    (read : info N current off=value) : headerWord m current off=(value:Word W) := by
  rw [←read,←header_val current m off cap,Fin.cast_val_eq_self]

set_option maxHeartbeats 2000000 in
theorem graph_native (G : LiftedSlots (Fin v) (mPort a) (BitWord a × BitWord t))
    (E : SlotGraph (Fin (mPort a)) h) (hm : 2≤ mPort a) (C : SlotImage.Columns)
    (split : ℕ) (w : SlotImage.RefreshInput v a t → ℕ) (s : Source current m G C split w)
    (next : SlotImage.Columns) (src : info N current 14=next.graph)
    (len : info N current 15=next.rows) (count : next.rows=v*mPort a*(1+h+pad))
    (oldCap : C.graph+6*C.rows<2^W) (shiftCap : split+3*C.rows<2^W)
    (inside : next.graph+6*next.rows<2^W) (deg : 1+h+pad<2^W)
    (rom : mPort a*h≤2^W) (rot : 2*mPort a<2^W)
    (x : (Fin v × Fin (mPort a)) × Fin (1+h+pad)) (back : Bool) (f : Fin 3)
    (vs : Fin 1 → Word W) (atWord : (vs 0).val=SlotImage.cell next finProdFinEquiv x back f) :
    (graphWords current E pad).eval Fin.elim0 m vs=
      ((SlotImage.fields (CompressorRefresh.graph G E hm pad) finProdFinEquiv (tagOrdinal t) x back f:ℕ):Word W) := by
  have cap := s.headerBound
  have native := nativeGraphInput current G C split Fin.elim0 m vs s.image s.shifts
    (natHeader current m 10 _ (by omega) s.graph) (natHeader current m 11 _ (by omega) s.rows)
    (natHeader current m 12 _ (by omega) s.splitBase) oldCap shiftCap
  have zero : (tagOrdinal t (0:BitWord t)).val=0 := by
    simpa only [zero_add,Nat.xor_self] using tagOrdinal_add (0:BitWord t) 0
  let start : DescriptorExpr.Term W 0 1 := closed (field current 14)
  let length : DescriptorExpr.Term W 0 1 := closed (field current 15)
  have base : start.eval Fin.elim0 m vs=(next.graph:Word W) :=
    (closed_field current 14 _ _ _).trans (natHeader current m 14 _ (by omega) src)
  have size : length.eval Fin.elim0 m vs=((v*mPort a*(1+h+pad):ℕ):Word W) :=
    (closed_field current 15 _ _ _).trans (natHeader current m 15 _ (by omega) (len.trans count))
  apply Refresh.six_graph_read G E hm (tagOrdinal t) zero pad (graphOld current) start length Fin.elim0 m vs
    native x back f next.graph base size (count ▸ inside) (by omega) deg (by omega) rom rot
  have index : vs 0=((SlotImage.cell next finProdFinEquiv x back f:ℕ):Word W) := by
    rw [←atWord,Fin.cast_val_eq_self]
  simpa only [SlotImage.cell,count] using index

end ThreeFlat.Diagonal.RefreshStageNav

end OAI
