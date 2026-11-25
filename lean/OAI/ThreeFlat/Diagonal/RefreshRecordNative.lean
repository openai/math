import OAI.ThreeFlat.Diagonal.RefreshRecordFits
import OAI.ThreeFlat.Diagonal.CompressorHalfFits
import OAI.ThreeFlat.Diagonal.SlotImageViews

namespace OAI
/-! # True machine-word reads for all four retained node record tables -/

namespace ThreeFlat.Diagonal.RefreshStageNav.Records

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HeaderScan RAM.PhysicalPinsExpr RAM.MotifRows
open RefreshDemandRows CompressorPacking.Native
open scoped Fin.CommRing
variable {W t v m : ℕ} (cur : Word W) (mem : Memory W) (vs : Fin 1 → Word W)
private abbrev memoryValues (mem : Memory W) (i : ℕ) : ℕ := (mem i).val
private abbrev registerValues (vs : Fin 1 → Word W) (i : Fin 1) : ℕ := (vs i).val
private abbrev fieldValue (mem : Memory W) (vs : Fin 1 → Word W) :=
  Formula.natural W (fun _ : Param => 0) (memoryValues mem) (registerValues vs)

theorem kernel_native (s : ℕ) (f : Fin 5) (head : (mem cur.val).val+40<2^W) (small : 6<2^W)
    (a : (vs 0).val=info (memoryValues mem) cur 34+s*5+f.val) :
    (closed (kernel cur)).eval Fin.elim0 mem vs=
      ((![(memoryValues mem) cur.val,s,2,1,info (memoryValues mem) cur 36+s*6] : Fin 5 → ℕ) f:Word W) :=
  closed_read mem vs _ (kernel_fit cur mem vs head small) (kernel_read cur (fun _ : Param => 0) (memoryValues mem) (registerValues vs) s f a)

theorem motif_native (K : ℕ) (z : Block v t) (p : Fin m) (f : Fin 6)
    (head : (mem cur.val).val+40<2^W) (small : 6<2^W) (ports : m<2^W)
    (lanes : info (memoryValues mem) cur 8=2^t) (addr : (vs 0).val=info (memoryValues mem) cur 36+siteId z p*6+f.val)
    (room : info (memoryValues mem) cur 2+blockId z*3+1<2^W) :
    let b := blockId z
    let c := info (memoryValues mem) cur 2+b*3
    (closed (motif cur m K)).eval Fin.elim0 mem vs=
      ((![b,info (memoryValues mem) cur 1+b*K,(memoryValues mem) (c+1),(memoryValues mem) c,0,2^p.val] : Fin 6 → ℕ) f:Word W) :=
  closed_read mem vs _ (motif_fit cur mem vs K z p f head small ports lanes addr room)
    (motif_read cur (fun _ : Param => 0) (memoryValues mem) (registerValues vs) z p K f lanes addr)

theorem halfHeader_native (d s : ℕ) (f : Fin 2) (head : (mem cur.val).val+40<2^W) (small : 6<2^W)
    (a : (vs 0).val=info (memoryValues mem) cur 38+s*2+f.val) :
    (closed (halfHeader cur d)).eval Fin.elim0 mem vs=
      ((![2*d,info (memoryValues mem) cur 40+s*(8*d)] : Fin 2 → ℕ) f:Word W) :=
  closed_read mem vs _ (halfHeader_fit cur mem vs d head small) (halfHeader_read cur (fun _ : Param => 0) (memoryValues mem) (registerValues vs) d s f a)

theorem halves_native {B : Type} {d u : ℕ} (G : LiftedSlots B d (BitWord t)) (base : B ≃ Fin u)
    (C : SlotImage.Columns) (w : SlotImage.Edge B (BitWord t) d → ℕ)
    (stored : SlotImage.Stored G base (tagOrdinal t) C (memoryValues mem) w)
    (p : B × BitWord t) (j : Fin (2*d)) (f : Fin 4)
    (head : (mem cur.val).val+40<2^W) (small : 4<2^W) (degree : 2*d<2^W) (lanes : 2^t<2^W)
    (h8 : info (memoryValues mem) cur 8=2^t) (h14 : info (memoryValues mem) cur 14=C.graph) (h15 : info (memoryValues mem) cur 15=C.rows)
    (h19 : info (memoryValues mem) cur 19=C.widths)
    (gg : C.graph+6*C.rows≤2^W) (ww : C.widths+u*d*2^t≤2^W)
    (addr : (vs 0).val=info (memoryValues mem) cur 40+(ShrinkStage.Halves.siteNumber base p*(2*d)+j.val)*4+f.val) :
    let e := ShrinkStage.Halves.sourceHalf G p j
    (closed (halves cur d)).eval Fin.elim0 mem vs=
      ((![ShrinkStage.Halves.edgeNumber base e,if j.val<d then 0 else 1,w e,
        ShrinkStage.Halves.prefixValue G w p j] : Fin 4 → ℕ) f:Word W) := by
  let q := halfColumns cur
  have cols : q.layout (fieldValue mem vs)=⟨2^t,C.graph,C.rows,C.widths⟩ := by
    change ShrinkStage.Halves.Layout.mk (info (memoryValues mem) cur 8) (info (memoryValues mem) cur 14) (info (memoryValues mem) cur 15) (info (memoryValues mem) cur 19)=_
    rw [h8,h14,h15,h19]
  have st : ShrinkStage.Halves.Stored G base (q.layout (fieldValue mem vs)) (memoryValues mem) w := cols.symm ▸ SlotImage.forHalves stored
  have region : ShrinkStage.Halves.Region (W:=W) (fun _ : Param => 0) (memoryValues mem) (registerValues vs) q u d t := by
    refine ⟨⟨field_fit cur mem vs 8 (by omega),field_fit cur mem vs 14 (by omega),
      field_fit cur mem vs 15 (by omega),field_fit cur mem vs 19 (by omega)⟩,h15.trans stored.rowCount,?_,?_,degree,lanes⟩
    · change info (memoryValues mem) cur 14+6*(u*d)≤_
      rwa [h14,←stored.rowCount]
    · change info (memoryValues mem) cur 19+_≤_
      rwa [h19]
  let x := index cur 40
  have pos : (fieldValue mem vs) x=(ShrinkStage.Halves.siteNumber base p*(2*d)+j.val)*4+f.val := by
    change (vs 0).val-info (memoryValues mem) cur 40=_
    omega
  have fx := index_fit cur mem vs 40 head
  have bx : (fieldValue mem vs) x<2^W := (Nat.sub_le _ _).trans_lt (vs 0).isLt
  exact closed_read mem vs _ (ShrinkStage.Halves.record_fits (fun _ : Param => 0) (memoryValues mem) (registerValues vs) q st region x p j f fx bx small pos)
    (ShrinkStage.Halves.record_read W (fun _ : Param => 0) (memoryValues mem) (registerValues vs) q st x p j f pos)


end ThreeFlat.Diagonal.RefreshStageNav.Records

end OAI
