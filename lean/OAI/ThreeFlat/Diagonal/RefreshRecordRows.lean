import OAI.ThreeFlat.Diagonal.RefreshRecordNative
import OAI.ThreeFlat.Diagonal.RefreshDenseAddress

namespace OAI
/-! # Typed coordinates and true data at the four refresh-node arrays -/

namespace ThreeFlat.Diagonal.RefreshStageNav.Records

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.DescriptorExpr RAM.HeaderScan
open RAM.PhysicalPinsExpr RAM.MotifRows RefreshDemandRows CompressorPacking.Native
open scoped Classical Fin.CommRing

inductive Table where
  | kernel | motif | halfHeader | halves
  deriving DecidableEq

instance : Fintype Table where
  elems := {.kernel, .motif, .halfHeader, .halves}
  complete := by intro q; cases q <;> decide

def Table.start : Table → ℕ
  | .kernel=>34 | .motif=>36 | .halfHeader=>38 | .halves=>40

def Table.cols (d : ℕ) : Table → ℕ
  | .kernel=>5 | .motif=>6 | .halfHeader=>2 | .halves=>8*d

def Table.expression {W : ℕ} (cur : Word W) (m d K : ℕ) : Table → Term W 0 1
  | .kernel=>closed (Records.kernel cur)
  | .motif=>closed (Records.motif cur m K)
  | .halfHeader=>closed (Records.halfHeader cur d)
  | .halves=>closed (Records.halves cur d)

def Table.scan {W : ℕ} (cur : Word W) (m d K : ℕ) (q : Table) :=
  Pipeline.scan cur q.start (q.start+1) (q.expression cur m d K)

structure Pointers where
  kernel : ℕ
  motif : ℕ
  headers : ℕ
  halves : ℕ
  choices : ℕ
  counts : ℕ

def Pointers.dst (p : Pointers) : Table → ℕ
  | .kernel=>p.kernel | .motif=>p.motif | .halfHeader=>p.headers | .halves=>p.halves

abbrev Site (v m t : ℕ) := (Fin v × Fin m) × BitWord t

def siteOrder {v m t : ℕ} : Site v m t ≃ Fin (v*m*2^t) :=
  RefreshStageLayout.pair finProdFinEquiv (tagOrdinal t)

theorem siteOrder_val {v m t : ℕ} (u : Site v m t) :
    (siteOrder u).val=siteId (u.1.1,u.2) u.1.2 := by
  rw [siteOrder,RefreshStageLayout.pair_index]
  change (_+_*_)*2^t+_=_
  simp only [siteId]
  ac_rfl

def rowOrder {v m t : ℕ} (d : ℕ) (q : Table) : Site v m t × Fin (q.cols d) ≃ Fin (v*m*2^t*q.cols d) :=
  RefreshStageLayout.pair siteOrder (Equiv.refl _)

def halfCol {d : ℕ} : Fin (2*d) × Fin 4 ≃ Fin (8*d) := finProdFinEquiv.trans (finCongr (by omega))

theorem halfCol_val {d : ℕ} (j : Fin (2*d)) (f : Fin 4) : (halfCol (j,f)).val=j.val*4+f.val := by
  change f.val+4*j.val=_
  omega

def Table.value {v m d t : ℕ} (P : Pointers) (hd K : ℕ) (G : LiftedSlots (Fin v × Fin m) d (BitWord t))
    (w : SlotImage.Edge (Fin v × Fin m) (BitWord t) d→ℕ) (memory : ℕ→ℕ)
    (q : Table) (r : Site v m t × Fin (q.cols d)) : ℕ :=
  let s := siteId (r.1.1.1,r.1.2) r.1.1.2
  let b := blockId (r.1.1.1,r.1.2)
  let pt := r.1.1.2
  match q,r.2 with
  | .kernel,f=>(![hd,s,2,1,P.motif+s*6]:Fin 5→ℕ) f
  | .motif,f=>(![b,P.counts+b*K,memory (P.choices+b*3+1),memory (P.choices+b*3),0,2^pt.val]:Fin 6→ℕ) f
  | .halfHeader,f=>(![2*d,P.halves+s*(8*d)]:Fin 2→ℕ) f
  | .halves,f=>
    let t := halfCol.symm f
    let e := ShrinkStage.Halves.sourceHalf G r.1 t.1
    (![ShrinkStage.Halves.edgeNumber finProdFinEquiv e,if t.1.val<d then 0 else 1,w e,
      ShrinkStage.Halves.prefixValue G w r.1 t.1] : Fin 4→ℕ) t.2


end ThreeFlat.Diagonal.RefreshStageNav.Records

end OAI
