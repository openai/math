import OAI.ThreeFlat.Diagonal.RefreshSuccessorImage
import OAI.ThreeFlat.Diagonal.RefreshSparseCopy

namespace OAI
/-! # The third publication sweep and its archive of per-motif supply widths -/

namespace ThreeFlat.Diagonal.RefreshStageNav

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HeaderScan CompressorPacking.Native
open RefreshDemandRows RefreshTies
open scoped Classical Fin.CommRing
noncomputable section

variable {W v a t h pad : ℕ} (current : Word W) (m : Memory W)

def apart (lo n i : ℕ) := i<lo ∨ lo+n≤ i

theorem info_frame {m' : Memory W} (n : ℕ) (keep : ∀ i,i=current.val ∨
    (m current.val).val≤ i ∧ i≤(m current.val).val+n → m' i=m i) (j : ℕ) (hj : j≤n) :
    info (fun i=>(m' i).val) current j=info (fun i => (m i).val) current j := by
  dsimp [info]
  rw [keep _ (.inl rfl),keep _ (.inr ⟨by omega,by omega⟩)]

theorem sparse_run (G : LiftedSlots (Fin v) (mPort a) (BitWord a × BitWord t))
    (E : SlotGraph (Fin (mPort a)) h) (hm : 2≤ mPort a) (C : SlotImage.Columns)
    (w : LiveSlot (Fin v) (BitWord t) (mPort a) (1+h+pad) → ℕ)
    (_stored : SlotImage.Stored (CompressorRefresh.graph G E hm pad) finProdFinEquiv (tagOrdinal t) C (fun i => (m i).val) w)
    (dst : ℕ) (head : (m current.val).val+20<2^W)
    (shift : info (fun i => (m i).val) current 8=2^t) (widths : info (fun i => (m i).val) current 19=C.widths)
    (ptr : info (fun i => (m i).val) current 3=dst) (length : info (fun i => (m i).val) current 20=v*2^t*mPort a*h)
    (cap : dst+v*2^t*mPort a*h<2^W)
    (widthCap : C.widths+v*mPort a*(1+h+pad)*2^t≤2^W)
    (ports : mPort a<2^W) (degree : h<2^W)
    (protect : ∀ i,i=current.val ∨ (m current.val).val≤ i ∧ i≤(m current.val).val+20 ∨
      C.widths≤ i ∧ i<C.widths+v*mPort a*(1+h+pad)*2^t → apart dst (v*2^t*mPort a*h) i) :
    let words := fun q : ((Block v t × Fin (mPort a)) × Fin h) =>
      m (C.widths+nextIndex (sparseSlot (pad:=pad) q.1.1 q.1.2 q.2))
    (Pipeline.scan current 3 20 (closed (sparseCopy (mPort a) h pad current))).run m =
      fillSegment dst (v*2^t*mPort a*h) (tableWord (RefreshStageLayout.sparseEntries (pad:=pad)) dst words) m := by
  dsimp only
  apply scan_table current m (RefreshStageLayout.sparseEntries (pad:=pad)) _ _ _ _ _ (by omega) ptr length cap
  rintro ⟨⟨z,p⟩,s⟩ reg m' addr frame
  have fptr := frame _ (protect _ (.inl rfl))
  have headers (j : ℕ) (hj : j≤20) := info_frame current m 20 (m':=m')
    (fun _ q=>frame _ (protect _ (q.imp_right Or.inl))) j hj
  have atSlot := sparse_native (pad:=pad) current m' (fun _=>reg) z p s (by rw [fptr]; omega) ports degree
    ((headers 8 (by decide)).trans shift)
    (by rw [headers _ (by decide),ptr,addr,RefreshStageLayout.sparse_index]; omega)
    (by rw [headers _ (by decide),widths]; exact widthCap)
  rw [atSlot,headers _ (by decide),widths]
  have key := (RefreshStageLayout.newWords (sparseSlot (pad:=pad) z p s)).isLt
  rw [RefreshStageLayout.new_index] at key
  change nextIndex (sparseSlot (pad:=pad) z p s) < v*mPort a*(1+h+pad)*2^t at key
  exact frame _ (protect _ (.inr (.inr ⟨Nat.le_add_right ..,Nat.add_lt_add_left key _⟩)))


end
end ThreeFlat.Diagonal.RefreshStageNav

end OAI
