import OAI.ThreeFlat.Diagonal.RefreshSparseImage
import OAI.ThreeFlat.Diagonal.RefreshWidthImage

namespace OAI
/-! # Numerical allocation conditions for one real refresh publication -/

namespace ThreeFlat.Diagonal.RefreshStageNav

open Computability.VPVNP.BurstRAM PrivateRAM RAM CompressorPacking.Native RefreshDemandRows
open scoped Fin.CommRing

variable {W : ℕ} (current : Word W) (m : Memory W)

/-- Three disjoint output arrays. The old graph, its widths and the admitted
histogram remain readable during both construction sweeps. -/
structure Archive (v a t h pad : ℕ) (old fresh : SlotImage.Columns) (split stride sparse : ℕ) : Prop where
  head : (m current.val).val+20<2^W
  graph : info (fun i => (m i).val) current 14=fresh.graph
  rows : info (fun i => (m i).val) current 15=fresh.rows
  edges : info (fun i => (m i).val) current 16=6*fresh.rows
  count : fresh.rows=v*mPort a*(1+h+pad)
  widths : info (fun i => (m i).val) current 19=fresh.widths
  wires : info (fun i => (m i).val) current 17=v*mPort a*(1+h+pad)*2^t
  supplies : info (fun i => (m i).val) current 3=sparse
  supplyWords : info (fun i => (m i).val) current 20=v*2^t*mPort a*h
  graphFit : fresh.graph+6*fresh.rows<2^W
  widthFit : fresh.widths+v*mPort a*(1+h+pad)*2^t<2^W
  supplyFit : sparse+v*2^t*mPort a*h<2^W
  oldGraphFit : old.graph+6*old.rows<2^W
  splitFit : split+3*old.rows<2^W
  countFit : info (fun i => (m i).val) current 1+v*2^t*stride≤2^W
  separate : fresh.graph+6*fresh.rows≤fresh.widths ∨ fresh.widths+v*mPort a*(1+h+pad)*2^t≤fresh.graph
  oldSafe : ∀ i, sourceCell current.val (m current.val).val old split (v*mPort a*(mPort a*2^t)) i ∨
      i=(m current.val).val+20 ∨ info (fun i => (m i).val) current 1≤ i ∧ i< info (fun i => (m i).val) current 1+v*2^t*stride →
      apart fresh.graph (6*fresh.rows) i ∧ apart fresh.widths (v*mPort a*(1+h+pad)*2^t) i
  lastSafe : ∀ i, i=current.val ∨ (m current.val).val≤ i ∧ i≤(m current.val).val+20 ∨
      fresh.graph≤ i ∧ i<fresh.graph+6*fresh.rows ∨ fresh.widths≤ i ∧ i<fresh.widths+v*mPort a*(1+h+pad)*2^t →
      apart sparse (v*2^t*mPort a*h) i

namespace Archive

variable {current m} {v a t h pad split stride sparse : ℕ} {old fresh : SlotImage.Columns}
    (z : Archive current m v a t h pad old fresh split stride sparse)

include z in
theorem header_outside (i : ℕ) (inHead : i=current.val ∨
    (m current.val).val≤ i ∧ i≤(m current.val).val+20) :
    apart fresh.graph (6*fresh.rows) i ∧ apart fresh.widths (v*mPort a*(1+h+pad)*2^t) i := by
  rcases inHead with p|⟨p,q⟩
  · exact z.oldSafe _ (.inl (.inl p))
  · by_cases b : i≤(m current.val).val+19
    · exact z.oldSafe _ (.inl (.inr (.inl ⟨p,b⟩)))
    · exact z.oldSafe _ (.inr (.inl (by omega)))


end Archive
end ThreeFlat.Diagonal.RefreshStageNav

end OAI
