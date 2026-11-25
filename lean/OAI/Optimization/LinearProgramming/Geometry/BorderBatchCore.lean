import OAI.Optimization.LinearProgramming.Geometry.BorderBatchFrame
import OAI.Optimization.LinearProgramming.Geometry.BorderDescriptors

/-! Materialize every signed prefix minor using a single fixed RAM block, preserving
all public matrix entries, prices, pivot indices and previously rounded rows. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch
open RAM RAM.Block Matrix Compression Compression.MinorLoad

/-- The complete scalar-free descriptor constructor followed by the signed determinant service. -/
def prepare : Block := .seq prepareDescriptors (batchBlock determinantBlock)

theorem prepare_run {r n k B : ℕ} {L : Layout r n} {D : Matrix (Fin r) (Fin n) ℚ}
    {price : Fin n → ℚ} {base m : Memory ℚ} {rows : Fin k → PivotRow n} (e g H : ℕ)
    (input : Inputs L D price B base) (hk : k+1≤r) (hrn : r≤n) (hmat : ∀ i j, ratBits (D i j) ≤ e)
    (previous : PivotPrefixRAM.Stored base m rows price B) (keep : PreservesInput L base m) (safe : RowRAM.Within H m) :
    ∃ v cost, cost ≤ 41*(r+n+1)^2+(n*(2200*(n+1)^7+17)+2) ∧
      Eval (RowRAM.Within (H+batchIncrement n e g)) prepare m cost v ∧ PivotPrefixRAM.Stored base v rows price B ∧
      PreservesInput L base v ∧ ∀ j : Fin n, v.data (L.answers+j.val) = borderedMinor (D.submatrix (Fin.castLE hk) id) (fun i => (rows i).pivot) j := by
  let J := fun i => (rows i).pivot
  let W := H+batchIncrement n e g
  let P := fun q : ℚ => ratBits q≤W
  have Wdet : max H (detRegisterBits n e) ≤ W := by dsimp [W,batchIncrement]; omega
  have ready := input.ready previous keep
  obtain ⟨u,desc,_,table,udata,uindices⟩ := prepareDescriptors_spec (fun q => ratBits q≤H) m safe L D hk J ready
  obtain ⟨v,kv,hkv,det,raw,vdata,vindices⟩ := signed_border_batch D J L hk hrn u table H e desc.safe_end hmat
  have detData (p : ℕ) (lo : 32≤p) (hi : p<L.answers) : v.data p=m.data p := (vdata _ (by omega) hi).trans (congrFun udata _)
  have detIndices (p : ℕ) (lo : 128≤p) (hi : p<L.headers) : v.index p=m.index p := by
    have he := L.headers_end; have re := L.rows_end
    exact (vindices _ (by omega)).trans (uindices _ lo (Or.inl hi) (Or.inl (by omega)) (Or.inl (by omega)))
  have sg := L.source_ge; have sp := L.source_end; have lp := L.prices_end; have lt' := L.triples_end; have la := L.rounded_end
  have vs := stored_after_border_frame input previous (by omega) (fun p lo hi _ => detIndices p lo hi) (fun p lo hi => detData p (by omega) hi)
  have keepV : PreservesInput L base v := fun p lo hi => (detData p lo (by omega)).trans (keep p lo hi)
  have dWide := PowerRAM.weaken (Q := Memory.AllData P) desc (fun _ h p => (h p).trans ((le_max_left H (detRegisterBits n e)).trans Wdet))
  have vWide := PowerRAM.weaken (Q := Memory.AllData P) det (fun _ h p => (h p).trans Wdet)
  have time := prepareDescriptors_steps_le hk n
  refine ⟨v,_,?_,dWide.seq vWide,vs,keepV,raw⟩
  omega

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
