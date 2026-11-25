import OAI.Computability.BorderVNP.DiagonalTallyOperandWriter
import OAI.Computability.BorderVNP.DiagonalTallyCellReports
import OAI.Computability.BorderVNP.DiagonalTallyPacketEvidence

/-! # Reading physically relocated cell report operands -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyOperandArray

open VPVNP.BurstRAM VPVNP.TapeWord RoutingISA DiagonalTallyPacketEmit
open DiagonalTallyMaterialize DiagonalTallyGather
open private refsAt_of_index from OAI.Computability.BorderVNP.DiagonalTallyPacketEvidence

/-- Every output field and physical bit reference of one completed writer block. -/
structure Frame.ArraysAt (f : Frame) (k : Kind) (m : ℕ → ℕ) : Prop where
  /-- The five consecutive fields for each native operand. -/
  descriptor : ∀ i < 5*f.nrows k, m (f.descriptors+i)=f.field k i
  /-- The absolute addresses read later by the gather operation. -/
  reference : ∀ i < f.nrefs k, m (f.refs+i)=f.refValue k i

/-- On disjoint reference and descriptor intervals the actual writer image supplies both. -/
theorem Frame.arraysAt_image (f : Frame) (k : Kind) (m : ℕ → ℕ)
    (apart : f.refs+f.nrefs k ≤ f.descriptors ∨ f.descriptors+5*f.nrows k ≤ f.refs) :
    f.ArraysAt k (f.image k m) := by
  constructor
  · exact fun _ hi => written_at _ _ _ hi
  · intro i hi
    unfold Frame.image
    have outside : ¬(f.descriptors ≤ f.refs+i ∧ f.refs+i-f.descriptors<5*f.nrows k) := by omega
    rw [written,ite_eq_right outside,written_at _ _ _ hi]

/-- Count bits are gathered most-significant first from their real external addresses. -/
def Frame.countDigits (f : Frame) (g : Fin f.gadgets) (bits : Fin f.width → Bool) : List (ℕ × Bool) :=
  (List.ofFn fun j => (f.external+g.val*f.width+j.val,bits j)).reverse

/-- Unlike private bit-bank indices, these count operands name absolute shared memory. -/
def Frame.countRow (f : Frame) (g : Fin f.gadgets) (bits : Fin f.width → Bool) : Operand :=
  ⟨f.parameters+g.val,f.zeroAddr,0,f.refs+g.val*f.width,f.countDigits g bits,f.zeroAddr,0⟩

/-- Address relocation preserves the reported value and its gadget coordinate. -/
theorem Frame.count_pair (f : Frame) (g : Fin f.gadgets) (bits : Fin f.width → Bool) :
    (f.countRow g bits).pair=(f.parameters+g.val,value (List.ofFn bits)) := by
  simp [countRow,countDigits,Operand.pair,List.map_ofFn,Function.comp_def,readDigits_reverse]

private theorem rows (f : Frame) (k : Kind) (m : ℕ → ℕ) (a : f.ArraysAt k m)
    {i j : ℕ} (hi : i<f.nrows k) (hj : j<5) :
    m (f.descriptors+5*i+j)=f.field k (5*i+j) := by
  rw [Nat.add_assoc,a.descriptor _ (by omega)]

/-- The actual allocated five-word count record dereferences the whole canonical count field,
including its little-endian bit order, with no dependence on private-bank offsets. -/
theorem Frame.count_resident {w : ℕ} (f : Frame) (m : Memory w) (a : f.ArraysAt .count (readings m))
    (zero : (m f.zeroAddr).val=0) (g : Fin f.gadgets) (bits : Fin f.width → Bool)
    (data : ∀ j : Fin f.width, (m (f.external+g.val*f.width+j.val)).val=(bits j).toNat) :
    (f.countRow g bits).resident m (f.descriptors+5*g.val) := by
  have hrow (j : ℕ) (hj : j<5) := rows f .count (readings m) a (i := g.val) g.isLt hj
  have r0 := hrow 0 (by decide)
  have r1 := hrow 1 (by decide)
  have r2 := hrow 2 (by decide)
  have r3 := hrow 3 (by decide)
  have r4 := hrow 4 (by decide)
  simp [field,Nat.mul_add_div (by decide : 0<5),readings] at r0 r1 r2 r3 r4
  have hlen : (f.countDigits g bits).length=f.width := by simp [countDigits]
  refine ⟨r0,r1,zero,r2,?_,r4,zero,?_⟩
  · simpa only [countRow,hlen] using r3
  · apply refsAt_of_index
    intro j hj
    change j<(f.countDigits g bits).length at hj
    rw [hlen] at hj
    let t : Fin f.width := ⟨f.width-1-j,by omega⟩
    have rd : (f.countDigits g bits)[j]'(by rwa [hlen])=(f.external+g.val*f.width+t.val,bits t) := by
      simp [countDigits,List.getElem_reverse,t]
    change (m (f.refs+g.val*f.width+j)).val=(f.countDigits g bits)[j].1 ∧
      (m (f.countDigits g bits)[j].1).val=(f.countDigits g bits)[j].2.toNat
    rw [rd]
    have he := Nat.mul_le_mul_right f.width g.isLt
    rw [Nat.succ_mul] at he
    have ref := a.reference (g.val*f.width+j) (by change _<f.gadgets*f.width; omega)
    simp only [readings,refValue,Nat.mul_add_mod_of_lt hj] at ref
    simp only [t]
    exact ⟨by simpa [Nat.add_assoc] using ref,data t⟩

/-- Each actual marked copy names the decoded one-copy parameter and place,
and exactly one bit in the owner's compact use bank. -/
theorem Frame.unary_resident {w : ℕ} (f : Frame) (m : Memory w) (a : f.ArraysAt .unary (readings m))
    (i : ℕ) (hi : i<f.marked*f.copies) (param place : ℕ) (b : Bool)
    (paramAt : (m (f.side+3*(i/f.copies)+1)).val=param)
    (placeAt : (m (f.side+3*(i/f.copies)+1+1)).val=place)
    (bitAt : (m (f.external+i)).val=b.toNat) :
    (unaryOperand (f.side+3*(i/f.copies)+1) (f.side+3*(i/f.copies)+1+1) (f.refs+i)
      (f.external+i) param place b).resident m (f.descriptors+5*i) := by
  have hrow (j : ℕ) (hj : j<5) := rows f .unary (readings m) a (i := i) hi hj
  have r0 := hrow 0 (by decide)
  have r1 := hrow 1 (by decide)
  have r2 := hrow 2 (by decide)
  have r3 := hrow 3 (by decide)
  have r4 := hrow 4 (by decide)
  simp [field,Nat.mul_add_div (by decide : 0<5),readings] at r0 r1 r2 r3 r4
  exact ⟨by rw [r0]; rfl,r1,paramAt,r2,r3,r4,placeAt,a.reference i hi,bitAt,trivial⟩

end DiagonalTallyOperandArray

end BorderVNP
end Computability
end OAI
