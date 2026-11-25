import OAI.Optimization.LinearProgramming.Lattice.BitState
import OAI.Optimization.LinearProgramming.Lattice.LLLBitSweep
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Size

/-! Polynomial lengths of the exact framed bit encodings of integral LLL states. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

private theorem signedWord_length (z : ℤ) : (intCode z).length = z.natAbs.size + 3 := by
  simp [intCode,intData,prodCode,pairBits_length,boolCode,Nat.size_eq_bits_len]
  omega

private theorem packedVector_length {α : Type} {n : ℕ} (ea : α → List Bool) (v : Vector α n)
    (B : ℕ) (h : ∀ k, (ea (v.get k)).length ≤ B) :
    (listCode ea (packVector v)).length ≤ n*(2*B+2)+1 := by
  unfold packVector
  rw [List.ofFn_eq_map]
  simpa only [List.length_finRange] using listCode_length_map_bound ea (fun i => v.get i)
    (List.finRange n) B (fun j _ => h j)

/-- Size in bits of the complete signed row-major table, including its row frames. -/
theorem packedMatrix_length {n m : ℕ} (a : Hex.Matrix ℤ n m) (B : ℕ)
    (h : ∀ i j, ((a.getRow i).get j).natAbs.size ≤ B) :
    (intMatrixCode (packMatrix a)).length ≤ n*(2*(m*(2*(B+3)+2)+1)+2)+1 := by
  unfold intMatrixCode packMatrix
  rw [List.ofFn_eq_map]
  apply (listCode_length_map_bound intRowCode (fun i => packVector (a.getRow i))
    (List.finRange n) (m*(2*(B+3)+2)+1) ?_).trans_eq
  · rw [List.length_finRange]
  · intro i _
    apply packedVector_length
    intro j
    rw [signedWord_length]
    exact Nat.add_le_add_right (h i j) 3

/-- A single cubic bound covers the cursor plus the complete basis, scaled Gram–Schmidt
coefficients, and principal determinants. Its input bounds dimensions *and* bit lengths. -/
theorem packedSweep_length {n m : ℕ} (s : Hex.Internal.LLLState n m) (j k W : ℕ)
    (hn : n ≤ W) (hm : m ≤ W) (hj : j.size ≤ W) (hk : k.size ≤ W)
    (hb : ∀ i l, ((s.b.getRow i).get l).natAbs.size ≤ W)
    (hν : ∀ i l, ((s.ν.getRow i).get l).natAbs.size ≤ W)
    (hd : ∀ i, (s.d.get i).size ≤ W) :
    (sweepCode stateCode (j,k,packState s)).length ≤ 100*(W+1)^3 := by
  have ht := packedMatrix_length s.b W hb
  have hv := packedMatrix_length s.ν W hν
  have hg := packedVector_length Nat.bits s.d W (fun i => by simpa only [← Nat.size_eq_bits_len] using hd i)
  simp only [sweepCode,stateCode,packState,gramListCode,prodCode,pairBits_length,Nat.size_eq_bits_len]
  calc
    _ ≤ 2*W+(2*W+(2*(W*(2*(W*(2*(W+3)+2)+1)+2)+1)+
      (2*(W*(2*(W*(2*(W+3)+2)+1)+2)+1)+((W+1)*(2*W+2)+1)+1)+1)+1)+1 := by
      gcongr
      · exact ht.trans (by gcongr)
      · exact hv.trans (by gcongr)
      · exact hg.trans (by gcongr)
    _ ≤ 100*(W+1)^3 := by ring_nf; omega

/-- Dimensions and every input coefficient width are bounded by the actual encoded
integer matrix presented to the machine. A positive row count exposes its column count. -/
theorem packedMatrix_input_bounds {n m : ℕ} (b : Hex.Matrix ℤ n m) (hn : 0 < n) :
    let L := (intMatrixCode (packMatrix b)).length
    n ≤ L ∧ m ≤ L ∧ ∀ i j, ((b.getRow i).get j).natAbs.size ≤ L := by
  have hrows := list_length_le_code intRowCode (packMatrix b)
  rw [length_packMatrix] at hrows
  have rowBound (i : Fin n) : (intRowCode (packVector (b.getRow i))).length ≤
      (intMatrixCode (packMatrix b)).length := by
    apply code_le_of_mem intRowCode
    exact List.mem_ofFn.mpr ⟨i,rfl⟩
  have hcols := list_length_le_code intCode (packVector (b.getRow ⟨0,hn⟩))
  rw [length_packVector] at hcols
  refine ⟨hrows,hcols.trans (rowBound ⟨0,hn⟩),?_⟩
  intro i j
  have he : (b.getRow i).get j ∈ packVector (b.getRow i) := List.mem_ofFn.mpr ⟨j,rfl⟩
  have hh := (code_le_of_mem intCode he).trans (rowBound i)
  rw [signedWord_length] at hh
  omega

/-- A framed matrix with `n` rows provides at least `n` physical clock ticks. -/
theorem packedCursor_rows_le {n m : ℕ} (s : Hex.Internal.LLLState n m) (k : ℕ) :
    n ≤ (cursorCode (k,packState s)).length := by
  have h := list_length_le_code intRowCode (packMatrix s.b)
  rw [length_packMatrix] at h
  simp only [cursorCode,stateCode,packState,prodCode,pairBits_length]
  change n ≤ 2*(Nat.bits k).length+(2*(listCode intRowCode (packMatrix s.b)).length+_+1)+1
  omega

end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
