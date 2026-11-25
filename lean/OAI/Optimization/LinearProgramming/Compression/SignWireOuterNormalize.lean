import OAI.Optimization.LinearProgramming.RAM.Array
import OAI.Optimization.LinearProgramming.BitRAM.Ops
import OAI.Optimization.LinearProgramming.RAM.CallableBase

/-! Normalize the low even address registers of the bit controller before a nested
numeric call. Physical index `4*j` is an inner native cell and `4*j+2` is an inner
odd caller cell. Their encoded zero addresses are respectively zero and two. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire

open RAM

/-- Each pair contains one inner native and one inner caller address word. -/
def normalizeOuterPairs : ℕ → Block
  | 0 => .skip
  | n+1 => .seq (normalizeOuterPairs n)
      (.seq (.op (.addrConst (4*n) 0)) (.op (.addrConst (4*n+2) 2)))

def normalizedOuterPairs {K : Type*} (m : Memory K) : ℕ → Memory K
  | 0 => m
  | n+1 => ((normalizedOuterPairs m n).putIndex (4*n) 0).putIndex (4*n+2) 2

@[simp] theorem normalizedOuterPairs_data {K : Type*} (m : Memory K) (n : ℕ) :
    (normalizedOuterPairs m n).data=m.data := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem normalizedOuterPairs_index {K : Type*} (m : Memory K) (n i : ℕ) :
    (normalizedOuterPairs m n).index i =
      if i<4*n ∧ i%2=0 then i%4 else m.index i := by
  induction n with
  | zero => simp [normalizedOuterPairs]
  | succ n ih =>
    by_cases h0 : i=4*n
    · subst i
      rw [normalizedOuterPairs,Memory.putIndex_ne _ (by omega : 4*n≠4*n+2),Memory.putIndex_same]
      split_ifs <;> omega
    · by_cases h2 : i=4*n+2
      · subst i
        rw [normalizedOuterPairs,Memory.putIndex_same]
        split_ifs <;> omega
      · rw [normalizedOuterPairs,Memory.putIndex_ne _ h2,Memory.putIndex_ne _ h0,ih]
        split_ifs <;> omega

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem normalizeOuterPairs_eval (P : K → Prop) (m : Memory K) (n : ℕ) (hs : m.AllData P) :
    Block.Eval (Memory.AllData P) (normalizeOuterPairs n) m (2*n) (normalizedOuterPairs m n) := by
  induction n with
  | zero => exact .skip hs
  | succ n ih =>
    let a := normalizedOuterPairs m n
    let b := a.putIndex (4*n) 0
    have hA : a.AllData P := ih.safe_end
    have ea := Block.Eval.op_addrConst (safe := Memory.AllData P) a (4*n) 0 hA hA
    have eb := Block.Eval.op_addrConst (safe := Memory.AllData P) b (4*n+2) 2 hA hA
    simpa only [normalizeOuterPairs,normalizedOuterPairs,Nat.mul_succ] using ih.seq (ea.seq eb)

/-- One fixed block, requiring exactly thirty-two genuine scalar-RAM instructions. -/
def outerNormalize : Block := normalizeOuterPairs 16

def outerNormalized {F : Type*} (m : Memory F) : Memory F := normalizedOuterPairs m 16

theorem outerNormalize_spec (P : K → Prop) (m : Memory K) (hs : m.AllData P) :
    Block.Eval (Memory.AllData P) outerNormalize m 32 (outerNormalized m) :=
  normalizeOuterPairs_eval P m 16 hs

theorem outerNormalize_run (P : K → Prop) (m : Memory K) (hs : m.AllData P) :
    (Callable.Fragment.ofBlock outerNormalize).Run P m 32 (outerNormalized m) :=
  Callable.Fragment.Run.ofBlock (outerNormalize_spec P m hs)

section Frame
variable {F : Type*}

@[simp] theorem outerNormalized_data (m : Memory F) : (outerNormalized m).data=m.data :=
  normalizedOuterPairs_data m 16

theorem outerNormalized_index (m : Memory F) (i : ℕ) :
    (outerNormalized m).index i = if i<64 ∧ i%2=0 then i%4 else m.index i :=
  normalizedOuterPairs_index m 16 i

theorem outerNormalized_native (m : Memory F) (j : ℕ) (hj : j<16) :
    (outerNormalized m).index (4*j)=0 := by
  rw [outerNormalized_index]
  split_ifs <;> omega

theorem outerNormalized_caller (m : Memory F) (j : ℕ) (hj : j<16) :
    (outerNormalized m).index (4*j+2)=2 := by
  rw [outerNormalized_index]
  split_ifs <;> omega

theorem outerNormalized_odd (m : Memory F) (j : ℕ) :
    (outerNormalized m).index (2*j+1)=m.index (2*j+1) := by
  rw [outerNormalized_index]
  split_ifs <;> omega

theorem outerNormalized_high (m : Memory F) (i : ℕ) (h : 64≤ i) :
    (outerNormalized m).index i=m.index i := by
  simp [outerNormalized_index,Nat.not_lt.mpr h]

theorem outerNormalized_stableEven (m : Memory F) : BitRAM.StableEven m (outerNormalized m) :=
  fun i hi _ => outerNormalized_high m i hi

/-- Reassemble the exact nested memory from the scalar file, live odd controller
registers, cached high even indices, and canonical low nested zero addresses. -/
theorem outerNormalized_eq_of_layout (m target : Memory F) (data : m.data=target.data)
    (odd : ∀ j, m.index (2*j+1)=target.index (2*j+1)) (high : BitRAM.StableEven m target)
    (native : ∀ j<16, target.index (4*j)=0) (caller : ∀ j<16, target.index (4*j+2)=2) :
    outerNormalized m=target := by
  have eq (i : ℕ) : (outerNormalized m).index i=target.index i := by
    by_cases he : i%2=0
    · by_cases hi : 64≤ i
      · exact (outerNormalized_high m i hi).trans (high i hi he).symm
      · have hj : i/4<16 := by omega
        by_cases h : i%4=0
        · have ei : 4*(i/4)=i := by omega
          exact ei ▸ (outerNormalized_native m (i/4) hj).trans (native (i/4) hj).symm
        · have ei : 4*(i/4)+2=i := by omega
          exact ei ▸ (outerNormalized_caller m (i/4) hj).trans (caller (i/4) hj).symm
    · have ei : 2*(i/2)+1=i := by omega
      exact ei ▸ (outerNormalized_odd m (i/2)).trans (odd (i/2))
  have ext {a b : Memory F} (hd : a.data=b.data) (hi : a.index=b.index) : a=b := by
    cases a; cases b; exact congrArg₂ Memory.mk hd hi
  exact ext ((outerNormalized_data m).trans data) (funext eq)

end Frame
end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI
