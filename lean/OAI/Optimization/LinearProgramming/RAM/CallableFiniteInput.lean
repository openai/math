import OAI.Optimization.LinearProgramming.RAM.CallableLocal
import OAI.Optimization.LinearProgramming.RAM.CallableBase
import OAI.Optimization.LinearProgramming.RAM.CallableOddBase

/-! Finite list encodings for the two logical register banks at a native RAM entry. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable
namespace Odd

private def addressWord (native caller : List ℕ) (j : ℕ) : ℕ :=
  if j%2=0 then 2*(native[j/2]?.getD 0) else slot (caller[j/2]?.getD 0)

private def scalarWord {K : Type*} [Zero K] (native caller : List K) (j : ℕ) : K :=
  if j%2=0 then native[j/2]?.getD 0 else caller[j/2]?.getD 0

/-- The initialized address window is finite even though the ideal representation has
an infinite tail of encoded logical zeros. -/
def finiteDims (cap : ℕ) (native caller : List ℕ) : List ℕ :=
  List.ofFn fun j : Fin (cap+1) => addressWord native caller j

def finiteScalars {K : Type*} [Zero K] (native caller : List K) : List K :=
  List.ofFn fun j : Fin (2*max native.length caller.length) => scalarWord native caller j

private theorem finiteDims_get (cap : ℕ) (native caller : List ℕ) (j : ℕ) :
    (finiteDims cap native caller)[j]?.getD 0 = if j≤cap then addressWord native caller j else 0 := by
  simp only [finiteDims,List.getElem?_ofFn]
  split <;> rename_i h
  · simp [show j≤cap by omega]
  · simp [show ¬ j≤cap by omega]

private theorem finiteScalars_get {K : Type*} [Zero K] (native caller : List K) (j : ℕ) :
    (finiteScalars native caller)[j]?.getD 0 = scalarWord native caller j := by
  simp only [finiteScalars,List.getElem?_ofFn]
  split
  · rfl
  · rename_i h
    have hn := le_max_left native.length caller.length
    have hc := le_max_right native.length caller.length
    have n : native.length≤j/2 := by omega
    have c : caller.length≤j/2 := by omega
    simp [scalarWord,List.getElem?_eq_none n,List.getElem?_eq_none c]

/-- Every outside or even address is zero on entry to a fresh native bank. -/
theorem finiteDims_empty_native (cap : ℕ) (ds : List ℕ) (j : ℕ) :
    (finiteDims cap [] ds)[j]?.getD 0 = if j≤cap ∧ j%2=1 then slot (ds[j/2]?.getD 0) else 0 := by
  rw [finiteDims_get]
  by_cases he : j%2=0
  · simp [addressWord,he]
  · have ho : j%2=1 := by omega
    simp [addressWord,ho]

/-- Scalars are scattered onto the odd physical cells in their input order. -/
theorem finiteScalars_empty_native {K : Type*} [Zero K] (xs : List K) (j : ℕ) :
    (finiteScalars [] xs)[j]?.getD 0 = if j%2=1 then xs[j/2]?.getD 0 else 0 := by
  rw [finiteScalars_get]
  by_cases he : j%2=0
  · simp [scalarWord,he]
  · have ho : j%2=1 := by omega
    simp [scalarWord,ho]

theorem start_finite {K : Type*} [Zero K] (cap : ℕ) (dn dc : List ℕ) (xn xc : List K) :
    start (finiteDims cap dn dc) (finiteScalars xn xc) =
      trimIndex cap ((memory (start dn xn).memory (start dc xc).memory).atPC 0) := by
  apply congrArg₂ (fun d a => (⟨0,d,a,none⟩ : State K))
  · exact funext (finiteScalars_get xn xc)
  · exact funext (finiteDims_get cap dn dc)

private theorem entry_le_sum (l : List ℕ) (j : ℕ) : l[j]?.getD 0 ≤ l.sum := by
  cases h : l[j]? with
  | none => exact Nat.zero_le _
  | some n => exact List.le_sum_of_mem (List.mem_of_getElem? h)

theorem initial_index_bound {K : Type*} [Zero K] (dn dc : List ℕ) (xn xc : List K) (j : ℕ) :
    (memory (start dn xn).memory (start dc xc).memory).index j ≤ 2*max dn.sum dc.sum+1 := by
  change addressWord dn dc j ≤ _
  have hdn := (entry_le_sum dn (j/2)).trans (le_max_left dn.sum dc.sum)
  have hdc := (entry_le_sum dc (j/2)).trans (le_max_right dn.sum dc.sum)
  unfold addressWord slot
  split <;> omega

/-- A sufficient finite address prefix for the whole compiled computation. -/
def inputCap (p : Program) (dn dc : List ℕ) (budget : ℕ) : ℕ :=
  max (addressBudget p) (2*max dn.sum dc.sum+1) + budget

/-- Transfer any execution from the ideal two-bank start to the finite physical tapes. -/
theorem trace_finite {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (dn dc : List ℕ) (xn xc : List K) {p : Program} {k budget : ℕ} {tr : Fin (k+1) → State K}
    (h : Trace p ((memory (start dn xn).memory (start dc xc).memory).atPC 0) k tr) (hk : k≤budget) :
    Trace p (start (finiteDims (inputCap p dn dc budget) dn dc) (finiteScalars xn xc)) k
      (fun i => trimIndex (inputCap p dn dc budget) (tr i)) := by
  let b := max (addressBudget p) (2*max dn.sum dc.sum+1)
  have hp : addressBudget p≤b := le_max_left ..
  have hb : ∀ j, ((memory (start dn xn).memory (start dc xc).memory).atPC 0).index j≤b :=
    fun j => (initial_index_bound dn dc xn xc j).trans (le_max_right ..)
  rw [start_finite]
  exact trace_trimIndex hp hb h (Nat.add_le_add_left hk b)

/-- Run a complete fragment from finite lists on the ordinary native `RAM.start`.
All final and intermediate scalars are the exact ones proved in the logical run. -/
theorem run_halt_finite {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (dn dc : List ℕ) (xn xc : List K) {f : Fragment} {P : K → Prop} {bound : ℕ}
    {out : Memory K} (run : f.Run P (memory (start dn xn).memory (start dc xc).memory) bound out)
    (tag : ℕ) :
    ∃ k ≤ bound+1, ∃ tr : Fin (k+1) → State K,
      Trace (f.program tag) (start (finiteDims (inputCap (f.program tag) dn dc (bound+1)) dn dc)
        (finiteScalars xn xc)) k tr ∧
      (tr (Fin.last k)).output=some tag ∧ (tr (Fin.last k)).data=out.data ∧
      ∀ i j, P ((tr i).data j) := by
  obtain ⟨k,hk,tr,ht,ho,hm,hs⟩ := Fragment.run_halt run tag
  have real := trace_finite dn dc xn xc ht hk
  exact ⟨k,hk,_,real,ho,congrArg Memory.data hm,hs⟩

end Odd
end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
