import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import OAI.Optimization.LinearProgramming.Compression.RequestScreenData
import OAI.Optimization.LinearProgramming.Compression.RequestBasis

/-! The native flag scan selects the same first lattice row as the mathematical request. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace RequestTable

open ScreenData
open scoped BigOperators

/-- The search for the first flag in materialized finite order returns the same index
as `List.find?`; the out-of-range sentinel is the actual declared length. -/
theorem firstFlag_finRange {d : ℕ} (p : Fin d → Bool) :
    ((List.finRange d).map (fun i => if p i then (1 : ℕ) else 0)).idxOf 1 =
      (((List.finRange d).find? p).map Fin.val).getD d := by
  have flag : ((fun a : ℕ => a == 1) ∘ fun i => if p i then (1 : ℕ) else 0) = p := by
    funext i; cases h : p i <;> simp [Function.comp_apply,h]
  have atIndex (i : Fin d) : (List.finRange d).idxOf? i=some i.val := by
    rw [List.idxOf?_eq_some_iff]
    refine ⟨by simp,by simp,?_⟩
    intro j hj he
    have h := congrArg Fin.val he
    simp at h
    omega
  rw [List.idxOf,List.findIdx_map,flag,List.findIdx_eq_getD_bind_find?_idxOf?,List.length_finRange]
  cases h : (List.finRange d).find? p with
  | none => rfl
  | some i => simp [atIndex]

/-- Lift any word-level admission test to the corresponding finite index predicate. -/
theorem screenRows_pack {d : ℕ} (rows : Fin d → List ℚ) (p : Fin d → Bool)
    (hp : ∀ i, rowPass d (rows i)=p i) :
    screenRows (List.ofFn rows)=(((List.finRange d).find? p).map Fin.val).getD d := by
  unfold screenRows
  rw [List.length_ofFn,List.ofFn_eq_map,List.map_map]
  have eq : ((fun r => if rowPass d r then (1:ℕ) else 0) ∘ rows) = (fun i => if p i then 1 else 0) := by
    funext i; simp [Function.comp_apply,hp]
  rw [eq]; exact firstFlag_finRange p

private theorem sqSum {d : ℕ} (f : Fin d → ℚ) : (List.ofFn f).sum=∑ i, f i := by
  induction d with
  | zero => simp
  | succ d ih => rw [List.ofFn_succ,Fin.sum_univ_succ,List.sum_cons,ih]

theorem rowSquare_graph {d : ℕ} (w : Fin d → ℚ) (z : Fin d → ℤ) :
    rowSquare (List.ofFn (requestGraphRat w z))=requestGraphSquare w z := by
  rw [rowSquare,List.map_ofFn,sqSum,Fin.sum_univ_castSucc]
  simp [requestGraphRat,requestGraphSquare,Function.comp_apply,pow_two]

theorem rowPass_graph {n : ℕ} (w : Fin (n+1) → ℚ) (z : Fin (n+1) → ℤ) :
    rowPass (n+1) (List.ofFn (requestGraphRat w z)) =
      decide (z (Fin.last n)≠0 ∧ requestGraphSquare w z ≤ (requestCutoff (n+1) : ℚ)^2) := by
  have pick {k : ℕ} (f : Fin k → ℚ) (i : Fin k) :
      ((List.ofFn f).drop i.val).headD 0 = f i := by simp [i.isLt]
  have h : ((List.ofFn (requestGraphRat w z)).drop ((n+1)-1)).headD 0 = (z (Fin.last n) : ℚ) := by
    change ((List.ofFn (requestGraphRat w z)).drop (Fin.last n).castSucc.val).headD 0 = _
    rw [pick]; simp [requestGraphRat]
  simp only [rowPass,h,rowSquare_graph,Rat.num_intCast]

/-- Compare the exact binary scan with the finite-option selector on arbitrary graph rows. -/
theorem screenRows_requestCandidate {n : ℕ} (w : Fin (n+1) → ℚ) (g : Fin (n+1) → Fin (n+1) → ℤ) :
    screenRows (List.ofFn fun i => List.ofFn (requestGraphRat w (g i)))=
      ((requestCandidate w g (Fin.last n)).map Fin.val).getD (n+1) :=
  screenRows_pack _ _ (fun i => rowPass_graph w (g i))

/-- For a native reduced basis, integral lattice-span membership reconstructs its
integer row coefficients before selecting a row. The equality covers search failure. -/
theorem screenRows_native {n : ℕ} (w : Fin (n+1) → ℚ) (A : Fin (n+1) → Fin (n+1+1) → ℚ)
    (h : ∀ i, A i ∈ Submodule.span ℤ (Set.range (requestInputRows w))) :
    screenRows (List.ofFn fun i => List.ofFn (A i))=
      ((requestCandidate w (fun i => requestDecodeRow (A i)) (Fin.last n)).map Fin.val).getD (n+1) := by
  have rep : A=(fun i => requestGraphRat w (requestDecodeRow (A i))) := funext (fun i => requestDecodeRow_valid (h i))
  exact (congrArg (fun R : Fin (n+1) → Fin (n+1+1) → ℚ => screenRows (List.ofFn fun i => List.ofFn (R i))) rep).trans
    (screenRows_requestCandidate w (fun i => requestDecodeRow (A i)))

end RequestTable
end Compression
end LinearProgramming
end Optimization
end OAI
