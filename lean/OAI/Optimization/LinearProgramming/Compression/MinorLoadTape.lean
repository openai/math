import OAI.Optimization.LinearProgramming.Compression.MinorLoadInput

/-! Ordinary finite input tapes for a minor request. The scalar tape is shared for all
requests on D and E. Only the address tape changes when a different minor is requested. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace MinorLoad

open RAM

variable {K : Type*} [Zero K] {rD rE n : ℕ}

/-- Seven scratch entries followed by D and E, both in row-major order. -/
def pairScalarTape (D : Matrix (Fin rD) (Fin n) K) (E : Matrix (Fin rE) (Fin n) K) : List K :=
  List.ofFn (fun a : Fin (7+(rD+rE)*n) => stackedData D E a.val)

/-- The header and two finite lists of the requested row and column positions. -/
def pairAddressTape (D : Matrix (Fin rD) (Fin n) K) (E : Matrix (Fin rE) (Fin n) K)
    (u : PairMinorIndex rD rE n) : List ℕ :=
  let v := pairLayout D E u
  List.ofFn fun a : Fin (16+v.k+v.k) => indexData v a.val

@[simp] theorem length_pairScalarTape (D : Matrix (Fin rD) (Fin n) K) (E : Matrix (Fin rE) (Fin n) K) :
    (pairScalarTape D E).length = 7+(rD+rE)*n := by simp [pairScalarTape]

omit [Zero K] in
@[simp] theorem length_pairAddressTape (D : Matrix (Fin rD) (Fin n) K) (E : Matrix (Fin rE) (Fin n) K)
    (u : PairMinorIndex rD rE n) : (pairAddressTape D E u).length = 16+(pairLayout D E u).k+(pairLayout D E u).k := by
  simp [pairAddressTape]

private theorem data_outside (D : Matrix (Fin rD) (Fin n) K) (E : Matrix (Fin rE) (Fin n) K)
    (a : ℕ) (ha : 7+(rD+rE)*n ≤ a) : stackedData D E a = 0 := by
  rw [Nat.add_mul] at ha
  have h₁ : ¬ a<7 := by omega
  have h₂ : ¬ a-7<rD*n := by omega
  have h₃ : ¬ a-7-rD*n<rE*n := by omega
  rw [stackedData,ite_eq_right h₁,ite_eq_right h₂,matrixCell,dite_eq_right h₃]

omit [Zero K] in
private theorem index_outside (D : Matrix (Fin rD) (Fin n) K) (E : Matrix (Fin rE) (Fin n) K)
    (u : PairMinorIndex rD rE n) (a : ℕ) (ha : 16+(pairLayout D E u).k+(pairLayout D E u).k ≤ a) :
    indexData (pairLayout D E u) a = 0 := by
  let v := pairLayout D E u
  have hr : v.rowArray = 16 := by cases u <;> rfl
  have hc : v.colArray = 16+v.k := by cases u <;> rfl
  change 16+v.k+v.k ≤ a at ha
  change indexData v a = 0
  rw [indexData,ite_eq_right (show ¬a<6 by omega),dite_eq_right (by omega),dite_eq_right (by omega)]

private theorem tape_ofFn_getD {α : Type*} [Zero α] (f : ℕ → α) (bound : ℕ) (hz : ∀ i, bound ≤ i → f i = 0) :
    (fun a => ((List.ofFn fun i : Fin bound => f i.val)[a]?).getD 0) = f := by
  funext a
  rw [List.getElem?_ofFn]
  by_cases h : a < bound
  · simp [h]
  · simp [h, hz a (Nat.le_of_not_gt h)]

/-- The input view used by the code agrees at every address with `RAM.start` on finite lists. -/
theorem start_pairTapes (D : Matrix (Fin rD) (Fin n) K) (E : Matrix (Fin rE) (Fin n) K)
    (u : PairMinorIndex rD rE n) :
    start (pairAddressTape D E u) (pairScalarTape D E) = (pairMemory D E u).atPC 0 := by
  have hd := tape_ofFn_getD (stackedData D E) _ (data_outside D E)
  have hi := tape_ofFn_getD (indexData (pairLayout D E u)) _ (index_outside D E u)
  simp only [start, pairAddressTape, pairScalarTape, pairMemory, Memory.atPC, hd, hi]

end MinorLoad
end Compression
end LinearProgramming
end Optimization
end OAI
