import OAI.ThreeFlat.RAM.TraceOwnerFormula
import OAI.ThreeFlat.Diagonal.TraceSourceRectangle

namespace OAI
/-! # Validating the native reverse lookup of a rectangular hidden reservation -/

namespace ThreeFlat.RAM.TraceOwnerFormula

open Computability.VPVNP.BurstRAM PrivateRAM PhysicalPinsExpr DescriptorExpr
open Diagonal.TraceSourceOwner
open scoped Fin.CommRing

set_option maxRecDepth 12000 in
theorem reverse_natural (W : ℕ) (data : Param → ℕ) (mem : ℕ → ℕ) (s : Shape) (word v j : ℕ) :
    (formula .reverse).natural W data mem (vars s word v j) = unplace s v j := by
  simp only [formula,branch_natural,Formula.natural]
  by_cases a : j<2*s.cpu <;> by_cases b : j-2*s.cpu<s.layers*s.track <;>
    by_cases c : j-2*s.cpu-s.layers*s.track<s.edge <;>
    by_cases d : j-2*s.cpu-s.layers*s.track-s.edge<s.copy <;>
    simp [unplace,appendAt,vars,natOp,a,b,c,d]

/-- Verify a reverse candidate using the original count and its two forward coordinates.
The caller obtains both the candidate and this success flag without reserving a sentinel address. -/
def verify {W k : ℕ} : Term W k 6 :=
  .select .lt (.result 0) (.result 1)
    (.select .eq (.result 2) (.result 3)
      (.select .eq (.result 4) (.result 5) (.literal 1) (.literal 0)) (.literal 0)) (.literal 0)

theorem verify_binds {W k : ℕ} : (verify (W:=W) (k:=k)).binds=7 := by
  simp [verify,Term.select,Term.literal,Term.binds]

theorem verify_eval {W k : ℕ} (s : Shape) (v j : ℕ) (data : Fin k → Word W) (mem : Memory W)
    (bounds : ∀ i : Fin 6,
      (![unplace s v j,s.count,(locate s (unplace s v j)).1,v,(locate s (unplace s v j)).2,j] i) < 2^W) :
    verify.eval data mem (fun i => ((![unplace s v j,s.count,(locate s (unplace s v j)).1,v,
      (locate s (unplace s v j)).2,j] i : ℕ) : Word W)) =
      ((decode s v j).isSome.toNat : Word W) := by
  let h := unplace s v j
  let p := locate s h
  simp only [verify,Term.eval_select,Term.eval_literal,Term.eval]
  change (if Comparison.lt.test (h : Word W) (s.count : Word W) then
    (if Comparison.eq.test (p.1 : Word W) (v : Word W) then
      (if Comparison.eq.test (p.2 : Word W) (j : Word W) then 1 else 0) else 0) else 0) = _
  rw [test_cast .lt h s.count (bounds 0) (bounds 1),
    test_cast .eq p.1 v (bounds 2) (bounds 3),test_cast .eq p.2 j (bounds 4) (bounds 5)]
  by_cases ord : h<s.count <;> by_cases row : p.1=v <;> by_cases slot : p.2=j <;>
    simp [natTest,decode,Prod.ext_iff,h,p] at ord row slot ⊢ <;> simp_all
  all_goals by_cases cut : unplace s v j < s.count <;> simp [cut]

end ThreeFlat.RAM.TraceOwnerFormula

end OAI
