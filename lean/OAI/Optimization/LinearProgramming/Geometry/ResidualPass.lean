import OAI.Optimization.LinearProgramming.Geometry.UniformResidual

/-! Complete uniform pass from a computed projector table to its residual matrix. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open RAM Matrix
variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def residualPass : Block := uniformTableBlock GramCopy.residualCell

def residualPassTime (n : ℕ) : ℕ := uniformTableTime n n (n*(4*n+5)+4*n+11)

theorem residualPassTime_le (n : ℕ) : residualPassTime n ≤ polyBound 50 4 n := by
  unfold residualPassTime uniformTableTime uniformEntryTime polyBound
  ring_nf
  omega

/-- The only auxiliary address registers written during this pass. -/
def residualKeeps (p : ℕ) : Prop :=
  ¬ TableScratch p ∧ p ≠ 38 ∧ p ≠ 39 ∧ p ≠ 42

theorem residualKeeps_high (p : ℕ) (hp : 42 < p) : residualKeeps p := by
  unfold residualKeeps TableScratch
  omega

/-- All other scalars (above the small scratch block) and address registers survive.
The computed matrix costs a dimension-only polynomial number of RAM steps. -/
theorem residualPass_spec {n : ℕ} (P : K → Prop) (A : Matrix (Fin n) (Fin n) K)
    (m : Memory K) (src dst : ℕ) (hsrc : 8 ≤ src) (hsep : src+n*n ≤ dst)
    (hm : m.AllData P) (h0 : P 0) (h1 : P 1) (hval : ∀ i j, P ((1-A) i j))
    (h31 : m.index 31=n) (h33 : m.index 33=n) (h35 : m.index 35=dst)
    (h40 : m.index 40=src) (h41 : m.index 41=n)
    (hA : uniformRect n n src m = A) :
    ∃ t k, k ≤ residualPassTime n ∧ Block.Eval (Memory.AllData P) residualPass m k t ∧
      uniformRect n n dst t = 1-A ∧
      (∀ p, 8 ≤ p → (p < dst ∨ dst+n*n ≤ p) → t.data p = m.data p) ∧
      ∀ p, residualKeeps p → t.index p = m.index p := by
  let care := fun (p : ℕ) => 8 ≤ p
  have callback : TableCallbackSpec GramCopy.residualCell P care residualKeeps m n n dst
      (1-A) (n*(4*n+5)+4*n+11) := by
    apply GramCopy.residual_callback P care residualKeeps m n dst A h41
    · intro i j; rw [h40]; exact congrFun (congrFun hA i) j
    · intro i j; dsimp only; rw [h40]
      have hl := rectOffset_lt i j
      exact ⟨by dsimp [care]; omega, Or.inl (by omega)⟩
    · exact h0
    · exact h1
    · exact hval
    · decide
    · decide
    · exact fun _ h => h.2
    · simp [residualKeeps, TableScratch]
    · simp [residualKeeps, TableScratch]
  obtain ⟨t,k,hk,he,ht,hs,hi⟩ := uniformTableBlock_spec GramCopy.residualCell P care
      residualKeeps m n n dst (1-A) _ callback (fun _ h => h.1)
      (fun i j => by dsimp [care]; omega) h31 h33 h35 hm
  exact ⟨t,k,hk,he,ht,hs,fun p hp => hi p (.inr hp)⟩

end Geometry
end LinearProgramming
end Optimization
end OAI
