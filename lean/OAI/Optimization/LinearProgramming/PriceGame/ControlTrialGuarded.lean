import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialCore

/-! Certificates attached to every visited phase of the explicit trial stack. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Trial

universe u

variable {I P R C Q : Type u}

inductive GuardedSteps (guard : State I P R C → Prop) (ops : Kernel I P R C Q) (calls : ℕ) :
    State I P R C → List (Q × Bool) → ℕ → State I P R C → Prop where
  | refl (s) (safe : guard s) : GuardedSteps guard ops calls s [] 0 s
  | silent {s t u tr n} (safe : guard s) (h : step ops calls s = .proceed t)
      (tail : GuardedSteps guard ops calls t tr n u) : GuardedSteps guard ops calls s tr (n+1) u
  | answer {s f t u tr n q} (b : Bool) (safe : guard s) (h : step ops calls s = .ask q f t)
      (tail : GuardedSteps guard ops calls (if b then t else f) tr n u) :
      GuardedSteps guard ops calls s ((q,b)::tr) (n+1) u

variable {p q : State I P R C → Prop} {ops alt : Kernel I P R C Q} {calls : ℕ}
    {s t u : State I P R C} {tr post : List (Q × Bool)} {n m : ℕ}

theorem GuardedSteps.forget (h : GuardedSteps p ops calls s tr n t) : Steps ops calls s tr n t := by
  induction h with
  | refl => exact .refl _
  | silent _ act _ ih => exact .silent act ih
  | answer b _ act _ ih => exact .answer b act ih

theorem GuardedSteps.stop (h : GuardedSteps p ops calls s tr n t) : p t := by
  induction h with
  | refl _ safe => exact safe
  | silent _ _ _ ih => exact ih
  | answer _ _ _ _ ih => exact ih

theorem GuardedSteps.weaken (h : GuardedSteps p ops calls s tr n t) (imp : ∀ x, p x → q x) :
    GuardedSteps q ops calls s tr n t := by
  induction h with
  | refl _ hs => exact .refl _ (imp _ hs)
  | silent hs act _ ih => exact .silent (imp _ hs) act ih
  | answer b hs act _ ih => exact .answer b (imp _ hs) act ih

theorem GuardedSteps.trans (h : GuardedSteps p ops calls s tr n t)
    (tail : GuardedSteps p ops calls t post m u) : GuardedSteps p ops calls s (tr++post) (n+m) u := by
  induction h with
  | refl => simpa
  | silent hs act _ ih => simpa only [Nat.succ_add] using GuardedSteps.silent hs act (ih tail)
  | answer b hs act _ ih => simpa only [Nat.succ_add,List.cons_append] using GuardedSteps.answer b hs act (ih tail)

/-- A polynomially clipped physical implementation agrees on every actual step,
including the result state, whenever it agrees on the certified data packets. -/
theorem GuardedSteps.changeKernel (h : GuardedSteps p ops calls s tr n t)
    (same : ∀ s, p s → step alt calls s = step ops calls s) :
    GuardedSteps p alt calls s tr n t := by
  induction h with
  | refl _ hs => exact .refl _ hs
  | silent hs act _ ih => exact .silent hs ((same _ hs).trans act) ih
  | answer b hs act _ ih => exact .answer b hs ((same _ hs).trans act) ih

end Trial
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
