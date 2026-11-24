import OAI.Computability.VPVNP.RankQueryStackPhysical

/-! # Valid tags and row addresses of each Schur descriptor -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Dispatch

/-- A read carries two valid matrix indices. The largest tag is the arity tag. -/
def ValidDescription (n Z : ℕ) (v : Fin 6 → ℕ) : Prop :=
  v 0 < 5 ∧ (v 0 = 2 ∨ v 0 = 3 → v 1 < n ∧ v 2 < n ∧ v 3 ≤ Z)

theorem describe_valid {n U Z : ℕ} (q : SchurKey n U Z) (k : ℕ) :
    ValidDescription n Z (describe.eval (inputs q k)) := by
  unfold ValidDescription
  cases q with
  | product d b u z =>
    by_cases hd : d.val = 0 <;> by_cases hb : b.count = 0 <;>
      by_cases hu : u.val = 0 <;> by_cases hz : z.val = 0 <;> simplify_dispatch
  | factor a u z =>
    by_cases hu : u.val = 0 <;> by_cases hu' : u.val = 1 <;> by_cases hz : z.val = 0 <;> simplify_dispatch
    omega
  | outer | inner | one => simplify_dispatch
  | scalar neg i j z => cases neg <;> simplify_dispatch <;> omega
  | power a q =>
    by_cases h0 : q.exponent.val = 0 <;> by_cases h1 : q.exponent.val = 1 <;>
      by_cases hij : q.row.val = q.col.val <;> by_cases hz : q.degree.val = 0 <;> simplify_dispatch <;> omega

end RankQuery.Stack.Dispatch

end VPVNP
end Computability
end OAI
