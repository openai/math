import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Basic

namespace OAI
/-! # Fixed pitch for physical grouped host rows -/
namespace Hierarchy.DescentStageEdgeReceipt
open scoped Classical
noncomputable section
variable {V J : Type} [Fintype V] [Fintype J] [DecidableEq V] [DecidableEq J]

/-- Literal grouped host rows have a fixed multiplication pitch before the
first stage. It depends only on the purchased vertex address set. -/
def pitch (v : V↪ℕ) := (Finset.univ.sup v)+1

def groupRank (j : J↪ℕ) (v : V↪ℕ) : J×V↪ℕ where
  toFun u := j u.1*pitch v+v u.2
  inj' := by
    intro a b eqn
    have lim (x : V) : v x<pitch v := Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ x))
    have hp : 0<pitch v := Nat.zero_lt_succ _
    have top := congrArg (·/pitch v) eqn
    have bot := congrArg (·%pitch v) eqn
    change (j a.1*pitch v+v a.2)/_= _ at top
    change (j a.1*pitch v+v a.2)%_= _ at bot
    change (j a.1*pitch v+v a.2)/pitch v=(j b.1*pitch v+v b.2)/pitch v at top
    rw [Nat.mul_comm (j a.1),Nat.mul_comm (j b.1),Nat.mul_add_div hp,Nat.mul_add_div hp,
      Nat.div_eq_of_lt (lim a.2),Nat.div_eq_of_lt (lim b.2),Nat.add_zero,Nat.add_zero] at top
    simp [Nat.add_mod,Nat.mod_eq_of_lt (lim _)] at bot
    exact Prod.ext (j.injective top) bot

end
end Hierarchy.DescentStageEdgeReceipt

end OAI
