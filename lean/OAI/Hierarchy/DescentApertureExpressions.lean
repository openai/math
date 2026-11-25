import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # Native comparisons and counts across a short aperture -/
namespace Hierarchy.DescentFallbackRankRAM
open ThreeFlat.RAM DescriptorExpr Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w Δ : ℕ}
def unlessSeen (cur action : Expr) : List Expr→Expr
  | []=>action
  | old::rest=>.branch .eq old cur (.lit 0) (unlessSeen cur action rest)

theorem unlessSeen_eval (cur action : Expr) (xs : List Expr) (m : Memory w) (r : Word w) :
    (unlessSeen cur action xs).eval m r=if ∃x∈xs,x.eval m r=cur.eval m r then 0 else action.eval m r := by
  induction xs with
  | nil=>simp [unlessSeen]
  | cons x xs ih=>by_cases eqn : x.eval m r=cur.eval m r <;> simp [unlessSeen,Expr.eval,Comparison.test,eqn,ih]

def prior (j : Fin Δ) := (Finset.univ.filter (fun i : Fin Δ=>i<j)).toList

def foldSum (xs : List Expr) := xs.foldr (fun x acc=>Expr.op .add x acc) (.lit 0)

theorem foldSum_eval (xs : List Expr) (m : Memory w) (r : Word w) :
    (foldSum xs).eval m r=(xs.map (fun x=>x.eval m r)).sum := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>change x.eval m r+(foldSum xs).eval m r=_;simp [ih]

end
end Hierarchy.DescentFallbackRankRAM

end OAI
