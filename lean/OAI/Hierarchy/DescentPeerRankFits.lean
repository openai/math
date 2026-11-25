import OAI.Hierarchy.DescentSortedRoster

namespace OAI
/-! # Memory bounds for the finite native neighbor rank expression -/
namespace Hierarchy.DescentResetSourceClassRAM
open DescentFallbackRankRAM DescentFallbackLeafScan DescentSortedRoster ProtocolRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w at_ : ℕ}

private theorem unless_fits {key use : Expr} (a : key.Fits w at_) (b : use.Fits w at_) (xs : List Expr)
    (all : ∀x∈xs,x.Fits w at_) : (unlessSeen key use xs).Fits w at_ := by
  induction xs with
  | nil=>exact b
  | cons x xs ih=>exact ⟨all _ (.head _),a,trivial,ih (fun y hy=>all y (.tail _ hy))⟩

private theorem sum_fits (xs : List Expr) (ok : ∀x∈xs,x.Fits w at_) : (foldSum xs).Fits w at_ := by
  induction xs with
  | nil=>trivial
  | cons x xs ih=>exact ⟨ok _ (.head _),ih (fun y hy=>ok y (.tail _ hy))⟩

theorem rank_fits {D : ℕ} (src : Fin D→Expr) (q : Expr) (fits : ∀i,(src i).Fits w at_)
    (query : q.Fits w at_) : (calculate src q).Fits w at_ := by
  apply sum_fits
  intro _ hx
  obtain ⟨j,_,rfl⟩:=List.mem_map.mp hx
  apply unless_fits (fits j) (show (Expr.branch .lt (src j) q (.lit 1) (.lit 0)).Fits w at_ from ⟨fits j,query,trivial,trivial⟩)
  intro _ cur
  obtain ⟨i,_,rfl⟩:=List.mem_map.mp cur
  exact fits i

end
end Hierarchy.DescentResetSourceClassRAM

end OAI
