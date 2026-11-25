import OAI.Hierarchy.DescentSortedRoster

namespace OAI
/-! # Cost of ranking the actual sender IDs in one finite peer roster -/
namespace Hierarchy.DescentResetStemCompactOrder
open DescentFallbackRankRAM DescentFallbackLeafScan DescentSortedRoster ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM DescriptorExpr
open scoped Classical Fin.CommRing
noncomputable section

private theorem guarded_work {N : ℕ} (src : Fin N→Expr) (upper : ℕ) (bound : ∀i,(src i).work≤upper)
    (j : Fin N) (value : Expr) (xs : List (Fin N)) :
    (unlessSeen (src j) value (xs.map src)).work≤value.work+xs.length*(2*upper+2) := by
  induction xs with
  | nil=>simp [unlessSeen]
  | cons a xs ih=>
    change (src a).work+(src j).work+1+(unlessSeen (src j) value (xs.map src)).work+1≤_
    have:=bound a;have:=bound j
    rw [List.length_cons,Nat.succ_mul]
    omega

private theorem add_work (xs : List Expr) (u : ℕ) (upper : ∀e∈xs,e.work≤u) :
    (foldSum xs).work≤1+xs.length*(u+1) := by
  induction xs with
  | nil=>simp [foldSum,Expr.work]
  | cons a xs ih=>
    have one:=upper a (by simp)
    have rest:=ih (fun e he=>upper e (by simp [he]))
    change a.work+(foldSum xs).work+1≤_
    rw [List.length_cons,Nat.succ_mul];omega

/-- Each shared coarse-group or host table uses quadratically many scalar
comparisons in the number of its own reachable inputs. -/
theorem rank_work {N : ℕ} (src : Fin N→Expr) (query : Expr) (u : ℕ)
    (bound : ∀j,(src j).work≤u) (queryCost : query.work≤u) :
    (calculate src query).work ≤ 1+N*((2*u+3+N*(2*u+2))+1) := by
  have bit (j : Fin N) : (rankBit src query j).work≤2*u+3+N*(2*u+2) := by
    let test:=Expr.branch .lt (src j) query (.lit 1) (.lit 0)
    have testCost : test.work≤2*u+3:=by
      change (src j).work+query.work+1+1+1≤_
      have:=bound j;omega
    have size : (prior j).length≤N:=by
      simp only [prior,Finset.length_toList]
      simpa only [Finset.card_univ,Fintype.card_fin] using (Finset.card_le_card
        (Finset.filter_subset (fun i : Fin N=>i<j) Finset.univ))
    exact (guarded_work src u bound j test (prior j)).trans
      (Nat.add_le_add testCost (Nat.mul_le_mul_right _ size))
  unfold calculate
  have cost:=add_work ((Finset.univ : Finset (Fin N)).toList.map (rankBit src query))
    _ (fun e he=>by obtain ⟨j,_,rfl⟩:=List.mem_map.mp he;exact bit j)
  simpa only [List.length_map,Finset.length_toList,Finset.card_univ,Fintype.card_fin] using cost

end
end Hierarchy.DescentResetStemCompactOrder

end OAI
