import OAI.Computability.BorderVNP.CubeLabelISAEdge
import OAI.Computability.BorderVNP.CubeMeanRows

/-! # Identifying native cable contributions with the public mean numerators -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LabelTrial

open Cube.MeanChoice

/-- The width descriptor viewed from its source (direction zero) or its destination. -/
def orientedCable {C : Type*} (dir : ℕ) (c other : C) (width : ℕ) : Traffic C :=
  if dir = 0 then .cable c other width else .cable other c width

/-- The two integers computed by the native edge fragment are the scaled
conditional bin means before and after the trial. The old prefix fixes the
opposite endpoint exactly when its ordinal precedes the current cell. -/
theorem edgeContrib_rows {n z : ℕ} (s : Finset (Fin n)) (x : Fin n → Fin (z+1))
    (c other : Fin n) (v u j : Fin (z+1)) (dir width : ℕ) (hc : c ∉ s)
    (hne : other ≠ c) (hprefix : other ∈ s ↔ other < c) :
    let own := if dir = 0 then u.val else j.val
    let opp := if dir = 0 then j.val else u.val
    let b := edgeBefore (z+1) c.val other.val (x other).val opp width
    let row := orientedCable dir c other width
    b = rowNat s x (.inl (u,j)) row ∧
      edgeAfter (z+1) v.val own b =
        rowNat (insert c s) (Function.update x c v) (.inl (u,j)) row := by
  dsimp only
  by_cases hd : dir = 0 <;> by_cases ho : other < c
  all_goals
    have hm : other ∈ s ↔ other.val < c.val := hprefix
    simp only [hd,ite_true,ite_false,orientedCable,rowNat,edgeBefore,edgeAfter,factor,
      hc,Finset.mem_insert,Function.update_self,Function.update_of_ne hne,hne,
      hm,Fin.ext_iff,← Fin.lt_def,ho,false_or,or_false]
  all_goals split_ifs <;> simp_all

end RoutingISA.LabelTrial

end BorderVNP
end Computability
end OAI
