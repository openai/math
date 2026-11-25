import OAI.Optimization.LinearProgramming.PriceGame.ControlCollapseMachine
import OAI.Optimization.LinearProgramming.PriceGame.ControlFeedback

/-! The index-and-row stack code computes the same root designation and prices
as the semantic lifting proof on every actual path. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open States States.Mass

theorem childAddress (N l : ℕ) (i : Vertex N l) (b : Bool) :
    (vertexEquivFin N (l+1) (i,b)).val = b.toNat + 2 * (vertexEquivFin N l i).val := by
  cases b <;> rfl

theorem parentAddress (N l : ℕ) (q : Vertex N (l+1)) :
    (vertexEquivFin N (l+1) q).val / 2 = (vertexEquivFin N l q.1).val := by
  obtain ⟨i,b⟩ := q
  rw [childAddress]
  cases b with
  | false => simp
  | true => simp; omega

theorem drop_head_eq (xs : List ℚ) (j : ℕ) : (xs.drop j).headD 0 = xs[j]?.getD 0 := by
  induction xs generalizing j with
  | nil => simp
  | cons a xs ih =>
    cases j with
    | zero => rfl
    | succ j => exact ih j

private theorem sourceCell (N l : ℕ) (base xs : List ℚ) (q : Vertex N (l+1)) (j : Vertex N l) :
    liftCell ((vertexEquivFin N (l+1) q).val, base, xs) (vertexEquivFin N l j).val =
      override (lookupTable N l base) (lookupTable N (l+1) xs) q j := by
  have heq : (vertexEquivFin N l j).val = (vertexEquivFin N l q.1).val ↔ j = q.1 :=
    Fin.val_inj.trans (vertexEquivFin N l).injective.eq_iff
  have hf : (vertexEquivFin N (l+1) (j,false)).val = 2 * (vertexEquivFin N l j).val := by
    rw [childAddress]; simp
  have ht : (vertexEquivFin N (l+1) (j,true)).val = 2 * (vertexEquivFin N l j).val + 1 := by
    rw [childAddress]; simp [Nat.add_comm]
  simp only [liftCell, parentAddress, heq, override, parentPrices, lookupTable, drop_head_eq, hf, ht]
  rfl

/-- One compiled row update gives exactly the typed override, including the
designated copy and ties between equal prices. -/
theorem liftRow_refines (N l : ℕ) (base xs : List ℚ) (hlen : base.length = N*2^l)
    (q : Vertex N (l+1)) :
    liftRow ((vertexEquivFin N (l+1) q).val,base,xs) = upRow N l base xs q := by
  apply List.ext_getElem
  · calc
      _ = base.length := by simp [liftRow]
      _ = N*2^l := hlen
      _ = _ := (length_packTable _ _ _).symm
  · intro i hi hj
    have hw : i < N*2^l := by simpa [liftRow, hlen] using hi
    let j := (vertexEquivFin N l).symm ⟨i,hw⟩
    have ha : (vertexEquivFin N l j).val = i := congrArg Fin.val ((vertexEquivFin N l).apply_symm_apply _)
    simp only [liftRow, List.getElem_map, List.getElem_range, upRow, packTable, List.getElem_ofFn]
    simpa only [ha] using sourceCell N l base xs q j

theorem packHistory_succ {N : ℕ} (l : ℕ) (h : History N) :
    packHistory (l+1) h = packHistory l h ++ [packTable N l (h l)] := by
  unfold packHistory
  rw [List.ofFn_succ_last]
  rfl

private theorem historyLookup {N l j : ℕ} (h : History N) (hj : j < l) :
    (packHistory l h)[j]? = some (packTable N j (h j)) := by
  have H : j < (packHistory l h).length := by simpa only [packHistory,List.length_ofFn] using hj
  rw [List.getElem?_eq_getElem H]
  simp only [packHistory,List.getElem_ofFn]

private theorem pathRows_agree (N l : ℕ) (left right : List (List ℚ))
    (eqs : ∀ j < l, left[j]? = right[j]?) : pathFromRows N left l = pathFromRows N right l := by
  induction l with
  | zero => rfl
  | succ l ih =>
    simp only [pathFromRows]
    rw [ih (fun j hj => eqs j (by omega)), eqs l (by omega)]

/-- The full compiled ancestor scan applied to the source's chronological history
returns exactly the root query that must be issued to the external oracle. -/
theorem collapse_refines (N l : ℕ) (h : History N) (x : Vertex N l → ℚ) (q : Vertex N l) :
    let payload := collapse (packHistory l h, ((vertexEquivFin N l q).val, packTable N l x))
    PackedQuery.mk payload.2 payload.1 =
      packQuery (designatedQuery (pathFromRows N (packHistory l h) l) x q) := by
  induction l with
  | zero =>
    change PackedQuery.mk (packTable N 0 x) _ = PackedQuery.mk (List.ofFn x) _
    exact congrArg (fun row => PackedQuery.mk row q.val) (packTable_zero N x)
  | succ l ih =>
    let y := lookupTable N l (packTable N l (h l))
    have hy : y = h l := funext fun i => lookupTable_pack N l (h l) i
    let x' := override (h l) x q
    have hu : liftRow ((vertexEquivFin N (l+1) q).val,packTable N l (h l),packTable N (l+1) x) =
        packTable N l x' := by
      rw [liftRow_refines _ _ _ _ (length_packTable ..)]
      unfold upRow
      have hx : lookupTable N (l+1) (packTable N (l+1) x) = x := funext fun i => lookupTable_pack _ _ _ _
      have hy' : lookupTable N l (packTable N l (h l)) = h l := hy
      erw [hx,hy']
    have hp : pathFromRows N (packHistory (l+1) h) l = pathFromRows N (packHistory l h) l := by
      apply pathRows_agree
      intro j hj
      rw [historyLookup h (Nat.lt_succ_of_lt hj),historyLookup h hj]
    have hrow : (packHistory (l+1) h)[l]?.getD [] = packTable N l (h l) := by
      rw [historyLookup h (Nat.lt_succ_self l)]
      rfl
    simp only [packHistory_succ, collapse, List.reverse_append, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.cons_append, List.foldl_cons, ascend, parentAddress, hu]
    have result := ih x' q.1
    change PackedQuery.mk _ _ = _ at result
    apply result.trans
    change packQuery (designatedQuery (pathFromRows N (packHistory l h) l) x' q.1) =
      packQuery (designatedQuery (pathFromRows N (packHistory l h ++ [packTable N l (h l)]) l)
        (override (lookupTable N l ((packHistory l h ++ [packTable N l (h l)])[l]?.getD [])) x q) q.1)
    rw [← packHistory_succ, hp, hrow]
    rw [show lookupTable N l (packTable N l (h l)) = h l from hy]

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
