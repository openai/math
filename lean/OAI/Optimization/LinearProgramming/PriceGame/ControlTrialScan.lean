import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialCore
import OAI.Optimization.LinearProgramming.PriceGame.ControlFeedback
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialFinish
import OAI.Optimization.LinearProgramming.PriceGame.TrialQueryTraces

/-! Simulation of a whole pending feedback frame on each finite Oracle transcript. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Trial

open States States.Mass Moment TrialExecution

variable {N ne r l j : ℕ}

/-- The evaluator reads only earlier baselines when rebuilding the root query. -/
theorem pathFromRows_congr (N : ℕ) (a b : List (List ℚ)) (k : ℕ)
    (hab : ∀ j < k, a[j]? = b[j]?) : pathFromRows N a k = pathFromRows N b k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pathFromRows]
    rw [ih (fun j hj => hab j (Nat.lt_succ_of_lt hj)), hab k (Nat.lt_succ_self _)]

theorem pathFromRows_push (history : History N) (y : Prices N l) :
    pathFromRows N (packHistory (l+1) (history.push l y)) (l+1) =
      .extend (pathFromRows N (packHistory l history) l) y (vertexDecidableEq N l) := by
  rw [packHistory_push, pathFromRows]
  have hlen : (packHistory l history).length = l := by simp [packHistory]
  have heq := pathFromRows_congr N ((packHistory l history)++[packTable N l y]) (packHistory l history) l
    (fun j hj => List.getElem?_append_left (by omega))
  rw [heq, List.getElem?_append_right (by omega), hlen, Nat.sub_self]
  have hy : lookupTable N l (packTable N l y) = y := funext fun i => lookupTable_pack _ _ _ _
  change (pathFromRows N (packHistory l history) l).extend (lookupTable N l (packTable N l y)) _ = _
  rw [hy]

theorem history_push_zero_tail (history : History N) (y : Prices N l)
    (prev : ∀ t, l ≤ t → ∀ i, history t i = 0) :
    ∀ t, l+1 ≤ t → ∀ i, (history.push l y) t i = 0 := by
  intro t ht i
  simpa only [History.push, dite_eq_right (by omega : t ≠ l)] using prev t (by omega) i

/-- A packed replay interpreter with matching prefix observations requests exactly
the same ordered designated rows, even when the answers need not be consistent. -/
theorem Emits.scan {α C : Type} {p : Computation N α} {tr out} (e : Emits p tr out)
    (g : List Bool → C ⊕ PackedQuery) (code : α → C) (tape : List Bool)
    (same : ∀ bs, g (tape++bs) = (observe p bs).map (fun v => code v.1) packQuery) :
    Scan g tape tr (code out) := by
  induction e generalizing tape with
  | pure a => exact .done (by simpa only [List.append_nil, observe, Sum.map_inl] using same [])
  | @ask q k tr a b _ ih =>
    refine .ask b (by simpa only [List.append_nil, observe, Sum.map_inr] using same []) (ih (tape++[b]) ?_)
    intro bs
    simpa only [List.append_assoc, List.cons_append, List.nil_append, observe] using same (b::bs)

theorem finish_scan_probe (experts : Fin ne → Expert N) (w : Weights ne) (hist : History N)
    (path : States.Path (Fin N) (Vertex N l)) (hpath : path = pathFromRows N (packHistory l hist) l)
    (xs : Fin j → Call N ne r l) (hj : j < r)
    (a : MarketAnswer experts l hist (incomingLocal experts w xs))
    (ch : Certified (N:=N) (r:=r) (l:=l+1) (incomingDeep experts w xs)) {tr labels}
    (e : Emits (feedbackAll path a.prices ch.val.prices) tr labels) :
    Scan (completeSized feedbackPrefix N ne (List.ofFn (fun e => packExpert (experts e)))
      (codeInput l hist w) (List.ofFn (fun j => codeCall (xs j)))
      (codeProbe a (incomingDeep experts w xs)) (codeOutput ch.val)) [] tr
      (codeCall (probeReturn experts w hist xs hj a ch labels).val) := by
  rw [← probeReturn_pack]
  apply e.scan
  intro bs
  simp only [List.nil_append, completeSized, codeProbe, ite_true, codeInput, codeOutput]
  rw [← feedbackPrefix_refines]
  rw [← hpath]
  have hy : lookupTable N l (packTable N l a.prices) = a.prices :=
    funext fun i => lookupTable_pack _ _ _ _
  have hx : lookupTable N (l+1) (packTable N (l+1) ch.val.prices) = ch.val.prices :=
    funext fun i => lookupTable_pack _ _ _ _
  rw [hy,hx]
  cases observe (feedbackAll path a.prices ch.val.prices) bs <;> rfl

theorem finish_scan_final (experts : Fin ne → Expert N) (w : Weights ne) (hist : History N)
    (xs : Fin j → Call N ne r l) (hj : r ≤ j) (y : Prices N l)
    (ch : Certified (N:=N) (r:=r) (l:=l+1) (incomingDeep experts w xs)) :
    Scan (completeSized feedbackPrefix N ne (List.ofFn (fun e => packExpert (experts e)))
      (codeInput l hist w) (List.ofFn (fun j => codeCall (xs j)))
      (codeFinal y (incomingDeep experts w xs)) (codeOutput ch.val)) [] []
      (codeCall (finalReturn experts w xs hj y ch).val) := by
  apply Scan.done
  change Sum.inl _ = Sum.inl _
  rw [finalReturn_pack]

end Trial
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
