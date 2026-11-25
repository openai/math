import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialPackets

/-! Packing a successful local computation preserves its returned packet, including
prices, cached integer scores, and the order of all recorded public probes. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Trial

open States.Mass TrialExecution Moment

variable {N ne r l j : ℕ}

@[simp] theorem atD_packTable (N k : ℕ) (f : Vertex N k → ℚ) (i : Fin (N*2^k)) :
    atD (packTable N k f) i.val = f ((vertexEquivFin N k).symm i) := atD_ofFn _ _

@[simp] theorem atD_packBool (N k : ℕ) (f : Vertex N k → Bool) (i : Fin (N*2^k)) :
    atD (packTable N k f) i.val = f ((vertexEquivFin N k).symm i) := atD_ofFn _ _

theorem packHistory_push {N l : ℕ} (h : History N) (y : Vertex N l → ℚ) :
    packHistory (l+1) (h.push l y) = packHistory l h ++ [packTable N l y] := by
  rw [packHistory, List.ofFn_succ', List.concat_eq_append]
  unfold packHistory
  congr 1
  · apply congrArg List.ofFn
    funext j
    simp [History.push, Nat.ne_of_lt j.isLt]
  · simp [History.push]

theorem descend_probe {experts : Fin ne → Expert N} {history : History N} {L : Weights ne}
    (A : MarketAnswer experts l history L) (w dw : Weights ne) :
    descend (codeInput l history w) (codeProbe A dw) = codeInput (l+1) (history.push l A.prices) dw := by
  simp [descend, codeInput, codeProbe, packHistory_push]

theorem descend_final (history : History N) (y : Prices N l) (w dw : Weights ne) :
    descend (codeInput l history w) (codeFinal y dw) = codeInput (l+1) (history.push l y) dw := by
  simp [descend, codeInput, codeFinal, packHistory_push]

theorem mapped_pack (hist : History N) (w : Weights ne) (p : Prepared) (y : Prices N l)
    (hp : p.baseline = packTable N l y) (ch : Output N ne r (l+1)) :
    mapped N (codeInput l hist w) p (codeOutput ch) = packTable N l (States.parentPrices y ch.prices) := by
  have hx : lookupTable N (l+1) (packTable N (l+1) ch.prices) = ch.prices :=
    funext fun i => lookupTable_pack N (l+1) ch.prices i
  have hy : lookupTable N l (packTable N l y) = y := funext fun i => lookupTable_pack N l y i
  simp only [mapped, codeInput, codeOutput, hp, hx, hy]

/-- A probe's packed allocation sum is the original gain, including allocations on
repeated tuple goods being counted exactly as the market counted them. -/
theorem probe_gain_pack (experts : Fin ne → Expert N) (history : History N)
    (w : Weights ne) (A : MarketAnswer experts l history w) (dw : Weights ne)
    (z : Vertex N l → Bool) (e : Fin ne) :
    (∑ i : Fin (N*2^l),
      atD (atD (codeProbe A dw).allocation e.val) i.val *
        labelSign (atD (List.ofFn (fun k => packExpert (experts k))) e.val).positive *
        labelSign (atD (packTable N l z) i.val)) =
      gainQ (fun e i => A.fractions e (some i)) (sides experts) (fun i => labelSign (z i)) e := by
  simp only [codeProbe, atD_ofFn, atD_packTable, atD_packBool, packExpert]
  let f := fun i : Vertex N l => A.fractions e (some i) * labelSign (experts e).skeleton.positive * labelSign (z i)
  exact (vertexEquivFin N l).symm.sum_comp f

theorem probeReturn_pack (experts : Fin ne → Expert N) (w : Weights ne) (history : History N)
    (xs : Fin j → Call N ne r l) (hj : j < r) (A : MarketAnswer experts l history (incomingLocal experts w xs))
    (ch : Certified (N:=N) (r:=r) (l:=l+1) (incomingDeep experts w xs)) (z : Vertex N l → Bool) :
    finishPacketSized N ne (List.ofFn (fun e => packExpert (experts e))) (codeInput l history w)
      (codeProbe A (incomingDeep experts w xs)) (codeOutput ch.val) (packTable N l z) =
      codeCall (probeReturn experts w history xs hj A ch z).val := by
  apply Completed.mk.injEq .. |>.mpr
  refine ⟨rfl, mapped_pack _ _ _ _ rfl _, ?_, rfl⟩
  change (List.ofFn fun e : Fin ne => _) = (Vector.ofFn _).toList
  rw [Vector.toList_ofFn]
  apply congrArg List.ofFn
  funext e
  exact probe_gain_pack experts history _ A _ z e

theorem finalReturn_pack (experts : Fin ne → Expert N) (w : Weights ne) (history : History N)
    (xs : Fin j → Call N ne r l) (hj : r ≤ j) (y : Prices N l)
    (ch : Certified (N:=N) (r:=r) (l:=l+1) (incomingDeep experts w xs)) :
    finishPacketSized N ne (List.ofFn (fun e => packExpert (experts e))) (codeInput l history w)
      (codeFinal y (incomingDeep experts w xs)) (codeOutput ch.val) [] =
      codeCall (finalReturn experts w xs hj y ch).val := by
  apply Completed.mk.injEq .. |>.mpr
  refine ⟨rfl, mapped_pack _ _ _ _ rfl _, ?_, rfl⟩
  simp [codeFinal, finalReturn]

end Trial
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
