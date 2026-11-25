import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialPackets
import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionMarketBounds

/-! # Correct market and weight preparation for one suspended trial call -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Trial
open States.Mass Moment TrialExecution

private theorem atD_table {N l : ℕ} (f : Vertex N l → ℚ) (i : Fin (N * 2^l)) :
    atD (packTable N l f) i.val = f ((vertexEquivFin N l).symm i) := by
  unfold packTable
  apply atD_ofFn

private theorem origin_vertex {N l : ℕ} (i : Vertex N l) :
    origin N l (vertexEquivFin N l i).val = (rootVertex N l i).val := by
  simp [origin, (vertexEquivFin N l i).isLt]

private theorem origin_index {N l : ℕ} (i : Fin (N * 2^l)) :
    origin N l i.val = (rootVertex N l ((vertexEquivFin N l).symm i)).val := by
  simp [origin, i.isLt]

private theorem history_read {N l d : ℕ} (history : History N)
    (zeroTail : ∀ j, l ≤ j → ∀ i, history j i = 0) (v : Vertex N d) :
    atD (atD (packHistory l history) d) (vertexEquivFin N d v).val = history d v := by
  by_cases hd : d < l
  · have hrow := atD_ofFn (fun j : Fin l => packTable N j (history j)) (⟨d, hd⟩ : Fin l)
    change atD (packHistory l history) d = packTable N d (history d) at hrow
    simpa [hrow] using atD_table (history d) (vertexEquivFin N d v)
  · simp [packHistory, atD, hd, zeroTail _ (Nat.le_of_not_gt hd)]
    rfl

theorem shiftRaw_pack {N l : ℕ} (expert : Expert N) (history : History N)
    (zeroTail : ∀ j, l ≤ j → ∀ i, history j i = 0) :
    shiftRaw N (packHistory l history) (packExpert expert) = expert.skeleton.shift expert.raw history := by
  cases hp : expert.skeleton.pivot with
  | none => simp [shiftRaw, packExpert, Skeleton.shift, hp]
  | some z =>
    obtain ⟨d, v⟩ := z
    simp only [shiftRaw, packExpert, hp, Option.map_some, Skeleton.shift, origin_vertex,
      atD_ofFn, history_read history zeroTail, States.signed, Skeleton.signed]

theorem acceptsRaw_pack {N l : ℕ} (expert : Expert N) (i : Fin (N * 2 ^ l)) :
    acceptsRaw l (packExpert expert) i.val = expert.accepts l ((vertexEquivFin N l).symm i) := by
  by_cases hl : l = expert.skeleton.level
  · subst l
    let v := vertexEquivFin N expert.skeleton.level
    have heq : (∃ j, (v (expert.skeleton.tuple j)).val = i.val) ↔
        (∃ j, expert.skeleton.tuple j = v.symm i) := by
      constructor
      · rintro ⟨j, hj⟩
        exact ⟨j, v.eq_symm_apply.mpr (Fin.ext hj)⟩
      · rintro ⟨j, hj⟩
        exact ⟨j, congrArg Fin.val (v.eq_symm_apply.mp hj)⟩
    have hc : (List.ofFn (fun j => (v (expert.skeleton.tuple j)).val)).contains i.val =
        decide (∃ j, expert.skeleton.tuple j = v.symm i) := by
      apply Bool.eq_iff_iff.mpr
      rw [List.contains_iff_mem, List.mem_ofFn, decide_eq_true_eq]
      exact heq
    calc
      _ = (List.ofFn (fun j => (v (expert.skeleton.tuple j)).val)).contains i.val := by
        simp only [acceptsRaw, packExpert, beq_self_eq_true, Bool.true_and, v]
      _ = decide (∃ j, expert.skeleton.tuple j = v.symm i) := hc
      _ = _ := by
        unfold Expert.accepts
        rw [dite_eq_left rfl]
  · simp [acceptsRaw, packExpert, Expert.accepts, hl, Ne.symm hl]

theorem bidRaw_pack {N l : ℕ} (expert : Expert N) (history : History N)
    (zeroTail : ∀ j, l ≤ j → ∀ i, history j i = 0) (i : Fin (N * 2 ^ l)) :
    bidRaw N l (packHistory l history) (packExpert expert) i.val =
      expert.intercept history ((vertexEquivFin N l).symm i) := by
  rw [bidRaw, shiftRaw_pack expert history zeroTail, origin_index i]
  simp only [packExpert, atD_ofFn, Expert.intercept]

private theorem gain_read {N ne r l j : ℕ} (xs : Fin j → Call N ne r l)
    (t : Fin j) (e : Fin ne) :
    atD (atD (List.ofFn (fun a => codeCall (xs a))) t.val).gains e.val = callGain (xs t) e := by
  rw [atD_ofFn]
  simp [codeCall, atD, callGain, e.isLt]

private theorem score_read {N ne r l j : ℕ} (xs : Fin j → Call N ne r l)
    (t : Fin j) (e : Fin ne) :
    atD (atD (List.ofFn (fun a => codeCall (xs a))) t.val).child.scores e.val = callScore (xs t) e := by
  rw [atD_ofFn]
  simp [codeCall, codeOutput, atD, callScore, e.isLt]

private theorem localRaw_eq {N ne r l j : ℕ} (xs : Fin j → Call N ne r l)
    (e : Fin ne) (initial : Fin ne → ℚ) :
    localWeightRaw (List.ofFn fun a => codeCall (xs a)) e.val (initial e) =
      localWeightQ etaQ initial (probeAt fun t => callGain (xs t)) j e := by
  simp only [localWeightRaw, localWeightQ, List.length_ofFn]
  congr 1
  apply Finset.prod_congr rfl
  intro t ht
  have ht' : t < j := Finset.mem_range.mp ht
  rw [gain_read xs (⟨t, ht'⟩ : Fin j) e]
  simp [probeAt, ht']

private theorem deepRaw_eq {N ne r l j : ℕ} (xs : Fin j → Call N ne r l)
    (e : Fin ne) (initial : Fin ne → ℚ) :
    deepWeightRaw (List.ofFn fun a => codeCall (xs a)) e.val (initial e) =
      deepWeightQ initial (probeAt fun t => callScore (xs t)) j e := by
  simp only [deepWeightRaw, deepWeightQ, List.length_ofFn]
  congr 2
  apply Finset.sum_congr rfl
  intro t ht
  have ht' : t < j := Finset.mem_range.mp ht
  rw [score_read xs (⟨t, ht'⟩ : Fin j) e]
  simp [probeAt, ht']

theorem deepWeightsSized_spec {N ne r l j : ℕ} (experts : Fin ne → Expert N)
    (w : Weights ne) (history : History N) (xs : Fin j → Call N ne r l) :
    deepWeightsSized ne (List.ofFn fun e => packExpert (experts e)) (codeInput l history w)
      (List.ofFn fun a => codeCall (xs a)) = List.ofFn (incomingDeep experts w xs) := by
  unfold deepWeightsSized
  apply congrArg List.ofFn
  funext e
  simpa [codeInput, packExpert, incomingDeep, deepPartQ, mask, Expert.isLocal]
    using deepRaw_eq xs e (deepPartQ (mask experts l) w)

private theorem localWeights_spec {N ne r l j : ℕ} (experts : Fin ne → Expert N)
    (w : Weights ne) (xs : Fin j → Call N ne r l) :
    (fun e : Fin ne => localWeightRaw (List.ofFn fun a => codeCall (xs a)) e.val
      (if (packExpert (experts e)).level = l then w e else 0)) = incomingLocal experts w xs := by
  funext e
  simpa [packExpert, incomingLocal, localPartQ, mask, Expert.isLocal]
    using localRaw_eq xs e (localPartQ (mask experts l) w)

/-- The concrete preparer performs exactly the same LCM-scaled transshipment as
the adaptive trial, including every mass sent through an eligible good. -/
theorem prepare_probe_spec {N ne r l j : ℕ} (experts : Fin ne → Expert N) (w : Weights ne)
    (hw : ∀ e, 0 ≤ w e) (history : History N)
    (zeroTail : ∀ d, l ≤ d → ∀ i, history d i = 0) (xs : Fin j → Call N ne r l) (hj : j < r) :
    preparePacketSized N r ne (List.ofFn fun e => packExpert (experts e)) (codeInput l history w)
      (List.ofFn fun a => codeCall (xs a)) =
    codeProbe (marketSolverAtCommonWeightUnit experts l history (incomingLocal experts w xs)
      (incomingLocal_nonneg experts w hw xs)) (incomingDeep experts w xs) := by
  let v := vertexEquivFin N l
  have hacc : (fun (e : Fin ne) (i : Fin (N*2^l)) => acceptsRaw l (packExpert (experts e)) i.val) =
      fun e i => (experts e).accepts l (v.symm i) :=
    funext fun e => funext fun i => acceptsRaw_pack (experts e) i
  have hbid : (fun (e : Fin ne) (i : Fin (N*2^l)) => bidRaw N l (packHistory l history)
      (packExpert (experts e)) i.val) = fun e i => (experts e).intercept history (v.symm i) :=
    funext fun e => funext fun i => bidRaw_pack (experts e) history zeroTail i
  unfold preparePacketSized
  rw [deepWeightsSized_spec]
  simp only [List.length_ofFn, hj, ite_true, codeInput, atD_ofFn]
  rw [localWeights_spec, hacc, hbid]
  simp [codeProbe, marketSolverAtCommonWeightUnit, marketSolverOfFin, packTable, packExpert, v]

/-- Once the probe phase ends the common coordinatewise median is used at each
remaining call, with the deeper weights from all earlier calls. -/
theorem prepare_final_spec {N ne r l j : ℕ} (experts : Fin ne → Expert N) (w : Weights ne)
    (history : History N) (xs : Fin j → Call N ne r l) (hj : r ≤ j) :
    preparePacketSized N r ne (List.ofFn fun e => packExpert (experts e)) (codeInput l history w)
      (List.ofFn fun a => codeCall (xs a)) =
    codeFinal (fun i => median fun t : Fin r => (xs ⟨t.val,lt_of_lt_of_le t.isLt hj⟩).data.baseline i)
      (incomingDeep experts w xs) := by
  unfold preparePacketSized
  rw [deepWeightsSized_spec]
  simp only [List.length_ofFn, Nat.not_lt.mpr hj, ite_false, codeFinal, codeInput]
  congr 1
  unfold medianRows packTable
  apply congrArg List.ofFn
  funext i
  apply congrArg median
  funext t
  have ht : t.val < j := lt_of_lt_of_le t.isLt hj
  simp [List.map_ofFn, codeCall, atD, ht, packTable, i.isLt]

end Trial
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
