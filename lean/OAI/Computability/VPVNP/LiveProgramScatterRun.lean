import OAI.Computability.VPVNP.LiveLinkedEvaluatorFrame
import OAI.Computability.VPVNP.LiveProgramAdviceRun
import OAI.Computability.VPVNP.LiveEvaluatorRAMImage
import OAI.Computability.VPVNP.LiveEvaluatorReindexSweep

/-!
# Permuting the exponent bits in the linked evaluator

The scatter writes the exponent payload positions of the initial tape. The incoming
order table bounds each computed destination. Consequently the linked scatter can reload
the five operands of its frame at each call and transfer the stage tag on its final call.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.ScatterRun

open BurstRAM LiveEvaluatorReindex LiveEvaluatorInitialize LiveEvaluatorEncoding
open LiveStageLink PairStages CompressorRecords
open scoped Fin.CommRing

variable {w d t Z base M a : ℕ} {pub : Fin 5 → Word w}

/-- Addresses outside the interval containing all reversed, tagged exponent payloads. -/
def Outside (pub : Fin 5 → Word w) (j : ℕ) : Prop :=
  j < (pub 2).val ∨ (pub 2).val + 2*(pub 4).val ≤ j

private theorem active_target (hw : 2 ≤ w) (L : LiveEvaluatorReindex.Layout pub d t Z base M a)
    (perm : Fin d ≃ Fin t) (m : Memory w) (order : ∀ i : Fin d, (m ((pub 1).val+i.val)).val = (perm i).val)
    (q : Word w) (active : q < pub 4) :
    (pub 2).val ≤ (targetAddress pub q m).val ∧
      (targetAddress pub q m).val < (pub 2).val + 2*(pub 4).val := by
  have hdt : d = t := by simpa using Fintype.card_congr perm
  have hq : q.val < d*Z := by rw [hdt, ← L.total]; exact active
  have hz : 0 < Z := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hq
  have hrow : q.val / Z < d := (Nat.div_lt_iff_lt_mul hz).mpr hq
  have hm := mapAddress_val pub q (by rw [L.width]; have := L.mapFit; omega)
  rw [L.width] at hm
  let i : Fin d := ⟨q.val / Z, hrow⟩
  have hread : (m (mapAddress pub q).val).val = (perm i).val := by rw [hm]; exact order i
  have hf : (m (mapAddress pub q).val).val*(pub 3).val + q.val % (pub 3).val < (pub 4).val := by
    rw [hread, L.width, L.total]
    have hmul := Nat.mul_le_mul_right Z (perm i).isLt
    rw [Nat.succ_mul] at hmul
    have hrem := Nat.mod_lt q.val hz
    omega
  have hback : 2*((pub 4).val-1-((m (mapAddress pub q).val).val * (pub 3).val +
      q.val % (pub 3).val)) < 2*(pub 4).val := by omega
  have hfit := L.targetFit
  rw [← L.total] at hfit
  rw [targetAddress_val pub q m hw hf (by omega)]
  omega

private theorem report_protects (hw : 2 ≤ w) (L : LiveEvaluatorReindex.Layout pub d t Z base M a)
    (perm : Fin d ≃ Fin t) (m : Memory w) (order : ∀ i : Fin d, (m ((pub 1).val+i.val)).val = (perm i).val)
    (q : Word w) (bs : List Bool) (r : Report w)
    (run : let P := (scatterPhase.instantiate w pub).program
      execute P 27 (P.start q) m bs = some r) :
    ∀ m' j, Outside pub j → after m' r.events j = m' j := by
  dsimp only at run
  by_cases active : q < pub 4
  · rw [execute_phase_active pub q m bs 0 active] at run
    split at run
    · cases run
      intro m' j hj
      obtain ⟨lo, hi⟩ := active_target hw L perm m order q active
      unfold Outside at hj
      change writeMemory m' (targetAddress pub q m) (inputSymbol pub q m) j = m' j
      exact ite_eq_right (by omega)
    · contradiction
  · by_cases zero : q = 0
    · subst q
      have empty : pub 4 = 0 := le_antisymm (le_of_not_gt active) (Fin.zero_le _)
      rw [execute_phase_empty pub m bs 22 empty] at run
      split at run
      · cases run; intro m' j _; rfl
      · contradiction
    · rw [execute_phase_past pub q m bs 22 (le_of_not_gt active) zero] at run
      contradiction

/-- Replaying any one of the actual call reports on any memory only writes inside the
payload interval. Earlier scatter writes preserve the advised permutation. -/
theorem reports_outside (hw : 2 ≤ w) (L : LiveEvaluatorReindex.Layout pub d t Z base M a)
    (perm : Fin d ≃ Fin t) {m : Memory w} (order : ∀ i : Fin d, (m ((pub 1).val+i.val)).val = (perm i).val)
    {q : Option (Word w)} {bs : List (List Bool)} {rs : List (Report w)}
    (run : runSegment (scatterPhase.instantiate w pub).program 27 q m bs = some rs) :
    ∀ r ∈ rs, ∀ m' j, Outside pub j → after m' r.events j = m' j := by
  induction bs generalizing q m rs with
  | nil => have h : rs = [] := by simpa [runSegment] using run.symm
           simp [h]
  | cons b bs ih =>
    cases q with
    | none => simp [runSegment] at run
    | some q =>
      let P := (scatterPhase.instantiate w pub).program
      cases he : execute P 27 (P.start q) m b with
      | none => simp [runSegment, P] at he run; simp [he] at run
      | some r =>
        change runSegment P 27 (some q) m (b :: bs) = some rs at run
        rw [runSegment, he] at run
        obtain ⟨tail, ht, rfl⟩ := Option.map_eq_some_iff.mp run
        have head := report_protects hw L perm m order q b r he
        have keep (i : Fin d) : (after m r.events ((pub 1).val+i.val)).val = (perm i).val := by
          apply (congrArg Fin.val (head m _ _)).trans (order i)
          rcases L.mapDisjoint with hlo | hhi
          · exact Or.inl (by have := i.isLt; omega)
          · exact Or.inr (by rw [L.total]; omega)
        intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact head
        · exact ih keep ht s hs

/-- Base word address of the five scatter operands, seventeen words past the advice frame base. -/
def operandBase (G : PairStages.Group) : Word G.w :=
  Pieces.word G.g G.lit (.geometry (LiveProgram.Layout.adviceFrames G.constants + 17))

theorem component_eq (G : PairStages.Group) (st : Word G.w) (m : Memory G.w) (bits : List Bool) :
    let C := Pieces.component G.components Stage.scatter G.g G.lit
    let R := (Frame.machine scatterPhase (operandBase G)).program
    execute C 47 (C.start st) m bits = execute R 47 (R.start st) m bits := rfl

/-- Execute the complete framed scatter in the linked group. Its last report hands
control to the last-group router and the tape bank stores the evaluator's initial
configuration with the formal-coordinate exponents. -/
theorem returning_outside (G : PairStages.Group) (clock : 94 ≤ G.clock) (hw : 2 ≤ G.w)
    (pub : Fin 5 → Word G.w) (perm : Fin d ≃ Fin t) (dense : Fin d → Word Z)
    (formal : Fin t → Word Z) (order : ∀ i, formal (perm i) = dense i)
    (running : G.evaluator.extra ≠ 0) (hs : G.evaluator.extra+2 ≤ 2^G.w)
    (A : List Bool) (stateBase : Word G.w) (radius : ℕ)
    (L : LiveEvaluatorReindex.Layout pub d t Z stateBase.val radius A.length)
    (m : Memory G.w) (src : Sources pub perm dense m)
    (space : (A ++ EvaluatorProgramRawInput.runtime formal).length ≤ radius+1)
    (prepared : Stores hw hs stateBase.val m
      (LiveEvaluatorTail.initialCode radius (UniversalMachine.initial G.evaluator
        (A ++ EvaluatorProgramRawInput.runtime (fun _ : Fin t => (0 : Word Z))))))
    (tagged : G.tagged Stage.scatter m) (data : Frame.data (operandBase G) m = pub)
    (frameOutside : ∀ j : Fin 5, Outside pub ((operandBase G)+(j.val : Word G.w)).val)
    (tagOutside : G.addr.val < stateBase.val ∨ stateBase.val+fieldWords radius ≤ G.addr.val)
    (bankFit : stateBase.val + fieldWords radius ≤ 2^G.w) :
    let code := LiveEvaluatorTail.initialCode radius (UniversalMachine.initial G.evaluator
      (A ++ EvaluatorProgramRawInput.runtime formal))
    ∃ final, Advice.Returning G.P G.clock (max 1 (d*Z)) 10 m final ∧
      Stores hw hs stateBase.val final code ∧ LiveEvaluatorRAM.ConfigAt final stateBase code ∧
      G.tagged Stage.last final ∧ Advice.CostLimit G.P G.clock (max 1 (d*Z)) m (11*max 1 (d*Z)) ∧
      (∀ j, j ≠ G.addr.val → Outside pub j → final j = m j) := by
  dsimp only
  obtain ⟨rs, hr, halt, store, hlen, hprobes⟩ := sweep_native hw pub perm dense formal order
    G.evaluator running hs A stateBase.val radius L m src space prepared
  have tagSafe : Outside pub G.addr.val := by
    unfold Outside
    rw [L.target, L.total]
    simp only [List.length_append, EvaluatorProgramRawInput.runtime_length] at space
    unfold fieldWords at tagOutside
    omega
  have protect := reports_outside hw L perm src.order hr
  let final := writeMemory (after m (eventLog rs)) G.addr (tagWord G.w Stage.last)
  have ret : Advice.Returning G.P G.clock (max 1 (d*Z)) 10 m final := by
    apply Group.framedReturning (T := scatterPhase) (b := 3) clock tagged (dest := Stage.last)
      (by rfl) data (component_eq G) hr halt hlen hprobes
    intro r h u
    exact ⟨protect r h u _ tagSafe, funext (fun j => protect r h u _ (frameOutside j))⟩
  have kept : Stores hw hs stateBase.val final (LiveEvaluatorTail.initialCode radius
      (UniversalMachine.initial G.evaluator (A ++ EvaluatorProgramRawInput.runtime formal))) := by
    intro k
    have hk : stateBase.val + k.val ≠ G.addr.val := by have := k.isLt; omega
    change writeMemory _ _ _ _ = _
    rw [writeMemory, ite_eq_right hk]
    exact store k
  refine ⟨final, ret, kept, ?_, by simp [Group.tagged, final, writeMemory], ?_, ?_⟩
  · apply LiveEvaluatorRAM.configAt_of_words hw hs
    intro k
    have haddr : (stateBase + (k.val : Word G.w)).val = stateBase.val + k.val := by
      rw [Fin.val_add, Fin.val_natCast, Nat.add_mod_mod, Nat.mod_eq_of_lt (by have := k.isLt; omega)]
    rw [haddr]
    exact kept k
  · obtain ⟨logs, hrun, _, _, hn, hp⟩ := ret
    intro actual ha
    obtain rfl := Option.some.inj (ha.symm.trans hrun)
    rw [← hn]
    have bound (xs : List (Report G.w)) (hb : ∀ r ∈ xs, r.probes ≤ 10) :
        RAMBuckets.cost Report.probes xs ≤ 11*xs.length := by
      induction xs with
      | nil => simp [RAMBuckets.cost]
      | cons r xs ih =>
        have head := hb r (List.mem_cons_self ..)
        have tail := ih (fun a ha => hb a (List.mem_cons_of_mem _ ha))
        rw [RAMBuckets.cost, List.length_cons, Nat.mul_succ]
        omega
    exact bound actual (fun r h => (hp r h).1)

  · intro j htag hj
    change writeMemory _ _ _ j = _
    rw [writeMemory, ite_eq_right htag]
    have keep (xs : List (Report G.w))
        (hp : ∀ r ∈ xs, ∀ u : Memory G.w, after u r.events j = u j) (u : Memory G.w) :
        after u (eventLog xs) j = u j := by
      induction xs generalizing u with
      | nil => rfl
      | cons r xs ih =>
        change ((r.events ++ eventLog xs).foldl update u) j = _
        rw [List.foldl_append]
        exact (ih (fun q hq => hp q (List.mem_cons_of_mem _ hq)) _).trans (hp r (List.mem_cons_self ..) u)
    exact keep rs (fun r h u => protect r h u j hj) m

/-- Execution and configuration at the scatter handoff. -/
theorem returning (G : PairStages.Group) (clock : 94 ≤ G.clock) (hw : 2 ≤ G.w)
    (pub : Fin 5 → Word G.w) (perm : Fin d ≃ Fin t) (dense : Fin d → Word Z)
    (formal : Fin t → Word Z) (order : ∀ i, formal (perm i) = dense i)
    (running : G.evaluator.extra ≠ 0) (hs : G.evaluator.extra+2 ≤ 2^G.w)
    (A : List Bool) (stateBase : Word G.w) (radius : ℕ)
    (L : LiveEvaluatorReindex.Layout pub d t Z stateBase.val radius A.length)
    (m : Memory G.w) (src : Sources pub perm dense m)
    (space : (A ++ EvaluatorProgramRawInput.runtime formal).length ≤ radius+1)
    (prepared : Stores hw hs stateBase.val m
      (LiveEvaluatorTail.initialCode radius (UniversalMachine.initial G.evaluator
        (A ++ EvaluatorProgramRawInput.runtime (fun _ : Fin t => (0 : Word Z))))))
    (tagged : G.tagged Stage.scatter m) (data : Frame.data (operandBase G) m = pub)
    (frameOutside : ∀ j : Fin 5, Outside pub ((operandBase G)+(j.val : Word G.w)).val)
    (tagOutside : G.addr.val < stateBase.val ∨ stateBase.val+fieldWords radius ≤ G.addr.val)
    (bankFit : stateBase.val + fieldWords radius ≤ 2^G.w) :
    let code := LiveEvaluatorTail.initialCode radius (UniversalMachine.initial G.evaluator
      (A ++ EvaluatorProgramRawInput.runtime formal))
    ∃ final, Advice.Returning G.P G.clock (max 1 (d*Z)) 10 m final ∧
      Stores hw hs stateBase.val final code ∧ LiveEvaluatorRAM.ConfigAt final stateBase code ∧
      G.tagged Stage.last final ∧ Advice.CostLimit G.P G.clock (max 1 (d*Z)) m (11*max 1 (d*Z)) := by
  obtain ⟨final, ret, store, config, tag, cost, _⟩ :=
    returning_outside G clock hw pub perm dense formal order running hs A stateBase radius L m src
      space prepared tagged data frameOutside tagOutside bankFit
  exact ⟨final, ret, store, config, tag, cost⟩

end LiveProgram.ScatterRun

end VPVNP
end Computability
end OAI
