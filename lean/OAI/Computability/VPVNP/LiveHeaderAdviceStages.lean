import OAI.Computability.VPVNP.LiveHeaderIndexStages
import OAI.Computability.VPVNP.LiveHeaderAdvice
import OAI.Computability.VPVNP.LiveHeaderPrefix

/-! # The distributed advice scan in the native header table -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderProgram

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM ChainAssignments LiveHeaderSchedule LiveHeader
open scoped Fin.CommRing

variable {w d : ℕ}

/-- Public operands for scanning the distributed advice into its allocated header array,
starting at cursor zero. -/
def adviceWords (w : ℕ) (s : Sizes) (base : ℕ) : Fin 2 → Word w := ![0, Fin.ofNat _ (adviceBase s base)]

theorem advice_row (w : ℕ) (s : Sizes) (base : ℕ) :
    rowData w s base .advice ∘ includeFin (by decide : 2+1 ≤ 17) =
      LiveHeaderBounded.publicData (adviceWords w s base) (Fin.ofNat _ s.advice) := by
  funext j
  fin_cases j <;> rfl

theorem advice_step (hw : 4 ≤ w) (pub : Fin 2 → Word w) (zero : pub 0 = 0) (bound : ℕ)
    (fit : (pub 1).val+bound ≤ 2^w) (addr : Word w) (htag : addr.val < (pub 1).val)
    (i : ℕ) (hi : i < bound) (m : Memory w) (bits : List Bool) (rep : Report w) {fuel : ℕ}
    (h : execute (adviceTable.instantiate w pub).program fuel
      ((adviceTable.instantiate w pub).program.start (i : Word w)) m bits = some rep) :
    rep.result = some ((i+1 : ℕ) : Word w) ∧ after m rep.events addr.val = m addr.val := by
  obtain ⟨es, rs', ht, hresult, _, _, _⟩ := copyCell_trace hw 1 pub (i : Word w) (fun _ => 0) m
  have he : execute (adviceTable.instantiate w pub).program 13
      ((adviceTable.instantiate w pub).program.start (i : Word w)) m [] = some ⟨es, some ((i+1 : ℕ) : Word w)⟩ := by
    change execute (adviceTable.instantiate w pub).program (1+(copyCell 1).length) ⟨_,(i : Word w),fun _ => 0,fun _ => 0⟩ _ [] = _
    rw [execute_template, run_eq_trace, ht]
    simp [hresult]
  obtain ⟨_, rfl⟩ := execute_empty_forces_anyFuel he h
  refine ⟨rfl, ?_⟩
  change after m es addr.val = m addr.val
  rw [trace_after ht,zero,sub_zero]
  have hiv : (i : Word w).val = i := Fin.val_cast_of_lt (by omega)
  have hd : (pub 1 + (i : Word w)).val = (pub 1).val+i := by rw [Fin.val_add, hiv, Nat.mod_eq_of_lt (by omega)]
  simp [writeMemory,hd,show addr.val ≠ (pub 1).val+i by omega]

theorem advice_stage_native (s : Sizes) (base : ℕ) (hw : 4 ≤ w) (advice : CutSchedule.Bits s.advice)
    (cuts : AllCuts s.h s.delta) (g : Fin (2^(s.h+1))) (m : Memory w)
    (headers : SiteHeaders d hw advice cuts g m) (sites : s.advice ≤ 2^d)
    (scratch : 2^d ≤ base) (fit : limit s base ≤ 2^w) :
    let P := ((stageTemplate .advice).2.instantiate w (rowData w s base .advice)).program
    ∃ rs, runSegment P 16 (some 0) m (List.replicate (calls s .advice) []) = some rs ∧
      endState (some 0) rs = none ∧ rs.length = calls s .advice ∧
      (∀ rep ∈ rs, rep.probes ≤ probes .advice) ∧
      LiveStageLink.PreservesTagOnReturns (Fin.ofNat _ base) m rs ∧
      AdviceImage (d := d) hw advice cuts g (adviceBase s base) m (after m (eventLog rs)) := by
  let pub := adviceWords w s base
  let addr : Word w := Fin.ofNat _ base
  have hrow (bits : List (List Bool)) :
      runSegment ((stageTemplate .advice).2.instantiate w (rowData w s base .advice)).program 16 (some 0) m bits =
      runSegment (LiveHeaderBounded.machine adviceTable pub (s.advice : Word w)).program 16 (some 0) m bits := by
    change runSegment ((entry (LiveHeaderBounded.bounded adviceTable)).2.instantiate w (rowData w s base .advice)).program _ _ _ _ = _
    rw [run_entry,advice_row]
    rfl
  dsimp only
  rw [limit_eq] at fit
  have dst : adviceBase s base = base + 17 + 3*(s.h+2) := by
    dsimp [adviceBase,rightIndexBase,leftIndexBase,populationAddr,highAddr,indexBase]
    omega
  by_cases empty : s.advice = 0
  · let rep := LiveHeaderBounded.closedReport w
    have he := LiveHeaderBounded.execute_closed adviceTable pub (s.advice : Word w) 12 0
      (by simp [empty]) m []
    dsimp only at he
    refine ⟨[rep], ?_, rfl, by simp [calls, empty], ?_, LiveStageLink.PreservesTagOnReturns.singleton_accept _ _ _ rfl, ?_⟩
    · rw [hrow, show calls s .advice = 1 by simp [calls,empty], List.replicate_one,runSegment,he]
      rfl
    · intro r hr; obtain rfl := List.mem_singleton.mp hr; exact Nat.zero_le _
    · refine ⟨fun i => ?_, headers, fun _ _ => rfl⟩
      have := i.isLt; omega
  have hv : (pub 1).val = adviceBase s base := Nat.mod_eq_of_lt (by rw [dst]; omega)
  have ha : (s.advice : Word w).val = s.advice := Fin.val_cast_of_lt (by omega)
  have hfit : (pub 1).val+s.advice ≤ 2^w := by rw [hv,dst]; omega
  have hscratch : 2^d ≤ (pub 1).val := by rw [hv,dst]; omega
  have htag : addr.val < (pub 1).val := by
    change base % (2^w) < _
    rw [Nat.mod_eq_of_lt (by omega), hv, dst]; omega
  obtain ⟨raw, hr, _, hl, hp, image⟩ := physical_advice_scan_native headers pub rfl sites hscratch hfit
  have frame := runSegment_cursor_frame (adviceTable.instantiate w pub).program 13 s.advice addr
    (fun i hi mem rep he => advice_step hw pub rfl _ hfit addr htag i hi mem [] rep he)
    0 s.advice m raw (by omega) hr
  have complete := LiveHeaderBounded.runSegment_cursor_complete adviceTable pub (s.advice : Word w)
    (by decide : 0 < 13) 0 m (List.replicate s.advice []) raw (by rw [List.length_replicate,Nat.zero_add,ha]) hr
    (fun i hi mem bits rep he => (advice_step hw pub rfl _ hfit addr htag i (by rwa [ha] at hi) mem bits rep he).1)
  let outs := raw.map LiveHeaderBounded.activeReport ++ [LiveHeaderBounded.closedReport w]
  refine ⟨outs, ?_, ?_, ?_, ?_, guarded_frame frame, ?_⟩
  · rw [hrow, show calls s .advice = s.advice+1 from rfl, List.replicate_succ']
    exact complete
  · rw [show outs = _ ++ _ from rfl, endState_append]; rfl
  · simp [outs,hl,calls]
  · intro r hm
    rcases List.mem_append.mp hm with hh | hh
    · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hh; exact hp x hx
    · obtain rfl := List.mem_singleton.mp hh; exact Nat.zero_le _
  · have he : after m (eventLog outs) = after m (eventLog (raw.map LiveHeaderBounded.activeReport)) := by
      simp only [outs,eventLog,List.flatMap_append,after,List.foldl_append,List.flatMap_singleton]
      rfl
    rw [he,LiveHeaderBounded.after_activeReports,← hv]
    exact image

end LiveHeaderProgram

end VPVNP
end Computability
end OAI
