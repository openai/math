import OAI.Computability.VPVNP.LiveEvaluatorRAMTranscript
import OAI.Computability.VPVNP.LiveEvaluatorRAMPrepareImage
import OAI.Computability.VPVNP.LiveEvaluatorCells
import OAI.Computability.VPVNP.RAMChain

/-!
# Accepting paths of a complete live evaluator group

The first call selects and publishes the action. The remaining calls each
check one cell and preserve that memory. Acceptance of the actual native
segment therefore fixes both the length of its branch stream and every entry
after the first. The memory on which the cell tests run is the memory obtained
by replaying the complete native report.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorRAM.Schedule

open BurstRAM
open PrimedInputRAM (Flow)
open LiveEvaluatorRAMPrepare (prepare)
open LiveEvaluatorGroup (AllCells)
open scoped Fin.CommRing

variable {w M : ℕ}

/-- The concrete interpreter halts on these branch lists and leaves the
specified external memory. -/
private def Finishes (p : UniversalMachine.Program) (pub : Pub → Word w) (s : Option (Word w))
    (m : Memory w) (bits : List (List Bool)) (mem : Memory w) : Prop :=
  ∃ rs, runSegment (nativeProgram p pub) (callFuel p) s m bits = some rs ∧
    endState s rs = none ∧ after m (eventLog rs) = mem

private theorem after_cons_report (m : Memory w) (r : Report w) (rs : List (Report w)) :
    after m (eventLog (r :: rs)) = after (after m r.events) (eventLog rs) := by
  simp [after, eventLog, List.foldl_append]

private theorem finishes_cons (p : UniversalMachine.Program) (pub : Pub → Word w) (st : Word w)
    (m : Memory w) (bs : List Bool) (tail : List (List Bool)) (mem : Memory w) :
    Finishes p pub (some st) m (bs :: tail) mem ↔
      ∃ mid, (∃ es out, Flow.Exec pub st (body (prepare p)) (fun _ => 0) m es out mid ∧
        choiceBits es = bs) ∧ Finishes p pub (nextState pub st) mid tail mem := by
  constructor
  · rintro ⟨rs, hr, hhalt, hmem⟩
    rw [runSegment] at hr
    cases he : execute (nativeProgram p pub) (callFuel p) ((nativeProgram p pub).start st) m bs with
    | none => simp [he] at hr
    | some r =>
      simp only [he, Option.map_eq_some_iff] at hr
      obtain ⟨rest, hrest, rfl⟩ := hr
      obtain ⟨es, out, mid, hbody, hbits, _, hstate, hmid⟩ := (nativeStep_iff ..).mp he
      rw [hstate, hmid] at hrest
      refine ⟨mid, ⟨es, out, hbody, hbits⟩, rest, hrest, ?_, ?_⟩
      · simpa only [endState, hstate] using hhalt
      · simpa only [after_cons_report, hmid] using hmem
  · rintro ⟨mid, hbody, rest, hrest, hhalt, hmem⟩
    obtain ⟨r, he, hmid⟩ := (nativeStep_exists_iff ..).mpr hbody
    obtain ⟨_, _, _, _, _, _, hstate, _⟩ := (nativeStep_iff ..).mp he
    refine ⟨r :: rest, ?_, ?_, ?_⟩
    · simp only [runSegment, he, hstate, hmid, hrest, Option.map_some]
    · simpa only [endState, hstate] using hhalt
    · simpa only [after_cons_report, hmid] using hmem

private def control (w total i : ℕ) : Option (Word w) :=
  if i = total then none else some (i : Word w)

private def cellAt (pub : Pub → Word w) (m : Memory w) (i : ℕ) : Prop :=
  cellTest (located (loaded pub (i : Word w) (fun _ => 0) m) m) m

private theorem cursor_ne_zero {i : ℕ} (hi : 0 < i) (hf : i < 2 ^ w) : (i : Word w) ≠ 0 := by
  intro hz
  have h := congrArg Fin.val hz
  rw [Fin.val_natCast, Nat.mod_eq_of_lt hf, Fin.val_zero] at h
  omega

/-- Starting in the cell scan, the only possible accepting stream consists
of one empty entry per remaining cell. This includes the empty suffix at halt. -/
private theorem scan_finishes (p : UniversalMachine.Program) (pub : Pub → Word w)
    (hfit : calls (pub 0).val ≤ 2 ^ w) (m mem : Memory w)
    (n i : ℕ) (hi : 0 < i) (hcount : i + n = calls (pub 0).val) (bits : List (List Bool)) :
    Finishes p pub (control w (calls (pub 0).val) i) m bits mem ↔
      bits = List.replicate n [] ∧ m = mem ∧
        ∀ j, i ≤ j → j < calls (pub 0).val → cellAt pub m j := by
  induction n generalizing i bits with
  | zero =>
    simp only [Nat.add_zero] at hcount
    subst i
    cases bits <;> simp [Finishes, control, runSegment, endState, eventLog, after]
    all_goals omega
  | succ n ih =>
    have hlt : i < calls (pub 0).val := by omega
    have hn : nextState pub (i : Word w) = control w (calls (pub 0).val) (i+1) :=
      nextState_at pub i hlt hfit
    have hz := cursor_ne_zero hi (hlt.trans_le hfit)
    rw [control, ite_eq_right hlt.ne]
    cases bits with
    | nil => simp [Finishes, runSegment, endState, List.replicate_succ]
    | cons b tail =>
      rw [finishes_cons, hn]
      simp_rw [noninitial_choices_iff p pub hz]
      constructor
      · rintro ⟨mid, ⟨htest, rfl, rfl⟩, hr⟩
        obtain ⟨rfl, hmem, htail⟩ := (ih (i+1) (by omega) (by omega) tail).mp hr
        refine ⟨List.replicate_succ.symm, hmem, ?_⟩
        intro j hj hbound
        rcases hj.eq_or_lt with rfl | hlt'
        · exact htest
        · exact htail j hlt' hbound
      · rw [List.replicate_succ, List.cons.injEq]
        rintro ⟨⟨rfl, htail⟩, hmem, hc⟩
        exact ⟨m, ⟨hc i le_rfl hlt, rfl, rfl⟩, (ih (i+1) (by omega) (by omega) tail).mpr
          ⟨htail, hmem, fun j hj => hc j (by omega)⟩⟩

private theorem allCells_iff_interval (p : UniversalMachine.Program) (pub : Pub → Word w)
    (m : Memory w) (hfit : calls M ≤ 2 ^ w) :
    AllCells M p pub m ↔ ∀ j, 1 ≤ j → j < calls M → cellAt pub m j := by
  have phase (s : Bool) (i : Fin (2*M+1)) :
      (∃ es regs mem, Flow.Exec pub (cellCursor s i : Word w) (body (prepare p))
        (fun _ => 0) m es regs mem) ↔ cellAt pub m (cellCursor s i) :=
    noninitial_call_iff p pub (cursor_ne_zero (by simp [cellCursor])
      ((cellCursor_lt_calls s i).trans_le hfit)) _ m
  constructor
  · intro hall j hj hlt
    by_cases hfirst : j ≤ 2*M+1
    · let i : Fin (2*M+1) := ⟨j-1, by omega⟩
      have h : cellCursor false i = j := by simp [cellCursor, i]; omega
      rw [← h]
      exact (phase false i).mp (hall false i)
    · let i : Fin (2*M+1) := ⟨j-(2*M+1)-1, by unfold calls at hlt; omega⟩
      have h : cellCursor true i = j := by simp [cellCursor, i]; omega
      rw [← h]
      exact (phase true i).mp (hall true i)
  · intro hall s i
    exact (phase s i).mpr (hall _ (by simp [cellCursor]) (cellCursor_lt_calls s i))

/-- Exact path and final-memory characterization for the actual group program.
The first choice list survives, including when two slots publish equal records. -/
theorem acceptedSegment_iff (p : UniversalMachine.Program) (pub : Pub → Word w)
    (m mem : Memory w) (bits : List (List Bool)) (hM : (pub 0).val = M)
    (hfit : calls M ≤ 2 ^ w) :
    (∃ rs, runSegment (nativeProgram p pub) (callFuel p) (some 0) m bits = some rs ∧
      endState (some 0) rs = none ∧ after m (eventLog rs) = mem) ↔
      ∃ bs, bits = bs :: List.replicate (2*(2*M+1)) [] ∧
        Prepared p pub m mem bs ∧ AllCells M p pub mem := by
  subst M
  change Finishes p pub (some 0) m bits mem ↔ _
  have hpos : 0 < calls (pub 0).val := by simp [calls]
  have hn : nextState pub 0 = control w (calls (pub 0).val) 1 :=
    nextState_at pub 0 hpos hfit
  cases bits with
  | nil => simp [Finishes, runSegment, endState]
  | cons b tail =>
    rw [finishes_cons, hn]
    simp_rw [scan_finishes p pub hfit _ mem (2*(2*(pub 0).val+1)) 1 (by decide) rfl tail]
    simp only [List.cons.injEq]
    constructor
    · rintro ⟨mid, hbody, htail, rfl, hall⟩
      exact ⟨b, ⟨rfl, htail⟩, hbody, (allCells_iff_interval p pub mid hfit).mpr hall⟩
    · rintro ⟨_, ⟨rfl, htail⟩, hbody, hall⟩
      exact ⟨mem, hbody, htail, rfl, (allCells_iff_interval p pub mem hfit).mp hall⟩

/-- A group path is determined by the first call's actual branch string.
All successful cell calls consume empty strings. -/
def actualPathEquiv (p : UniversalMachine.Program) (pub : Pub → Word w) (m : Memory w)
    (hM : (pub 0).val = M) (hfit : calls M ≤ 2 ^ w) :
    ActualPaths (nativeProgram p pub) (callFuel p) 0 m (fun _ => True) ≃
      {bs : List Bool // ∃ mem, Prepared p pub m mem bs ∧ AllCells M p pub mem} where
  toFun b := ⟨b.val.headD [], by
    obtain ⟨rs, hr, hhalt, _⟩ := b.property
    obtain ⟨bs, he, hp, hc⟩ := (acceptedSegment_iff p pub m _ b.val hM hfit).mp ⟨rs, hr, hhalt, rfl⟩
    exact he ▸ ⟨_, hp, hc⟩⟩
  invFun b := ⟨b.val :: List.replicate (2*(2*M+1)) [], by
    obtain ⟨mem, hp, hc⟩ := b.property
    obtain ⟨rs, hr, hhalt, _⟩ := (acceptedSegment_iff p pub m mem _ hM hfit).mpr ⟨b.val, rfl, hp, hc⟩
    exact ⟨rs, hr, hhalt, trivial⟩⟩
  left_inv b := by
    apply Subtype.ext
    obtain ⟨rs, hr, hhalt, _⟩ := b.property
    obtain ⟨bs, he, _, _⟩ := (acceptedSegment_iff p pub m _ b.val hM hfit).mp ⟨rs, hr, hhalt, rfl⟩
    change b.val.headD [] :: _ = b.val
    rw [he]
    rfl
  right_inv _ := rfl

end LiveEvaluatorRAM.Schedule

end VPVNP
end Computability
end OAI
