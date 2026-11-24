import OAI.Computability.VPVNP.RankCoordinateRegisters
import OAI.Computability.VPVNP.SliceArithmeticCallCopies
import OAI.Computability.VPVNP.SliceArithmeticCallClear
import OAI.Computability.VPVNP.SpaceRunMonotone

/-!
# Reusing the rank workspace across prefix queries

Each call copies its fixed template into private work stacks. Designated
ports receive the live prefix-length word from register four. On return the
selected result word replaces register three, and every work port is cleared
before the next query.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Coordinate.PrefixWorkspace

open RAMTape BurstRAM Dispatch UniversalCountStack SliceArithmetic

/-- Auxiliary ports of a prefix-rank call, with separate template and working stacks for each
callee port and one scratch stack for copies. -/
inductive Aux (H : Type) where
  | template (h : H) | work (h : H) | scratch
  deriving DecidableEq, Fintype

/-- The five prefix-search word registers together with the private workspace used for calls to
the rank machine. -/
abbrev Port (H : Type) := PrefixWords.Port (Aux H)

variable {H : Type}

/-- Initialize the template and working stacks from two banks, leaving the copy scratch empty. -/
def auxBank (template work : Stacks H) : Stacks (Aux H)
  | .template h => template h
  | .work h => work h
  | .scratch => []

/-- The complete stack bank for a prefix-rank call, with the supplied template, working stacks,
and five word registers. -/
def bank {w : ℕ} (template work : Stacks H) (rs : Regs 5 w) :=
  PrefixWords.bank (auxBank template work) rs

/-- The caller stack holding the working copy of a particular port of the rank machine. -/
def workPort (h : H) : Port H := .inr (.work h)

private def scratch : Port H := .inr .scratch

private def reg (i : Fin 5) : Port H := .inl (.reg i)

private def source (dynamic : H → Bool) (h : H) : Port H :=
  if dynamic h then reg 4 else .inr (.template h)

/-- Contents of a working stack before a rank call. Dynamic ports receive the prefix word in
register four, and the others receive their template stacks. -/
def prepared {w : ℕ} (dynamic : H → Bool) (template : Stacks H) (rs : Regs 5 w) (h : H) :=
  if dynamic h then wordBits (rs 4) else template h

variable [Fintype H]

private noncomputable def plan (dynamic : H → Bool) : List (Port H × Port H) :=
  Finset.univ.toList.map (fun h => (source dynamic h, workPort h))

private noncomputable def workPorts : List (Port H) := Finset.univ.toList.map workPort

/-- Populate every working port from the prefix word or its template stack according to the
dynamic-port predicate. -/
noncomputable def copyIn (dynamic : H → Bool) : FiniteRoutine (Port H) := CallCopies.copyPlan scratch (plan dynamic)

omit [Fintype H] in
private theorem workPort_injective : Function.Injective (workPort (H := H)) :=
  fun _ _ he => Aux.work.inj (Sum.inr.inj he)

omit [Fintype H] in
private theorem source_ne_work (dynamic : H → Bool) (i j : H) : source dynamic i ≠ workPort j := by
  unfold source; split <;> intro h <;> cases h

private theorem plan_dest (dynamic : H → Bool) : (plan dynamic).map Prod.snd = workPorts := by
  simp only [plan, workPorts, List.map_map, Function.comp_def]

private theorem plan_src (dynamic : H → Bool) : (plan dynamic).map Prod.fst = Finset.univ.toList.map (source dynamic) := by
  simp only [plan, List.map_map, Function.comp_def]

private theorem valid (dynamic : H → Bool) : CallCopies.Valid scratch (plan dynamic) := by
  unfold CallCopies.Valid
  rw [plan_dest, plan_src]
  refine ⟨(Finset.nodup_toList _).map workPort_injective, ?_, ?_, ?_⟩
  · intro p hp hd
    obtain ⟨h, _, rfl⟩ := List.mem_map.mp hp
    obtain ⟨j, _, hj⟩ := List.mem_map.mp hd
    exact source_ne_work dynamic h j hj.symm
  · intro hp
    obtain ⟨h, _, he⟩ := List.mem_map.mp hp
    unfold source at he
    split at he <;> cases he
  · intro hp
    obtain ⟨h, _, he⟩ := List.mem_map.mp hp
    cases he

/-- Step bound for copying one input stack of length at most M into each of the rank workspace
ports. -/
def copyClock (H : Type) [Fintype H] (M : ℕ) := Fintype.card H * (5*M+2)+1

/-- Step bound for clearing register three, copying the w-bit rank into it, and erasing all
working stacks. -/
def returnClock (H : Type) [Fintype H] (w M : ℕ) := (w+1)+(5*w+2)+(Fintype.card H*(M+1)+1)

variable [DecidableEq H] {w : ℕ}

omit [Fintype H] [DecidableEq H] in
theorem bank_bound (template work : Stacks H) (rs : Regs 5 w) (M : ℕ) (hw : w ≤ M)
    (ht : ∀ h, (template h).length ≤ M) (hs : ∀ h, (work h).length ≤ M) (p : Port H) :
    (bank template work rs p).length ≤ M := by
  cases p with
  | inl k => exact (RegisterTable.bank_length_le Fin.elim0 0 rs k).trans hw
  | inr k => cases k with
    | template h => exact ht h
    | work h => exact hs h
    | scratch => exact Nat.zero_le _

private theorem plan_output (dynamic : H → Bool) (template : Stacks H) (rs : Regs 5 w) :
    CallCopies.copied (plan dynamic) (bank template (fun _ => []) rs) =
      bank template (prepared dynamic template rs) rs := by
  let s := bank template (fun _ => []) rs
  have unchanged (k : Port H) (hk : ∀ h, workPort h ≠ k) : CallCopies.copied (plan dynamic) s k = s k := by
    apply CallCopies.copied_outside
    rw [plan_dest]
    intro h
    obtain ⟨a, _, ha⟩ := List.mem_map.mp h
    exact hk a ha
  funext k
  cases k with
  | inl k => exact unchanged _ (by intro h he; cases he)
  | inr k => cases k with
    | template k | scratch => exact unchanged _ (by intro h he; cases he)
    | work h =>
      have hp : (source dynamic h, workPort h) ∈ plan dynamic := List.mem_map.mpr ⟨h, by simp, rfl⟩
      have hh := CallCopies.copied_at (plan dynamic) s (valid dynamic).1 hp
      change CallCopies.copied (plan dynamic) s (workPort h) = prepared dynamic template rs h
      rw [hh]
      unfold source prepared
      split <;> rfl

/-- Copy the live prefix length and template into all callee ports without
consuming either source. Every caller register survives the preparation. -/
theorem copyIn_bounded (dynamic : H → Bool) (template : Stacks H) (rs : Regs 5 w) (M : ℕ)
    (hw : w ≤ M) (ht : ∀ h, (template h).length ≤ M) :
    ∃ t ≤ copyClock H M, (copyIn dynamic).BoundedRun (M+copyClock H M) t
      (bank template (fun _ => []) rs) (bank template (prepared dynamic template rs) rs) := by
  let s := bank template (fun _ => []) rs
  have hb := bank_bound template (fun _ => []) rs M hw ht (fun _ => Nat.zero_le M)
  obtain ⟨t, hclock, hr⟩ := CallCopies.copyPlan_runs scratch (plan dynamic) s M (valid dynamic) rfl
    (by intro p hp; obtain ⟨a, _, rfl⟩ := List.mem_map.mp hp; rfl) (fun p _ => hb p.1)
  have hk : t ≤ copyClock H M := by simpa [plan, copyClock] using hclock
  refine ⟨t, hk, ?_⟩
  change (copyIn dynamic).Runs t s (CallCopies.copied (plan dynamic) s) at hr
  rw [show CallCopies.copied (plan dynamic) s = _ from plan_output dynamic template rs] at hr
  exact spaceRun_of_steps hr (fun k => Nat.add_le_add (hb k) hk)

/-- Any bounded callee run changes only its private work stacks. -/
def callRank (r : FiniteRoutine H) : FiniteRoutine (Port H) := r.onPorts workPort

omit [Fintype H] in
theorem callRank_bounded (r : FiniteRoutine H) {M t : ℕ} {s out : Stacks H} (template : Stacks H)
    (rs : Regs 5 w) (hw : w ≤ M) (ht : ∀ h, (template h).length ≤ M)
    (hr : r.BoundedRun M t s out) :
    (callRank r).BoundedRun M t (bank template s rs) (bank template out rs) := by
  let base := bank template s rs
  have outside (p : Port H) (hp : ∀ h, workPort h ≠ p) : (base p).length ≤ M := by
    cases p with
    | inl k => exact (RegisterTable.bank_length_le Fin.elim0 0 rs k).trans hw
    | inr k => cases k with
      | template h => exact ht h
      | work h => exact (hp h rfl).elim
      | scratch => exact Nat.zero_le _
  have run := FiniteRoutine.BoundedRun.onPorts (a := r) workPort_injective base hr outside
  have he : installStacks workPort base out = bank template out rs := by
    apply installStacks_frame (small := out) (target := bank template out rs) workPort_injective (fun _ => rfl)
    intro p hp
    cases p with
    | inr k => cases k with
      | work h => exact (hp h rfl).elim
      | _ => rfl
    | inl k => rfl
  rwa [installStacks_eq workPort_injective base s (fun _ => rfl), he] at run

/-- Replace register three by the word from the callee’s result port and clear the working
stacks for the next prefix query. -/
noncomputable def returnRank (result : H) : FiniteRoutine (Port H) :=
  ((CallClear.clear (reg 3)).followedBy (SuccessorFields.prependCopy (workPort result) (reg 3) scratch)).followedBy
    (CallClear.cleanup workPorts)

omit [Fintype H] in
private theorem update_reg (template work : Stacks H) (rs : Regs 5 w) (rank : Word w) :
    Function.update (bank template work rs) (reg 3) (wordBits rank) =
      bank template work (Function.update rs 3 rank) := by
  funext k
  cases k with
  | inr k => rfl
  | inl k =>
    have he := congrFun (ISA.bank_updateReg Fin.elim0 (0 : Word w) rs [] 3 rank) k
    cases k with
    | reg i => by_cases hi : i = 3 <;> simp [bank, PrefixWords.bank, reg, ISA.bank, hi]
    | _ => exact he

private theorem cleared (template work : Stacks H) (rs : Regs 5 w) :
    CallClear.erased workPorts (bank template work rs) = bank template (fun _ => []) rs := by
  funext k
  cases k with
  | inl k => simp [CallClear.erased, workPorts, workPort]; rfl
  | inr k => cases k with
    | work h => simp [CallClear.erased, workPorts, workPort, bank, PrefixWords.bank, auxBank]
    | template h | scratch => simp [CallClear.erased, workPorts, workPort, bank, PrefixWords.bank, auxBank]

/-- Return a complete rank word, reclaim every private port, and restore all
prefix-machine registers other than the result register. -/
theorem returnRank_bounded (result : H) (template work : Stacks H) (rs : Regs 5 w) (rank : Word w)
    (M : ℕ) (hw : w ≤ M) (ht : ∀ h, (template h).length ≤ M) (hs : ∀ h, (work h).length ≤ M)
    (hr : work result = wordBits rank) :
    ∃ t ≤ returnClock H w M, (returnRank result).BoundedRun (M+returnClock H w M) t
      (bank template work rs) (bank template (fun _ => []) (Function.update rs 3 rank)) := by
  let s := bank template work rs
  let mid := Function.update s (reg 3) []
  let finalRegs := Function.update rs 3 rank
  let finish := bank template work finalRegs
  have hc := CallClear.clear_runs (reg 3) s
  have hl : (s (reg 3)).length = w := length_wordBits _
  rw [hl] at hc
  have cp := SuccessorFields.prependCopy_runs (workPort result) (reg 3) scratch
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) mid rfl
  have hv : mid (workPort result) = wordBits rank := hr
  have hfinish : Function.update mid (reg 3) (mid (workPort result) ++ mid (reg 3)) = finish := by
    rw [hv, show mid (reg 3) = [] from Function.update_self .., List.append_nil]
    exact (Function.update_idem ..).trans (update_reg ..)
  rw [hfinish, hv, length_wordBits] at cp
  obtain ⟨k, hk, clean⟩ := CallClear.cleanup_runs workPorts finish M (by
    intro a ha
    obtain ⟨h, _, rfl⟩ := List.mem_map.mp ha
    exact hs h)
  have hclear : CallClear.erased workPorts finish = bank template (fun _ => []) finalRegs := cleared ..
  rw [hclear] at clean
  have hrun := ((FiniteRoutine.Runs.followedBy (a := CallClear.clear (reg 3))
    (b := SuccessorFields.prependCopy (workPort result) (reg 3) scratch) hc cp).followedBy clean)
  have hk' : k ≤ Fintype.card H*(M+1)+1 := by simpa [workPorts] using hk
  have htime : (w+1)+(5*w+2)+k ≤ returnClock H w M := Nat.add_le_add_left hk' _
  exact ⟨_, htime, spaceRun_of_steps hrun (fun k => Nat.add_le_add (bank_bound template work rs M hw ht hs k) htime)⟩

/-- Prepare, invoke, and reclaim one rank workspace while retaining the
immutable template for any later prefix. -/
noncomputable def rankCall (dynamic : H → Bool) (r : FiniteRoutine H) (result : H) :=
  ((copyIn dynamic).followedBy (callRank r)).followedBy (returnRank result)

/-- Stack-height allowance for staging and returning a prefix-rank call when the incoming bank
has stack heights at most M. -/
def callSpace (H : Type) [Fintype H] (w M : ℕ) :=
  M + max (copyClock H M) (returnClock H w M)

theorem rankCall_bounded (dynamic : H → Bool) (r : FiniteRoutine H) (result : H)
    (template out : Stacks H) (rs : Regs 5 w) (rank : Word w) (M t : ℕ) (hw : w ≤ M)
    (ht : ∀ h, (template h).length ≤ M) (run : r.BoundedRun M t (prepared dynamic template rs) out)
    (hr : out result = wordBits rank) :
    ∃ k ≤ copyClock H M+t+returnClock H w M,
      (rankCall dynamic r result).BoundedRun (callSpace H w M) k
        (bank template (fun _ => []) rs) (bank template (fun _ => []) (Function.update rs 3 rank)) := by
  obtain ⟨a, ha, h₁⟩ := copyIn_bounded dynamic template rs M hw ht
  have h₂ := callRank_bounded r template rs hw ht run
  obtain ⟨b, hb, h₃⟩ := returnRank_bounded result template out rs rank M hw ht run.final_cap hr
  refine ⟨a+t+b, Nat.add_le_add (Nat.add_le_add_right ha _) hb, ?_⟩
  apply FiniteRoutine.BoundedRun.followedBy (a := (copyIn dynamic).followedBy (callRank r))
  · exact FiniteRoutine.BoundedRun.followedBy (a := copyIn dynamic) (b := callRank r)
      (h₁.mono_cap (Nat.add_le_add_left (le_max_left ..) _)) (h₂.mono_cap (Nat.le_add_right ..))
  · exact h₃.mono_cap (Nat.add_le_add_left (le_max_right ..) _)

end RankQuery.Stack.Coordinate.PrefixWorkspace

end VPVNP
end Computability
end OAI
