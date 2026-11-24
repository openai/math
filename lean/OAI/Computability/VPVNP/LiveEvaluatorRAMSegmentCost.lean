import OAI.Computability.VPVNP.LiveEvaluatorRAMSegment
import OAI.Computability.VPVNP.RAMSuccessor

/-!
# Native evaluator-group costs in the transcript model

One cost unit pays for each call and one for each external probe. The first
call costs eight units for an accepting carry and ten for a running source.
Each of the two tape scans costs seven units per cell.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorRAM.Schedule

open BurstRAM
open scoped Fin.CommRing

variable {w M : ℕ}

private theorem scan_resources (p : UniversalMachine.Program) (pub : Pub → Word w)
    (hfit : calls (pub 0).val ≤ 2 ^ w) (n i : ℕ) (hi : 0 < i) (hn : i+n = calls (pub 0).val)
    (m : Memory w) (rs : List (Report w))
    (hr : runSegment (nativeProgram p pub) (callFuel p)
      (if i = calls (pub 0).val then none else some (i : Word w)) m (List.replicate n []) = some rs) :
    RAMBuckets.cost Report.probes rs = 7*n ∧ rs.length = n ∧
      ∀ r ∈ rs, r.probes = 6 ∧ r.events.length < callFuel p := by
  induction n generalizing i rs m with
  | zero =>
    simp [runSegment] at hr
    subst rs
    simp [RAMBuckets.cost]
  | succ n ih =>
    have hlt : i < calls (pub 0).val := by omega
    have hz : (i : Word w) ≠ 0 := by
      intro he
      have h := congrArg Fin.val he
      rw [Fin.val_natCast, Nat.mod_eq_of_lt (hlt.trans_le hfit), Fin.val_zero] at h
      omega
    rw [ite_eq_right hlt.ne, List.replicate_succ, runSegment] at hr
    cases he : execute (nativeProgram p pub) (callFuel p) ((nativeProgram p pub).start (i : Word w)) m [] with
    | none => simp [he] at hr
    | some r =>
      simp only [he, Option.map_eq_some_iff] at hr
      obtain ⟨tail, htail, rfl⟩ := hr
      obtain ⟨_, hmem, hprobes, hstate⟩ := nativeCell_report p pub (i : Word w) m [] r hz he
      rw [hstate, show nextState pub (i : Word w) = _ from nextState_at pub i hlt hfit, hmem] at htail
      obtain ⟨hcost, hlen, hcalls⟩ := ih (i+1) (by omega) (by omega) m tail htail
      rw [RAMBuckets.cost, hprobes, hcost, List.length_cons, hlen, List.forall_mem_cons]
      exact ⟨by omega, rfl, ⟨hprobes, nativeStep_report_length p pub _ m _ r he⟩, hcalls⟩

/-- Exact total cost and call count, with a constant clock and probe cap on
every report returned by an accepting native evaluator segment. -/
theorem segmentResources (p : UniversalMachine.Program) (pub : Pub → Word w) (m : Memory w)
    (bits : List (List Bool)) (rs : List (Report w)) (hM : (pub 0).val = M)
    (hfit : calls M ≤ 2^w) (hw : 2 ≤ w) (hstates : p.extra+2 ≤ 2^w)
    (hr : runSegment (nativeProgram p pub) (callFuel p) (some 0) m bits = some rs)
    (hhalt : endState (some 0) rs = none) :
    RAMBuckets.cost Report.probes rs = 1 + (if m (pub 1).val = 1 then 7 else 9) +
      7*(2*(2*M+1)) ∧ rs.length = calls M ∧
      ∀ r ∈ rs, r.probes ≤ 9 ∧ r.events.length < callFuel p := by
  subst M
  obtain ⟨bs, rfl, _, _⟩ := (acceptedSegment_iff p pub m _ bits rfl hfit).mp ⟨rs, hr, hhalt, rfl⟩
  rw [runSegment] at hr
  cases he : execute (nativeProgram p pub) (callFuel p) ((nativeProgram p pub).start 0) m bs with
  | none => simp [he] at hr
  | some r =>
    simp only [he, Option.map_eq_some_iff] at hr
    obtain ⟨tail, htail, rfl⟩ := hr
    obtain ⟨hprobes, _⟩ := nativePrepare_report p pub m bs r hw hstates he
    obtain ⟨_, _, _, _, _, _, hstate, _⟩ := (nativeStep_iff ..).mp he
    have hn := nextState_at pub 0 (by simp [calls]) hfit
    rw [hstate, show nextState pub 0 = _ from hn] at htail
    obtain ⟨hcost, hlen, hcalls⟩ := scan_resources p pub hfit _ 1 (by decide) rfl _ tail htail
    rw [RAMBuckets.cost, hprobes, hcost, List.length_cons, hlen, List.forall_mem_cons]
    refine ⟨rfl, by unfold calls; omega, ⟨?_, nativeStep_report_length p pub _ m _ r he⟩, ?_⟩
    · rw [hprobes]; split <;> decide
    · intro rep hrep
      obtain ⟨h, hclock⟩ := hcalls rep hrep
      exact ⟨by omega, hclock⟩

/-- The native group lies within the successor-chain caps used in Lemma 10.1. -/
theorem segmentWithinCaps (p : UniversalMachine.Program) (pub : Pub → Word w) (m : Memory w)
    (bits : List (List Bool)) (rs : List (Report w)) (hM : (pub 0).val = M)
    (hfit : calls M ≤ 2^w) (hw : 2 ≤ w) (hstates : p.extra+2 ≤ 2^w)
    {S H : ℕ} (hcost : 10 + 7*(2*(2*M+1)) ≤ S*H) (hcap : 10 ≤ H)
    (hr : runSegment (nativeProgram p pub) (callFuel p) (some 0) m bits = some rs)
    (hhalt : endState (some 0) rs = none) : withinCaps S H rs := by
  obtain ⟨ht, _, hc⟩ := segmentResources p pub m bits rs hM hfit hw hstates hr hhalt
  constructor
  · rw [ht]; split <;> omega
  · intro r h
    have := (hc r h).1
    omega

/-- Imposing the native transcript caps preserves each accepting branch path. -/
def capPathEquiv (p : UniversalMachine.Program) (pub : Pub → Word w) (m : Memory w)
    (hM : (pub 0).val = M) (hfit : calls M ≤ 2^w) (hw : 2 ≤ w) (hstates : p.extra+2 ≤ 2^w)
    {S H : ℕ} (hcost : 10 + 7*(2*(2*M+1)) ≤ S*H) (hcap : 10 ≤ H) :
    ActualPaths (nativeProgram p pub) (callFuel p) 0 m (withinCaps S H) ≃
      ActualPaths (nativeProgram p pub) (callFuel p) 0 m (fun _ => True) where
  toFun b := ⟨b.val, by
    obtain ⟨rs, hr, ha, _⟩ := b.property
    exact ⟨rs, hr, ha, trivial⟩⟩
  invFun b := ⟨b.val, by
    obtain ⟨rs, hr, ha, _⟩ := b.property
    exact ⟨rs, hr, ha, segmentWithinCaps p pub m b.val rs hM hfit hw hstates hcost hcap hr ha⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

end LiveEvaluatorRAM.Schedule

end VPVNP
end Computability
end OAI
