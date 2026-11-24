import OAI.Computability.VPVNP.LiveProgramCompressedPair
import OAI.Computability.VPVNP.LiveNativePairContinuation

/-!
# Accounting for all linked calls of the compressed pair

The online dispatcher reads six workspace words in addition to its own
probes. The compressed-pair linker and the surrounding live-group linker
each read one tag and may write one transfer. The same source report
sequences determine the two margins in the native single-pair specification.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair

open BurstRAM CompressorRecords PairStages

variable {w : ℕ} (pub : Fin 11 → Word w) (E : UniversalMachine.Program) (tag : Word w)

/-- Both tags are charged on every call, including the final call of a stage. -/
def linkedRow (i : Stage) (r : Report w) :=
  LiveStageLink.linkedReport (LiveProgram.next E) tag LiveProgram.Stage.pair (report pub i r)

theorem linkedRow_bounds (i : Stage) (r : Report w) :
    (linkedRow pub E tag i r).probes ≤ r.probes+4 ∧
      (linkedRow pub E tag i r).events.length ≤ r.events.length+77 := by
  have hi := report_effect pub i r (fun _ => 0)
  have ho := LiveStageLink.linkedReport_probes (LiveProgram.next E) tag LiveProgram.Stage.pair (report pub i r)
  have ht := LiveStageLink.linkedReport_length_le (LiveProgram.next E) tag LiveProgram.Stage.pair (report pub i r)
  change (linkedRow pub E tag i r).events.length ≤ (report pub i r).events.length + 2*21+5 at ht
  change (linkedRow pub E tag i r).probes = (report pub i r).probes+1+_ at ho
  obtain ⟨_,hp,ht',_⟩ := hi
  constructor
  · split at hp <;> split at ho <;> omega
  · omega

/-- Online reports after the workspace reads and the two enclosing dispatches. -/
def onlineLogs (base : Word w) (m : Memory w) (rs : List (Report w)) :=
  (OnlineWorkspace.framed base m rs).map (linkedRow pub E tag .online)

/-- Terminal reports as executed by the enclosing live pair stage. -/
def terminalLogs (rs : List (Report w)) := rs.map (linkedRow pub E tag .terminal)

/-- The startup reports, each charged for its own stage transition. -/
def wrappedStartup (src : List (Stage × Report w)) := src.map (fun p => linkedRow pub E tag p.1 p.2)

/-- The startup, online and terminal reports in their execution order. -/
def logs (base : Word w) (m : Memory w) (startup : List (Stage × Report w)) (online terminal : List (Report w)) :=
  wrappedStartup pub E tag startup ++ onlineLogs pub E tag base m online ++ terminalLogs pub E tag terminal

theorem onlineCost (base : Word w) (m : Memory w) (rs : List (Report w)) :
    RAMBuckets.cost Report.probes (onlineLogs pub E tag base m rs) ≤ 11*RAMBuckets.cost Report.probes rs := by
  induction rs generalizing m with
  | nil => simp [onlineLogs,OnlineWorkspace.framed,RAMBuckets.cost]
  | cons a rs ih =>
    have frame := (Workspace.report_effect base m a).2.1
    have link := (linkedRow_bounds pub E tag .online (Workspace.report base m a)).1
    have tail := ih (after m a.events)
    change 1+(linkedRow pub E tag .online (Workspace.report base m a)).probes +
      RAMBuckets.cost Report.probes (onlineLogs pub E tag base (after m a.events) rs) ≤
        11*((1+a.probes)+RAMBuckets.cost Report.probes rs)
    omega

theorem terminalCost (rs : List (Report w)) :
    RAMBuckets.cost Report.probes (terminalLogs pub E tag rs) ≤ 5*RAMBuckets.cost Report.probes rs := by
  induction rs with
  | nil => rfl
  | cons a rs ih =>
    have h := (linkedRow_bounds pub E tag .terminal a).1
    change 1+(linkedRow pub E tag .terminal a).probes+RAMBuckets.cost Report.probes (terminalLogs pub E tag rs) ≤
      5*((1+a.probes)+RAMBuckets.cost Report.probes rs)
    omega

theorem startupCost (src : List (Stage × Report w)) (H : ℕ) (h : ∀ p ∈ src, p.2.probes+5 ≤ H) :
    RAMBuckets.cost Report.probes (wrappedStartup pub E tag src) ≤ src.length*H := by
  induction src with
  | nil => simp [wrappedStartup,RAMBuckets.cost]
  | cons p xs ih =>
    have first := (linkedRow_bounds pub E tag p.1 p.2).1
    have bound := h p (by simp)
    have tail := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
    change 1+(linkedRow pub E tag p.1 p.2).probes+RAMBuckets.cost Report.probes (wrappedStartup pub E tag xs) ≤ _
    rw [List.length_cons,Nat.succ_mul]
    omega

theorem onlineRow (base : Word w) (m : Memory w) (rs : List (Report w)) {a : Report w}
    (h : a ∈ onlineLogs pub E tag base m rs) :
    ∃ b ∈ rs, a.probes ≤ b.probes+10 ∧ a.events.length ≤ b.events.length+101 := by
  induction rs generalizing m with
  | nil => contradiction
  | cons b rs ih =>
    change a ∈ linkedRow pub E tag .online (Workspace.report base m b) ::
      onlineLogs pub E tag base (after m b.events) rs at h
    rcases List.mem_cons.mp h with rfl | h
    · have ⟨_,hp,hl,_,_⟩ := Workspace.report_effect base m b
      have ⟨kp,kl⟩ := linkedRow_bounds pub E tag .online (Workspace.report base m b)
      exact ⟨b,by simp,by omega,by omega⟩
    · obtain ⟨a,ha,h₁,h₂⟩ := ih (after m b.events) h
      exact ⟨a,List.mem_cons_of_mem _ ha,h₁,h₂⟩

/-- The eventual per-branch estimates may be invoked with any fixed
constant. A sixty-fourth share for each of the two variable traversals
suffices after both tag protocols and the online pointer reads. -/
theorem linked_caps (base : Word w) (m : Memory w) (startup : List (Stage × Report w))
    (online terminal : List (Report w)) (S H cap : ℕ) (hS : 32 ≤ S) (hH : 2 ≤ H)
    (hstart : startup.length ≤ 8)
    (hs : ∀ p ∈ startup, p.2.probes+5 ≤ H ∧ p.2.events.length+77 ≤ cap)
    (ho : ∀ b ∈ online, b.probes+11 ≤ H ∧ b.events.length+101 ≤ cap)
    (ht : ∀ b ∈ terminal, b.probes+5 ≤ H ∧ b.events.length+77 ≤ cap)
    (oc : 64*RAMBuckets.cost Report.probes online ≤ S*H)
    (tc : 64*RAMBuckets.cost Report.probes terminal ≤ S*H) :
    let rs := logs pub E tag base m startup online terminal
    RAMBuckets.cost Report.probes rs ≤ S*(H-1) ∧
      ∀ a ∈ rs, 1+a.probes ≤ H ∧ a.events.length ≤ cap := by
  intro rs
  constructor
  · have c₁ := (startupCost pub E tag startup H (fun p hp => (hs p hp).1)).trans (Nat.mul_le_mul_right H hstart)
    have c₂ := onlineCost pub E tag base m online
    have c₃ := terminalCost pub E tag terminal
    have size := Nat.mul_le_mul_right H hS
    have gap := Nat.mul_le_mul_left S (show H ≤ 2*(H-1) by omega)
    rw [show S*(2*(H-1))=2*(S*(H-1)) by ring] at gap
    simp only [rs,logs,RAMBuckets.cost_append]
    omega
  · intro a ha
    simp only [rs,logs,List.mem_append] at ha
    rcases ha with (ha|ha)|ha
    · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ha
      have ⟨hp',hl⟩ := hs p hp
      have ⟨kp,kl⟩ := linkedRow_bounds pub E tag p.1 p.2
      exact ⟨by omega,by omega⟩
    · obtain ⟨b,hb,kp,kl⟩ := onlineRow pub E tag base m online ha
      obtain ⟨hp,hl⟩ := ho b hb
      exact ⟨by omega,by omega⟩
    · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
      obtain ⟨hp,hl⟩ := ht b hb
      have ⟨kp,kl⟩ := linkedRow_bounds pub E tag .terminal b
      exact ⟨by omega,by omega⟩

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI
