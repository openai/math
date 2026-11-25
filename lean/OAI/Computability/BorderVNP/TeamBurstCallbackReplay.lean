import OAI.Computability.BorderVNP.TeamBurstCallback
import OAI.Computability.BorderVNP.TeamBurstProbeReplay

/-! # Chronological path replay through the complete burst callback

The caller selects a fixed pair of live register indices. Along the unique spelling of
a given vector of previous words, the callback takes the range check, emits the prescribed
two sorting records per word, and arrives at the private continuation. The arbitrary
following choice stream is preserved, including when the burst has length zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamBurstCallback

open VPVNP BurstRAM RAMTape RAMSerialization TeamPrivateFragment
open TeamBurstCallbackSetup (Port Ready)

variable {r w H : ℕ} {hw : 2 ≤ w+1} {addr len : Fin r} {a q tick cap : Word w}
variable {rs : List (WordRecord (w+1))} {s : Stacks (Port r)}
variable {K R : Type} [DecidableEq K]

/-- A valid burst replays its chronological vector of guesses, preserves every architectural
register, appends its timed sorter records and fills the private input in low-bit-first order. -/
theorem replay_callback (target : StackCode K R) (ports : Port r → K) (hp : Function.Injective ports)
    (label : State addr len → R) (resume : R)
    (hr : ∀ z, target (label z) = rows addr len ports label resume z) (base : Stacks K)
    (ready : Ready hw H addr len a q tick cap rs s)
    (legal : q.val ≤ cap.val ∧ a.val+q.val ≤ 2^w) (free : rs.length+2*q.val ≤ 4*H)
    (vs : List (Word w)) (length : vs.length = q.val) (suffix : List Bool) :
    ∃ t out, t ≤ entryCost w q.val + TeamBurstProbe.loopTime w q.val 0 ∧
      StackRuns (replay target) t (label (start addr len), TeamBurstProbe.choices vs++suffix)
        (installStacks ports base s) (resume,suffix) (installStacks ports base out) ∧
      TeamBurstProbeStep.Ready hw H (TeamBurstProbe.advance q.val a) (TeamBurstProbe.advance q.val tick)
        (rs++TeamBurstProbe.records a tick vs) [] (out ∘ Port.step) ∧
      out (.step .privateInput) = TeamBurstProbe.bytes vs ∧ out (.step .marks) = [] ∧
      out (.step .width) = List.replicate w true ∧ out (.step .saved) = [] ∧
      (∀ i, out (.reg i) = s (.reg i)) ∧ out .stamp = s .stamp ∧ out .maxBurst = s .maxBurst ∧
      (∀ j, out (.guard j) = initialized addr len s q.val (.guard j)) ∧ out .high = [] := by
  let staged := initialized addr len s q.val
  let bank := installStacks ports base staged
  have inj : Function.Injective (ports ∘ Port.step) := hp.comp fun _ _ h => Port.step.inj h
  have mount : installStacks (ports ∘ Port.step) bank (staged ∘ Port.step) = bank :=
    installStacks_eq inj _ _ fun _ => installStacks_at hp ..
  obtain ⟨n,hn,prep⟩ := start_valid target ports hp label resume hr base ready legal
  have go := replay_segment prep (TeamBurstProbe.choices vs++suffix)
  have hloop : TeamBurstProbe.LoopReady hw H a tick rs [] vs.length (staged ∘ Port.step) := by
    rw [length]; exact ready_loop ready
  obtain ⟨k,u,hk,loop,stepReady,input,marks,width,saved⟩ := TeamBurstProbe.replay_runs
    target (ports ∘ Port.step) inj (label ∘ State.loop) resume (fun z => hr (.loop z)) bank
    vs a tick rs [] suffix (staged ∘ Port.step) hloop (by simpa [length] using free)
  rw [mount, mount_step ports hp base staged] at loop
  simp only [length, List.length_nil, List.reverse_nil, List.nil_append] at hk stepReady input
  exact ⟨_, withStep staged u, Nat.add_le_add hn hk, go.trans loop, stepReady, input, marks,
    width, saved, fun _ => rfl, rfl, rfl, fun _ => rfl, rfl⟩

end TeamBurstCallback

end BorderVNP
end Computability
end OAI
