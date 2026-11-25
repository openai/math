import OAI.Computability.BorderVNP.FiniteProcessorLoop

/-! # The physical burst prefix of a field-valued callback

The consecutive read words, old-value guesses, emitted record pairs and clocks
are those of the original guarded burst. The field accumulator reaches the
private loader without changing.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldProcessor

open VPVNP BurstRAM RAMTape TeamSite TeamSite.Work TeamPrivateFragment
open RAMSerialization (WordRecord)
open private rename_acc from OAI.Computability.BorderVNP.FiniteProcessorWeightSegments
open private callback from OAI.Computability.BorderVNP.TeamSiteLoop
open private burstClock from OAI.Computability.BorderVNP.TeamSiteWorkBurst

variable {Q Γ : Type} {p r k a m g w H : ℕ} {F : Type*} [Field F] [Fintype F] {hw : 2 ≤ w+1}
variable {rs : List (WordRecord (w+1))}

omit [Field F] in
private theorem rows_acc {K R : Type} (addr len : Fin r) (ports : TeamBurstCallbackSetup.Port r → K)
    (label : TeamBurstCallback.State addr len → R) (resume : R) (z : TeamBurstCallback.State addr len) (acc : F) :
    (TeamBurstCallback.rows addr len ports label resume z).rename id (fun q => (q,Fintype.equivFin F acc)) =
    TeamBurstCallback.rows addr len ports (fun q => (label q,Fintype.equivFin F acc)) (resume,Fintype.equivFin F acc) z := by
  cases z with
  | setup u | entry u =>
    simp only [TeamBurstCallback.rows,rename_acc]
    congr 1
    funext z
    cases z <;> rfl
  | loop q =>
    cases q with
    | test =>
      simp only [TeamBurstCallback.rows,TeamBurstProbe.rows,StackOp.rename,id_eq]
      congr 1
      funext b
      cases b <;> rfl
    | guess u =>
      simp only [TeamBurstCallback.rows,TeamBurstProbe.rows,rename_acc]
      congr 1
      funext z
      cases z <;> rfl
    | emit u | finish u =>
      simp only [TeamBurstCallback.rows,TeamBurstProbe.rows,rename_acc]
      congr 1
      funext z
      cases z <;> rfl

/-- A valid physical burst produces the exact record suffix, fills the private
input in chronological order, and retains every clock and architectural port.
Its last transition already enters the real private loader. -/
theorem burst_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (weights : Returns Q Γ F m a) (acc : F) (sg : Option Bool) (j : Fin a) (addr len : Fin r) (pc : Fin p)
    {s : Stacks (Port r k (m*g))} (h : Ready hw H rs s) (start length tick cap : Word w)
    (address : s (isa (.reg addr)) = wordBits start) (count : s (isa (.reg len)) = wordBits length)
    (stamp : s (.clock .stamp) = wordBits tick) (maxBurst : s (.clock .maxBurst) = wordBits cap)
    (legal : length.val ≤ cap.val ∧ start.val+length.val ≤ 2^w)
    (free : rs.length+2*length.val ≤ 4*H) (vs : List (Word w)) (hv : vs.length = length.val) (suffix : List Bool) :
    ∃ t out, t ≤ 1 + TeamBurstCallback.entryCost w length.val + TeamBurstProbe.loopTime w length.val 0 ∧
      StackRuns (replay (loopCode P lib weights)) t
        ((.clock sg (.exit (.callback (.call j addr len pc))),Fintype.equivFin F acc), TeamBurstProbe.choices vs++suffix) s
        ((.privateCall sg j pc (.load .start),Fintype.equivFin F acc),suffix) out ∧
      Bank hw H (rs++TeamBurstProbe.records start tick vs) (TeamPrivateCall.inputBits vs) out ∧
      out ∘ Port.clock = s ∘ Port.clock := by
  let label := fun z => (Loop.Label.burst (P := P) (Q := Q) (m := m) (g := g) sg j addr len pc z,Fintype.equivFin F acc)
  let resume := (Loop.Label.privateCall (P := P) (Q := Q) (m := m) (g := g) sg j pc (.load .start),Fintype.equivFin F acc)
  let base := s ∘ Loop.burstPort
  have ready := h.burstReady addr len address count stamp maxBurst
  obtain ⟨t,u,ht,run,step,raw,marks,width,saved,regs,st,cap',guard,high⟩ :=
    TeamBurstCallback.replay_callback (loopCode P lib weights) Loop.burstPort Loop.burstPort_injective label resume
      (fun z => by simp only [loopCode,FieldStack.productCode,label,loopFactor,Equiv.symm_apply_apply,mul_one,Loop.code]
                   exact rows_acc ..) s ready legal free vs hv suffix
  rw [installStacks_eq Loop.burstPort_injective s base (fun _ => rfl), installBurst] at run
  have first : StackRuns (replay (loopCode P lib weights)) 1
      ((.clock sg (.exit (.callback (.call j addr len pc))),Fintype.equivFin F acc), TeamBurstProbe.choices vs++suffix) s
      (label (TeamBurstCallback.start addr len),TeamBurstProbe.choices vs++suffix) s := by
    apply StackRuns.cons _ (StackRuns.nil ..)
    exact .goto (by simp [replay,loopCode,FieldStack.productCode,Loop.code,loopFactor,callback,label,StackOp.rename])
  refine ⟨_,_,by omega,first.trans run,?_,burstClock s u regs st cap'⟩
  refine ⟨?_,step.scratch,step.lifted,step.buffer,step.fields,?_,
    raw.trans (TeamBurstProbe.bytes_eq_inputBits _),h.temp,h.tracks⟩
  · intro i
    cases i with
    | address => rw [show withBurst s u (probe (.operand .address)) = _ from step.address, length_wordBits]
    | tick => rw [show withBurst s u (probe (.operand .tick)) = _ from step.time, length_wordBits]
    | before => rw [show withBurst s u (probe (.operand .before)) = [] from step.before]; simp
    | after => rw [show withBurst s u (probe (.operand .after)) = [] from step.after]; simp
  · intro aux
    cases aux with
    | reverse => change (u (.step .privateReverse)).length ≤ w; rw [show u (.step .privateReverse) = [] from step.bytes]; simp
    | marks => change (u (.step .marks)).length ≤ w; simp [marks]
    | width => change (u (.step .width)).length ≤ w; simp [width]
    | saved => change (u (.step .saved)).length ≤ w; simp [saved]
    | high => change (u .high).length ≤ w; simp [high]
    | guard i =>
      change (u (.guard i)).length ≤ w; rw [guard]
      cases i with
      | length => change (s (isa (.reg len))).length ≤ w; simp [count]
      | address => exact h.aux (.guard .address)
      | cap => exact h.aux (.guard .cap)
      | _ => exact Nat.zero_le _

end FieldProcessor

end BorderVNP
end Computability
end OAI
