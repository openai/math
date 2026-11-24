import OAI.Computability.VPVNP.LiveCompressedPairHandoff
import OAI.Computability.VPVNP.LiveCompressedPairExecution

/-!
# The reachable online and terminal phases of a compressed pair

When the online calendar returns, the next call stays in its source
invariant. When it accepts, the native transfer installs the terminal tag
in the actual memory belonging to a complete online path. Thus every
continuing call after the deterministic startup belongs to one of these
two source phases, including prefixes that may subsequently reject.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair

open BurstRAM BurstRAM.PrivateRAM CompressorRecords CompressorRecords.Schedule LiveStageLink

variable {w d initial phases : ℕ} {C : Catalog d} {b : Bootstrap} {plan : Online.Config C initial phases}
    {finalTable : PairTable} {pub : Fin 11 → Word w} {clock : ℕ}

local notation "T" => components b plan finalTable
local notation "addr" => PairTag.address pub

/-- Source invariants need to protect an outer address only on calls
reachable within that phase. This includes the source accepting exit. -/
def Protected.word {s : Stage} {input : Memory w} (safe : Protected b plan finalTable pub clock s input) (a : ℕ) : Prop :=
  ∀ st m bits r, safe.invariant st m → m (addr).val = tagWord w s →
    execute (sourceProgram T pub s) (clockAt pub clock s) ((sourceProgram T pub s).start st) m bits = some r →
    after m r.events a = m a

private def Back (input : Memory w) (st : Word w) (m : Memory w) : Prop :=
  ∀ bs rs finish, Completion T next pub addr Stage.online (clockAt pub clock Stage.online) st m bs rs finish →
    ∃ qs logs, Completion T next pub addr Stage.online (clockAt pub clock Stage.online) 0 input qs logs finish

private theorem post_of_completion {input finish : Memory w} {bits : List (List Bool)} {rs : List (Report w)}
    (done : Completion T next pub addr Stage.online (clockAt pub clock Stage.online) 0 input bits rs finish) :
    ∃ path : StagePaths b plan finalTable pub clock Stage.online input,
      onlinePost path = writeMemory finish addr (tagWord w Stage.terminal) := by
  obtain ⟨hr,hh,hm,hf⟩ := done.spec
  let a : StagePaths b plan finalTable pub clock Stage.online input := ⟨bits,rs,hr,hh,hf⟩
  have hlogs : ordinaryReports a = rs := Option.some.inj ((ordinaryRun a).symm.trans hr)
  exact ⟨a,by unfold onlinePost; rw [hlogs,hm]; rfl⟩

private theorem native {s : Stage} {st : Word w} {m : Memory w} {bits : List Bool} {out : Report w}
    (fit : 10 ≤ 2^w) (tag : m (addr).val = tagWord w s)
    (run : execute (program b plan finalTable pub) clock ((program b plan finalTable pub).start st) m bits = some out) :
    ∃ rep, execute (sourceProgram T pub s) (clockAt pub clock s) ((sourceProgram T pub s).start st) m bits = some rep ∧
      room next addr s (clockAt pub clock s) rep ∧ out = report pub s rep := by
  have fuel : clockAt pub clock s = clock-overhead pub s := by simp [clockAt,overhead,Nat.sub_sub,Nat.add_comm]
  obtain ⟨r,h,hr,ho⟩ := (execute_stage_iff b plan finalTable pub s fit clock st m tag bits out).mp run
  have exactCall := execute_widen_start (stages b plan finalTable s).table (embedding b plan finalTable s) id pub
    (clockAt pub clock s) st m bits
  rw [← fuel] at h hr
  exact ⟨r,exactCall.trans h,hr,ho⟩

variable {input : Memory w} (online : Protected b plan finalTable pub clock Stage.online input)
variable (terminal : ∀ p : StagePaths b plan finalTable pub clock Stage.online input,
  Protected b plan finalTable pub clock Stage.terminal (onlinePost p))

/-- The terminal invariant is indexed by the actual completed online path. -/
def Phase (st : Word w) (m : Memory w) : Prop :=
  (online.invariant st m ∧ m (addr).val = tagWord w Stage.online ∧
    Back (b := b) (plan := plan) (finalTable := finalTable) (pub := pub) (clock := clock) input st m) ∨
  ∃ p : StagePaths b plan finalTable pub clock Stage.online input,
    (terminal p).invariant st m ∧ m (addr).val = tagWord w Stage.terminal

theorem Phase.start (tag : input (addr).val = tagWord w Stage.online) : Phase online terminal 0 input :=
  Or.inl ⟨online.ready,tag,fun bs rs _ done => ⟨bs,rs,done⟩⟩

/-- One arbitrary continuing native call stays in its recorded phase or
enters the terminal phase with the right post-memory, and preserves the
chosen address. No accepting extension of this call is required. -/
theorem Phase.step (fit : 10 ≤ 2^w) (a : ℕ) (separate : a ≠ (addr).val)
    (wo : online.word a) (wt : ∀ p, (terminal p).word a)
    {st st' : Word w} {m : Memory w} {bits : List Bool} {out : Report w}
    (active : Phase online terminal st m)
    (run : execute (program b plan finalTable pub) clock ((program b plan finalTable pub).start st) m bits = some out)
    (continues : out.result = some st') :
    Phase online terminal st' (after m out.events) ∧ after m out.events a = m a := by
  rcases active with ⟨inv,tag,back⟩ | ⟨p,inv,tag⟩
  · obtain ⟨r,source,room,rfl⟩ := native fit tag run
    have word := wo _ _ _ _ inv tag source
    have effect := (report_effect pub Stage.online r m).2.2.2
    cases result : r.result with
    | some s =>
      have hs : s = st' := by simpa only [report,linkedReport,prependLog,exitReport,result,Option.some.injEq] using continues
      subst s
      rw [result] at effect
      rw [effect]
      obtain ⟨I,ht⟩ := online.frame st m bits r st' inv tag source result
      exact ⟨Or.inl ⟨I,ht,fun _ _ _ tail => back _ _ _ (.more source result room tail)⟩,word⟩
    | none =>
      have stzero : (0 : Word w) = st' := by
        simpa only [report,linkedReport,prependLog,exitReport,result,show next Stage.online=some Stage.terminal from rfl,
          Option.some.injEq] using continues
      subst st'
      obtain ⟨qs,rs,done⟩ := back _ _ _ (.last source result room)
      obtain ⟨p,hp⟩ := post_of_completion done
      rw [result,show next Stage.online=some Stage.terminal from rfl] at effect
      rw [effect]
      refine ⟨Or.inr ⟨p,Eq.mp (congrArg ((terminal p).invariant 0) hp) (terminal p).ready,?_⟩,?_⟩
      · simp [writeMemory]
      · simp [writeMemory,separate,word]
  · obtain ⟨r,source,_,rfl⟩ := native fit tag run
    have word := wt p _ _ _ _ inv tag source
    have effect := (report_effect pub Stage.terminal r m).2.2.2
    cases result : r.result with
    | none =>
      simp only [report,linkedReport,prependLog,exitReport,result,show next Stage.terminal=none from rfl] at continues
      contradiction
    | some s =>
      have hs : s = st' := by simpa only [report,linkedReport,prependLog,exitReport,result,Option.some.injEq] using continues
      subst s
      rw [result] at effect
      rw [effect]
      obtain ⟨I,ht⟩ := (terminal p).frame st m bits r st' inv tag source result
      exact ⟨Or.inr ⟨p,I,ht⟩,word⟩

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI
