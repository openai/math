import OAI.Optimization.LinearProgramming.Recovery.OddEpochModel

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PackedPCG

variable {K : Type*}

open RAM RAM.Tape RAM.Callable OracleSpec BitRAM
def BoundaryPost (p : BitProgram) (bo : WordOracle) (P : K → Prop) (env : Environment K)
    (ack cut : Receipt p K) (before : Memory K) : Dispatch.Stop p → Memory K → Memory K → Prop
  | .halted s, next, vm => next=before ∧ Live p P env s next vm
  | .request s q, next, vm => Mark p bo P env ack cut s q before next vm

theorem physical_boundary {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {p : BitProgram} {bo : WordOracle} {P : K → Prop} {env : Environment K}
    {ack cut : Receipt p K} {handler : Fragment} {start last c : p.Config} {budget used time : ℕ}
    (service : Handles p bo P env ack cut handler start last budget) (ended : last.pc=none)
    (pre : p.Run bo start used c) (source : p.Run bo c time last) {native m : Memory K}
    (live : Live p P env c native m) :
    ∃ n stop next v, Dispatch.Prefix p c n stop ∧ Dispatch.Suffix bo n time last stop ∧
      (boundary p handler).Run P (Odd.memory native m) (boundaryCost p budget n) (Odd.memory next v) ∧
      BoundaryPost p bo P env ack cut native stop next v := by
  apply boundary_run handler source ended live.represented live.vmSafe live.nativeSafe _ budget
  · intro s u walk rep data heads
    have old : s.transcript=c.transcript := walk.history
    have safe : Good P u := fun i => by rw [data]; exact live.vmSafe i
    exact ⟨rfl,rep,safe,live.nativeSafe,env.preserve m u data heads live.ports,
      by simpa only [old] using live.cache,(heads statusReg (by decide) (by decide)).trans live.clean⟩
  · intro n s q u walk aft wait safe data heads
    exact service pre source live walk aft wait safe data heads

abbrev Last (p : BitProgram) (K : Type*) := Dispatch.Stop p × Memory K

def Out (p : BitProgram) (P : K → Prop) (env : Environment K) (last : p.Config)
    (z : Last p K) (physical : Memory K) : Prop :=
  ∃ m, physical=Odd.memory z.2 m ∧ Produced p P env last z.1 z.2 m

theorem ready_safe {p : BitProgram} {bo : WordOracle} {P : K → Prop} {env : Environment K}
    {start last : p.Config} {x : Cursor p K} {outer : Memory K}
    (ready : Active p bo P env start last x outer) : outer.AllData P := by
  obtain ⟨_,_,v,rfl,live,_⟩ := ready
  exact Odd.allData _ _ live.nativeSafe live.vmSafe

theorem ready_finished {K : Type*} [LT K] [DecidableLT K] {p : BitProgram} {bo : WordOracle} {P : K → Prop} {env : Environment K}
    (ack cut : Receipt p K) {start last : p.Config} {x : Cursor p K} {outer : Memory K}
    (ready : Active p bo P env start last x outer) (closed : epochGuard.test outer=false) :
    ∃ z : Last p K, Out p P env last z outer ∧ ServiceTrace p bo ack cut x.source x.native z.1 z.2 := by
  obtain ⟨_,source,m,rfl,live,limit⟩ := ready
  have pc : x.source.pc=none := by
    cases eq : x.source.pc with
    | none => rfl
    | some q =>
      have openGuard : epochGuard.test (Odd.memory x.native m)=true := by
        simp only [epochGuard,Odd.cond_test]
        simp [Cond.test,live.represented.stateCode,pcCode,eq,limit]
      rw [closed] at openGuard
      contradiction
  have equal := (halt_start source pc).1
  have state : m.index stateReg=p.states := by simpa only [pcCode,pc,Option.elim] using live.represented.stateCode
  exact ⟨(.halted x.source,x.native),⟨m,rfl,equal,live,state⟩,.halted (.halted pc)⟩

end PackedPCG
end Recovery
end LinearProgramming
end Optimization
end OAI
