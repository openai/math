import OAI.Optimization.LinearProgramming.Recovery.OddBoundary
import OAI.Optimization.LinearProgramming.Recovery.OddEpochControl
import OAI.Optimization.LinearProgramming.BitRAM.DispatchPrefixFacts

/-! First-restart receipts for a packed bit-PCG epoch. A successful service supplies the
actual next bit, while an interruption returns the observed request and the resulting
numerical memory to the caller. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PackedPCG

variable {K : Type*}
open RAM RAM.Tape RAM.Callable OracleSpec BitRAM

/-- The source configuration owns the emitted word in its reversed buffer. The finite
control address is where the program resumes after a successful numerical answer. -/
abbrev Receipt (p : BitProgram) (K : Type*) :=
  p.Config → Fin p.states → Memory K → Memory K → Prop

structure Environment (K : Type*) where
  cache : Transcript → Memory K → Prop
  ports : Memory K → Prop
  preserve : ∀ a t, t.data=a.data → StableHeaders a t → ports a → ports t

structure Live (p : BitProgram) (P : K → Prop) (env : Environment K) (c : p.Config)
    (native vm : Memory K) : Prop where
  represented : Rep p c vm
  vmSafe : Good P vm
  nativeSafe : native.AllData P
  ports : env.ports vm
  cache : env.cache c.transcript native
  clean : vm.index statusReg=0

inductive Mark (p : BitProgram) (bo : WordOracle) (P : K → Prop) (env : Environment K)
    (ack cut : Receipt p K) (s : p.Config) (q : Fin p.states) (before next vm : Memory K) : Prop where
  | answered (receipt : ack s q before next) (live : Live p P env (Dispatch.answered bo s q) next vm)
  | interrupted (receipt : cut s q before next) (nativeSafe : next.AllData P) (safe : Good P vm)
      (nil : vm.index nilReg=0) (flag : 0<vm.index statusReg) (ports : env.ports vm)

/-- The chronological source path up to the first genuine interruption or the completed halt. -/
inductive ServiceTrace (p : BitProgram) (bo : WordOracle) (ack cut : Receipt p K) :
    p.Config → Memory K → Dispatch.Stop p → Memory K → Prop where
  | halted {c n s native} (pre : Dispatch.Prefix p c n (.halted s)) :
      ServiceTrace p bo ack cut c native (.halted s) native
  | interrupted {c n s q native next} (pre : Dispatch.Prefix p c n (.request s q))
      (receipt : cut s q native next) : ServiceTrace p bo ack cut c native (.request s q) next
  | answered {c n s q native next z final} (pre : Dispatch.Prefix p c n (.request s q))
      (receipt : ack s q native next) (tail : ServiceTrace p bo ack cut (Dispatch.answered bo s q) next z final) :
      ServiceTrace p bo ack cut c native z final

/-- Every successful service up to a specified pending packet. Its final native bank
is the actual input of the interrupted numerical call. -/
inductive AnsweredPrefix (p : BitProgram) (bo : WordOracle) (ack : Receipt p K) :
    p.Config → Memory K → p.Config → Fin p.states → Memory K → Prop where
  | pending {c n s q native} (pre : Dispatch.Prefix p c n (.request s q)) :
      AnsweredPrefix p bo ack c native s q native
  | answered {c n s q native next stopPC stopNext before} (pre : Dispatch.Prefix p c n (.request s q))
      (receipt : ack s q native next)
      (tail : AnsweredPrefix p bo ack (Dispatch.answered bo s q) next stopPC stopNext before) :
      AnsweredPrefix p bo ack c native stopPC stopNext before

private theorem ServiceTrace.final_receipt {p : BitProgram} {bo : WordOracle} {ack cut : Receipt p K}
    {c : p.Config} {native final : Memory K} {z : Dispatch.Stop p} (h : ServiceTrace p bo ack cut c native z final) :
    match z with
    | .halted _ => True
    | .request s q => ∃ before, AnsweredPrefix p bo ack c native s q before ∧ cut s q before final := by
  induction h with
  | halted => trivial
  | interrupted pre why => exact ⟨_,.pending pre,why⟩
  | @answered c n s q native next z final pre why _ ih =>
    cases z with
    | halted => trivial
    | request stopPC stopNext =>
      obtain ⟨before,path,last⟩ := ih
      exact ⟨before,.answered pre why path,last⟩

theorem ServiceTrace.last_cut {p : BitProgram} {bo : WordOracle} {ack cut : Receipt p K}
    {c s : p.Config} {q : Fin p.states} {native final : Memory K}
    (h : ServiceTrace p bo ack cut c native (.request s q) final) :
    ∃ before, AnsweredPrefix p bo ack c native s q before ∧ cut s q before final :=
  h.final_receipt

/-- The final native bank contains exactly the last cache in the receipt. The stopped
bit bank exposes both the source halt code and the public restart flag. -/
def Produced (p : BitProgram) (P : K → Prop) (env : Environment K) (last : p.Config) :
    Dispatch.Stop p → Memory K → Memory K → Prop
  | .halted s, native, vm => s=last ∧ Live p P env s native vm ∧ vm.index stateReg=p.states
  | .request _ _, native, vm => 0<vm.index statusReg ∧ vm.index stateReg=p.states ∧
      native.AllData P ∧ Good P vm ∧ env.ports vm ∧ vm.index nilReg=0

def epochLoop (p : BitProgram) (handler : Fragment) : Fragment :=
  framedLoop p statusReg (boundary p handler)

theorem prefix_action {p : BitProgram} {c : p.Config} {n : ℕ} {z : Dispatch.Stop p}
    (pre : Dispatch.Prefix p c n z) :
    match z with
    | .halted s => s.pc=none
    | .request s q => ∃ pc, s.pc=some pc ∧ p.instruction pc (s.store (p.scan pc)).head? = .ask q := by
  induction pre with
  | halted pc => exact pc
  | request pc ask => exact ⟨_,pc,ask⟩
  | @next _ _ _ _ stop _ _ _ ih => cases stop <;> exact ih

theorem halt_start {p : BitProgram} {bo : WordOracle} {c d : p.Config} {n : ℕ}
    (h : p.Run bo c n d) (closed : c.pc=none) : c=d ∧ n=0 := by
  cases h with
  | refl => exact ⟨rfl,rfl⟩
  | step edge _ =>
    obtain ⟨q,pc⟩ := Dispatch.tick_running edge
    rw [closed] at pc
    contradiction

theorem Live.refresh {p : BitProgram} {P : K → Prop} {env : Environment K} {c : p.Config}
    {native vm : Memory K} (h : Live p P env c native vm) : Live p P env c native (vm.putIndex Dispatch.limitReg p.states) :=
  ⟨h.represented.putScratch (i := Dispatch.limitReg) (by decide) _,h.vmSafe,h.nativeSafe,
    env.preserve vm _ rfl (ready_headers vm _) h.ports,h.cache,
    (Memory.putIndex_ne vm (by decide : statusReg≠Dispatch.limitReg) _).trans h.clean⟩

/-- The very same two real VM headers choose whether the outer LP retry loop repeats. -/
theorem Produced.retry_test {K : Type*} [LT K] [DecidableLT K] {p : BitProgram} {P : K → Prop} {env : Environment K} {last : p.Config}
    {z : Dispatch.Stop p} {native vm : Memory K} (h : Produced p P env last z native vm) :
    (Odd.cond (.addrLT nilReg statusReg)).test (Odd.memory native vm) =
      match z with | .halted _ => false | .request .. => true := by
  rw [Odd.cond_test]
  cases z with
  | halted s =>
    obtain ⟨_,live,_⟩ := h
    simp [Cond.test,live.clean]
  | request s q =>
    obtain ⟨flag,_,_,_,_,nil⟩ := h
    simp [Cond.test,nil,flag]

section Ordered
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A handler certificate at an actual reachable boundary. The prior numeric memory,
the saved bit prefix, the certified suffix, and the heap representation are all explicit. -/
def Handles (p : BitProgram) (bo : WordOracle) (P : K → Prop) (env : Environment K)
    (ack cut : Receipt p K) (handler : Fragment) (start last : p.Config) (budget : ℕ) : Prop :=
  ∀ {c : p.Config} {used time : ℕ} {native vm : Memory K}, p.Run bo start used c → p.Run bo c time last →
    Live p P env c native vm → ∀ {n s q u}, Dispatch.Prefix p c n (.request s q) →
    Dispatch.Suffix bo n time last (.request s q) → Awaiting p s q u → Good P u → u.data=vm.data →
    StableHeaders vm u → ∃ next v, (transfer p handler).Run P (Odd.memory native u) budget (Odd.memory next v) ∧
      Mark p bo P env ack cut s q native next v

end Ordered

structure Cursor (p : BitProgram) (K : Type*) where
  source : p.Config
  native : Memory K
  left : ℕ

def Active (p : BitProgram) (bo : WordOracle) (P : K → Prop) (env : Environment K)
    (start last : p.Config) (x : Cursor p K) (physical : Memory K) : Prop :=
  (∃ i, p.Run bo start i x.source) ∧ p.Run bo x.source x.left last ∧
  ∃ m, physical=Odd.memory x.native m ∧ Live p P env x.source x.native m ∧ m.index Dispatch.limitReg=p.states

end PackedPCG
end Recovery
end LinearProgramming
end Optimization
end OAI
