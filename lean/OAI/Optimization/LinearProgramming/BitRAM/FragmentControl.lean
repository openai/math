import OAI.Optimization.LinearProgramming.BitRAM.DispatchCompiler
import OAI.Optimization.LinearProgramming.BitRAM.FragmentLoop
import OAI.Optimization.LinearProgramming.BitRAM.DispatchSource

/-! The finite bit interpreter linked to a relocatable ordinary RAM service. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM
namespace Dispatch

variable {K : Type*}

open RAM RAM.Tape RAM.Callable OracleSpec

/-- One compiled bit instruction, with a physical call only on the branch that issued a request. -/
def fragWithCallback (p : BitProgram) (callback : Fragment) : Fragment :=
  .seq (.ofBlock (issuedTable p)) (.branch (.addrLT nilReg askReg) callback (.ofBlock .skip))

/-- Restore the interpreter's halt sentinel at entry and immediately after each concrete callback. -/
def fragController (p : BitProgram) (callback : Fragment) : Fragment :=
  fragmentLoop p (fragWithCallback p callback)

/-- A service only needs to handle words issued by the source run. The return state is part of the
predicate, so two call sites may use different established packet formats. -/
def PermittedAsksFrom (p : BitProgram) (bo : WordOracle) (allowed : p.Config → Fin p.states → Prop)
    (start : p.Config) : Prop :=
  ∀ (u : p.Config) (n : Nat) (q next : Fin p.states), p.Run bo start n u → u.pc = some q →
    p.instruction q (u.store (p.scan q)).head? = .ask next → allowed u next

private theorem permitted_tail {p : BitProgram} {bo : WordOracle} {allowed : p.Config → Fin p.states → Prop}
    {c d : p.Config} {n : Nat} (h : PermittedAsksFrom p bo allowed c) (edge : p.tick bo c = some (n,d)) :
    PermittedAsksFrom p bo allowed d :=
  fun u k q next run pc ask => h u (n+k) q next (.step edge run) pc ask

private theorem ordinary_transcript_eq {p : BitProgram} {c t : p.Config} {op : Op p}
    (h : ordinaryTarget c op = some t) : t.transcript = c.transcript := by
  cases op <;> simp [ordinaryTarget] at h <;> subst t <;> rfl

private theorem stable_limit {m : Memory K} (n : Nat) : StableHeaders m (m.putIndex limitReg n) := by
  intro i low _
  exact Memory.putIndex_ne _ (by unfold limitReg; omega) _

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Real executions of a linked service on permitted source requests. The additional invariant
can relate the public transcript to cache pointers, immutable input data and the service's state. -/
def FragCallbackCorrect (p : BitProgram) (bo : WordOracle) (P : K → Prop)
    (ctx : Transcript → Memory K → Prop) (allowed : p.Config → Fin p.states → Prop)
    (callback : Fragment) (factor : Nat) : Prop :=
  ∀ c q m, allowed c q → Awaiting p c q m → Good P m → ctx c.transcript m →
    ∃ t, callback.Run P m (factor * chargedAsk bo c) t ∧ Rep p (answered bo c q) t ∧
      ctx (answered bo c q).transcript t

/-- The physical dispatch table retains the application's pre-callback environment. Different
numeric services can establish this from the precise index frame their live cache uses. -/
def TableKeeps (p : BitProgram) (P : K → Prop) (ctx : Transcript → Memory K → Prop) : Prop :=
  ∀ (c : p.Config) (q : Fin p.states) (m : Memory K), c.pc = some q → Rep p c m → Good P m →
    ctx c.transcript m → ∃ t j, j ≤ 2*p.states+27 ∧ Block.Eval (Good P) (issuedTable p) m j t ∧
      Issued p c (p.instruction q (c.store (p.scan q)).head?) t ∧ ctx c.transcript t

private theorem tableKeeps_of_headers {p : BitProgram} {P : K → Prop} {ctx : Transcript → Memory K → Prop}
    (keeps : ∀ (h : Transcript) (m t : Memory K), t.data = m.data → StableHeaders m t → ctx h m → ctx h t) :
    TableKeeps p P ctx := by
  intro c q m pc r ok env
  obtain ⟨t,j,hj,run,issue,data,headers⟩ := issuedTable_correct pc r ok
  exact ⟨t,j,hj,run,issue,keeps c.transcript m t data headers env⟩

/-- The table is followed by the actual callback fragment on a permitted request. The ordinary
branch runs the selected action and retains the previous transcript. -/
theorem fragWithCallback_tick_ctx {p : BitProgram} {bo : WordOracle} {P : K → Prop}
    {ctx : Transcript → Memory K → Prop} {allowed : p.Config → Fin p.states → Prop}
    {callback : Fragment} {factor : Nat} (oracle : FragCallbackCorrect p bo P ctx allowed callback factor)
    (table : TableKeeps p P ctx)
    {c d : p.Config} {cost : Nat} (edge : p.tick bo c = some (cost,d))
    (permit : ∀ q next, c.pc = some q → p.instruction q (c.store (p.scan q)).head? = .ask next → allowed c next)
    {m : Memory K} (rep : Rep p c m) (safe : Good P m) (env : ctx c.transcript m) :
    ∃ t, (fragWithCallback p callback).Run P m ((2*p.states+29+factor)*cost) t ∧
      Rep p d t ∧ ctx d.transcript t := by
  obtain ⟨q,pc⟩ := tick_running edge
  obtain ⟨mid,j,hj,code,issued,envMid⟩ := table c q m pc rep safe env
  have tableRun := Fragment.Run.ofBlock (P := P) code
  generalize hop : p.instruction q (c.store (p.scan q)).head? = op at issued
  cases issued with
  | ordinary next rep' =>
    have actual := ordinary_tick bo pc (by rw [hop]; exact next)
    obtain ⟨hc,hd⟩ := Prod.mk.inj (Option.some.inj (actual.symm.trans edge))
    subst cost
    subst d
    have test : (Cond.addrLT nilReg askReg).test mid = false := by
      simp [Cond.test,rep'.heap.nilValue,rep'.askReady]
    have skip := Fragment.Run.ofBlock (P := P) (Block.Eval.skip code.safe_end)
    have real := tableRun.seq (Fragment.Run.branchFalse test callback skip)
    exact ⟨mid,real.mono (by simp; omega),rep', by rw [ordinary_transcript_eq next]; exact envMid⟩
  | @ask next _ wait =>
    have actual := tick_ask (bo := bo) pc hop
    obtain ⟨hc,hd⟩ := Prod.mk.inj (Option.some.inj (actual.symm.trans edge))
    subst cost
    subst d
    obtain ⟨t,respond,rep',env'⟩ := oracle c next mid (permit q next pc hop) wait code.safe_end envMid
    have test : (Cond.addrLT nilReg askReg).test mid = true := by
      simp [Cond.test,wait.heap.nilValue,wait.askFlag]
    have real := tableRun.seq (Fragment.Run.branchTrue test respond (.ofBlock .skip))
    refine ⟨t,real.mono ?_,rep',env'⟩
    have pos : 1 ≤ chargedAsk bo c := by unfold chargedAsk; omega
    have overhead := Nat.mul_le_mul_left (2*p.states+29) pos
    rw [Nat.mul_one] at overhead
    rw [Nat.add_mul]
    omega

theorem fragWithCallback_tick {p : BitProgram} {bo : WordOracle} {P : K → Prop}
    {ctx : Transcript → Memory K → Prop} {allowed : p.Config → Fin p.states → Prop}
    {callback : Fragment} {factor : Nat} (oracle : FragCallbackCorrect p bo P ctx allowed callback factor)
    (keeps : ∀ (h : Transcript) (m t : Memory K), t.data = m.data → StableHeaders m t → ctx h m → ctx h t)
    {c d : p.Config} {cost : Nat} (edge : p.tick bo c = some (cost,d))
    (permit : ∀ q next, c.pc = some q → p.instruction q (c.store (p.scan q)).head? = .ask next → allowed c next)
    {m : Memory K} (rep : Rep p c m) (safe : Good P m) (env : ctx c.transcript m) :
    ∃ t, (fragWithCallback p callback).Run P m ((2*p.states+29+factor)*cost) t ∧
      Rep p d t ∧ ctx d.transcript t := by
  exact fragWithCallback_tick_ctx oracle (tableKeeps_of_headers keeps) edge permit rep safe env

/-- In any outer RAM program containing this fragment, every physical instruction of every
permitted service and of every interpreter iteration is charged to the same source run. -/
theorem fragWithCallback_run_ctx {p : BitProgram} {bo : WordOracle} {P : K → Prop}
    {ctx : Transcript → Memory K → Prop} {allowed : p.Config → Fin p.states → Prop}
    {callback : Fragment} {factor : Nat} (oracle : FragCallbackCorrect p bo P ctx allowed callback factor)
    (table : TableKeeps p P ctx)
    (resetCtx : ∀ h (a : Memory K), ctx h a → ctx h (a.putIndex limitReg p.states))
    {c d : p.Config} {cost : Nat} (source : p.Run bo c cost d) (halted : d.pc = none)
    (permit : PermittedAsksFrom p bo allowed c) {m : Memory K}
    (rep : Rep p c m) (safe : Good P m) (env : ctx c.transcript m) :
    ∃ t, (fragController p callback).Run P m ((2*p.states+32+factor)*cost+2) t ∧
      Rep p d t ∧ ctx d.transcript t := by
  let inv (s : p.Config) (a : Memory K) :=
    Rep p s a ∧ Good P a ∧ ctx s.transcript a ∧ PermittedAsksFrom p bo allowed s
  have init : inv c m := ⟨rep,safe,env,permit⟩
  have restores : ∀ s a, inv s a → inv s (a.putIndex limitReg p.states) := by
    intro s a ha
    exact ⟨ha.1.putScratch (i := limitReg) (by decide) _,ha.2.1,
      resetCtx s.transcript a ha.2.2.1,ha.2.2.2⟩
  have one : ∀ s s' n, p.tick bo s = some (n,s') → ∀ a, inv s a →
      ∃ t, (fragWithCallback p callback).Run P a ((2*p.states+29+factor)*n) t ∧ inv s' t := by
    intro s s' n edge a ha
    obtain ⟨t,run,r,env'⟩ := fragWithCallback_tick_ctx oracle table edge
      (fun q next pc op => ha.2.2.2 s 0 q next (.refl s) pc op) ha.1 ha.2.1 ha.2.2.1
    exact ⟨t,run,r,run.safe_end,env',permitted_tail ha.2.2.2 edge⟩
  obtain ⟨out,run,done⟩ := fragmentLoop_correct inv (2*p.states+29+factor)
    (fun _ _ ha => ha.2.1) (fun _ _ ha => ha.1.stateCode) restores one source halted init
  refine ⟨out,?_,done.1,done.2.2.1⟩
  rw [show 2*p.states+32+factor = 2*p.states+29+factor+3 by omega]
  exact run

/-- Full execution for an application whose environment is carried by the scalar bank and headers. -/
theorem fragWithCallback_run {p : BitProgram} {bo : WordOracle} {P : K → Prop}
    {ctx : Transcript → Memory K → Prop} {allowed : p.Config → Fin p.states → Prop}
    {callback : Fragment} {factor : Nat} (oracle : FragCallbackCorrect p bo P ctx allowed callback factor)
    (keeps : ∀ (h : Transcript) (m t : Memory K), t.data = m.data → StableHeaders m t → ctx h m → ctx h t)
    {c d : p.Config} {cost : Nat} (source : p.Run bo c cost d) (halted : d.pc = none)
    (permit : PermittedAsksFrom p bo allowed c) {m : Memory K}
    (rep : Rep p c m) (safe : Good P m) (env : ctx c.transcript m) :
    ∃ t, (fragController p callback).Run P m ((2*p.states+32+factor)*cost+2) t ∧
      Rep p d t ∧ ctx d.transcript t := by
  exact fragWithCallback_run_ctx oracle (tableKeeps_of_headers keeps)
    (fun h a env => keeps h a _ rfl (stable_limit _) env) source halted permit rep safe env

end Dispatch
end BitRAM
end LinearProgramming
end Optimization
end OAI
