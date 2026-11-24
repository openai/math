import OAI.Computability.VPVNP.PrimedInputRAMFlowEval

/-!
# Recovering structured traces from successful native execution

Every successful run of a linked block has a finite structured execution. The exit
receives exactly the unused fuel and branch suffix. In a standalone template the exit
is a single return instruction, so the recovered trace contains the entire event log.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM.Flow

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {w r k p : ℕ}

/-- Successful execution separates into a structured trace and its continuation. -/
def Exits (M : Machine w p r k) (state : Word w) (priv : Word w → Word w) (stop : Fin p)
    (a : PrimedInputRAM.Flow r k) (rs : Regs w r) (m : Memory w) (fuel : ℕ) (bits : List Bool)
    (out : Report w) : Prop :=
  ∃ es rs' m' left bs tail,
    Exec M.publicData state a rs m es rs' m' ∧ fuel = es.length + left ∧ bits = choiceBits es ++ bs ∧
    execute M.program left ⟨stop, state, rs', priv⟩ m' bs = some tail ∧ out = prependEvents es tail

private theorem positive {pub : Fin k → Word w} {state : Word w} {a : PrimedInputRAM.Flow r k} {rs m es rs' m'}
    (h : Exec pub state a rs m es rs' m') : 0 < es.length := by
  induction h <;> simp_all
  omega

private theorem exits_prepend {M : Machine w p r k} {state : Word w} {priv stop a b rs m fuel bits out}
    {e : Event w} (h : Exits M state priv stop b rs m fuel bits out)
    (lift : ∀ {es rs' m'}, Exec M.publicData state b rs m es rs' m' →
      Exec M.publicData state a rs m (e :: es) rs' m') :
    Exits M state priv stop a rs m (fuel+1) (choiceBits [e] ++ bits) (out.prepend e) := by
  obtain ⟨es, rs', m', left, bs, tail, hE, rfl, rfl, hrun, rfl⟩ := h
  refine ⟨e :: es, rs', m', left, bs, tail, lift hE, by simp; omega, ?_, hrun, rfl⟩
  cases e <;> simp [choiceBits]

private theorem exits_seq {M : Machine w p r k} {state : Word w} {priv stop a b rs m es r₁ m₁ fuel bits out}
    (first : Exec M.publicData state a rs m es r₁ m₁) (last : Exits M state priv stop b r₁ m₁ fuel bits out) :
    Exits M state priv stop (.seq a b) rs m (es.length+fuel) (choiceBits es ++ bits) (prependEvents es out) := by
  obtain ⟨fs, r₂, m₂, left, bs, tail, hE, rfl, rfl, hrun, rfl⟩ := last
  refine ⟨es ++ fs, r₂, m₂, left, bs, tail, .seq first hE, by simp [Nat.add_assoc],
    by simp [choiceBits_append], hrun, ?_⟩
  simp [prependEvents, List.append_assoc]

private theorem exits_loop {M : Machine w p r k} {state : Word w} {priv stop l q a rs m es r₁ m₁ fuel bits out}
    (ht : rs l < rs q) (first : Exec M.publicData state a rs m es r₁ m₁)
    (last : Exits M state priv stop (.whileLt l q a) r₁ m₁ fuel bits out) :
    Exits M state priv stop (.whileLt l q a) rs m (es.length+fuel+1) (choiceBits es ++ bits)
      ((prependEvents es out).prepend .tick) := by
  obtain ⟨fs, r₂, m₂, left, bs, tail, hE, rfl, rfl, hrun, rfl⟩ := last
  refine ⟨.tick :: (es ++ fs), r₂, m₂, left, bs, tail, .whileStep ht first hE, by simp; omega,
    by simp [choiceBits, choiceBits_append], hrun, ?_⟩
  simp [Report.prepend, prependEvents, List.append_assoc]

/-- Recover the structured execution from any successful entry, before the normal exit's
continuation. This applies to arbitrary linked code, even when the enclosing program has
further branches after the block. -/
theorem Linked.complete {M : Machine w p r k} {a : PrimedInputRAM.Flow r k}
    {label : a.Label → Fin p} {stop bad : Fin p} (hl : Linked M a label stop bad)
    (hb : M.code bad = .reject) (state : Word w) (priv : Word w → Word w)
    (rs : Regs w r) (m : Memory w) (fuel : ℕ) (bits : List Bool) (out : Report w)
    (h : BurstRAM.execute M.program fuel ⟨label a.entry,state,rs,priv⟩ m bits = some out) :
    Exits M state priv stop a rs m fuel bits out := by
  induction fuel using Nat.strong_induction_on generalizing a stop rs m bits out with
  | h fuel ih =>
    induction a generalizing stop rs m bits out with
    | line op =>
      cases fuel with
      | zero => contradiction
      | succ f =>
        rw [hl.execute hb state priv (f+1) _ _ _ _] at h
        simp only [run, code, Jump.run] at h
        cases he : op.effect M.publicData state rs m with
        | none => simp [he] at h
        | some z =>
          obtain ⟨e, r', m'⟩ := z
          simp only [he, Option.bind_some, Option.map_eq_some_iff] at h
          obtain ⟨t, hrun, rfl⟩ := h
          exact ⟨[e], r', m', f, bits, t, .line he, by simp [Nat.add_comm],
            by rw [line_choices he]; rfl, hrun, rfl⟩
    | seq a b ia _ =>
      obtain ⟨es, r₁, m₁, left, bs, t, he, hf, hbs, ht, hout⟩ := ia hl.seqLeft _ _ _ _ h
      have hlt : left < fuel := by have := positive he; omega
      have hr := ih left hlt hl.seqRight r₁ m₁ bs t ht
      rw [hf, hbs, hout]
      exact exits_seq he hr
    | ifEq l q a b ia ib | ifLt l q a b ia ib =>
      cases fuel with
      | zero => contradiction
      | succ f =>
        first | erw [hl.execute_ifEq state priv f rs m bits] at h
              | erw [hl.execute_ifLt state priv f rs m bits] at h
        obtain ⟨t, hrun, rfl⟩ := Option.map_eq_some_iff.mp h
        split at hrun
        · rename_i ht
          first | exact exits_prepend (ih f (by omega) hl.ifEqYes _ _ _ _ hrun) (Exec.ifEqYes ht)
                | exact exits_prepend (ih f (by omega) hl.ifLtYes _ _ _ _ hrun) (Exec.ifLtYes ht)
        · rename_i ht
          first | exact exits_prepend (ih f (by omega) hl.ifEqNo _ _ _ _ hrun) (Exec.ifEqNo ht)
                | exact exits_prepend (ih f (by omega) hl.ifLtNo _ _ _ _ hrun) (Exec.ifLtNo ht)
    | branch a b _ _ =>
      cases fuel with
      | zero => contradiction
      | succ f =>
        cases bits with
        | nil => erw [hl.execute_branch_nil state priv f rs m] at h; contradiction
        | cons bit bs =>
          erw [hl.execute_branch state priv f rs m bit bs] at h
          obtain ⟨t, hrun, rfl⟩ := Option.map_eq_some_iff.mp h
          cases bit with
          | true => exact exits_prepend (ih f (by omega) hl.branchYes _ _ _ _ hrun) Exec.branchYes
          | false => exact exits_prepend (ih f (by omega) hl.branchNo _ _ _ _ hrun) Exec.branchNo
    | whileLt l q a _ =>
      cases fuel with
      | zero => contradiction
      | succ f =>
        erw [hl.execute_whileLt state priv f rs m bits] at h
        obtain ⟨t, hrun, rfl⟩ := Option.map_eq_some_iff.mp h
        split at hrun
        · rename_i ht
          obtain ⟨es, r₁, m₁, left, bs, u, hE, hf, hbs, hu, hout⟩ := ih f (by omega) hl.loopBody _ _ _ _ hrun
          have hlt : left < f+1 := by omega
          have hr := ih left hlt hl r₁ m₁ bs u hu
          rw [hf, hbs, hout]
          exact exits_loop ht hE hr
        · rename_i ht
          exact ⟨[.tick], rs, m, f, bits, t, .whileDone ht, by simp [Nat.add_comm], rfl, hrun, rfl⟩

private theorem template_exit_run (a : PrimedInputRAM.Flow r k) (result : Option (Fin r))
    (pub : Fin k → Word w) (state : Word w) (priv : Word w → Word w) (rs : Regs w r) (m : Memory w)
    (fuel : ℕ) (bits : List Bool) :
    execute ((a.template result).instantiate w pub).program fuel ⟨a.exitPC,state,rs,priv⟩ m bits =
      if fuel = 0 ∨ bits ≠ [] then none else some ⟨[], result.map rs⟩ := by
  cases fuel with
  | zero => simp [execute]
  | succ n =>
    cases result <;> cases bits <;>
      simp [execute, Machine.program, Template.instantiate, template_exit, Instr.resize, Instr.run]

/-- A standalone compiled template accepts exactly its finite `Exec` derivations with
all bits consumed, sufficient fuel for the return, and the indicated returned register.
With `result = none` the exit is an accepting halt. -/
theorem template_execute_iff (a : PrimedInputRAM.Flow r k) (result : Option (Fin r))
    (pub : Fin k → Word w) (state : Word w) (priv : Word w → Word w) (rs : Regs w r) (m : Memory w)
    (fuel : ℕ) (bits : List Bool) (out : Report w) :
    execute ((a.template result).instantiate w pub).program fuel ⟨a.pc a.entry,state,rs,priv⟩ m bits =
        some out ↔
      ∃ rs' m', Exec pub state a rs m out.events rs' m' ∧ out.result = result.map rs' ∧
        out.events.length < fuel ∧ choiceBits out.events = bits := by
  have hl := template_linked a result pub
  have hb : ((a.template result).instantiate w pub).code a.rejectPC = .reject := by
    simp [Template.instantiate, template_reject, Instr.resize]
  constructor
  · intro h
    obtain ⟨es, r₁, m₁, left, bs, tail, he, hf, hbs, ht, hout⟩ :=
      hl.complete hb state priv rs m fuel bits out h
    rw [template_exit_run] at ht
    split at ht
    · contradiction
    · rename_i hremaining
      obtain ⟨hleft, rfl⟩ := (not_or.mp hremaining).imp_right (fun h ↦ by simpa using h)
      obtain rfl := Option.some.inj ht
      subst out
      simp only [prependEvents, List.append_nil]
      exact ⟨r₁, m₁, he, rfl, by omega, by simpa using hbs.symm⟩
  · rintro ⟨r₁, m₁, he, hr, hlen, hbits⟩
    let left := fuel - out.events.length
    have hp : 0 < left := Nat.sub_pos_of_lt hlen
    calc
      _ = execute ((a.template result).instantiate w pub).program (out.events.length + left)
          ⟨a.pc a.entry,state,rs,priv⟩ m (choiceBits out.events ++ []) := by
        simp [left, Nat.add_sub_of_le hlen.le, hbits]
      _ = _ := he.execute hl hb priv left []
      _ = some out := by
        rw [template_exit_run, ite_eq_right (by simp [hp.ne']), Option.map_some]
        cases out
        simp_all [prependEvents]

end PrimedInputRAM.Flow

end VPVNP
end Computability
end OAI
