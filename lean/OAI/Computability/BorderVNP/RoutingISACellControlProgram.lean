import OAI.Computability.BorderVNP.RoutingISACellControlEmit
import OAI.Computability.BorderVNP.RoutingISACellControlSetup
import OAI.Computability.BorderVNP.RoutingISATableEvents

/-! # Verified native pre-sidecar owned-cell header production -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellControlRows

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM TypedTaskBuilder
open private both emit_exact from OAI.Computability.BorderVNP.RoutingISACellControlEmit

private theorem updated (l : Layout) (i j k : ℕ) (z t : NatState) (old : l.Ready i j z)
    (keep : ∀ r : Reg, r.val < 20 → r ≠ 18 → r ≠ 19 → t.reg r=z.reg r)
    (ci : t.reg 18=i+1) (cj : t.reg 19=k) : l.Ready (i+1) k t := by
  intro r hr
  by_cases h : r=18
  · subst r; exact ci
  by_cases h' : r=19
  · subst r; exact cj
  rw [keep _ hr h h',old r hr]
  rcases r with ⟨r,rr⟩; change r < 20 at hr
  interval_cases r <;> first | rfl | contradiction

private theorem commit_effect (l : Layout) (mem : ℕ → ℕ) (pub : Arg → ℕ) (i w : ℕ)
    (z : NatState) (fit : l.Room w) (hi : i < l.cells) (h : l.Gathered mem i (l.before mem i) z)
    (hm : z.mem=l.image mem i) :
    commit.fixedSafe w pub z ∧ l.Ready (i+1) (l.before mem (i+1)) (commit.fixedEval pub z) ∧
      (commit.fixedEval pub z).mem=l.image mem (i+1) := by
  let j := l.before mem i
  have ji : j < l.cells := (l.before_le mem i).trans_lt hi
  have he := emit_exact l mem pub w i j z h ji fit
  let b : Code := .ifEq 21 5 emit .nop
  let v := b.fixedEval pub z
  have team : z.reg 5=l.team := h.ready 5 (by decide)
  have one : z.reg 1=1 := h.ready 1 (by decide)
  have idx : z.reg 18=i := h.ready 18 (by decide)
  have cur : z.reg 19=j := h.ready 19 (by decide)
  have ev : v=if l.owner mem i=l.team then both l mem i j z else z := by
    change (if z.reg 21=z.reg 5 then emit.fixedEval pub z else Code.nop.fixedEval pub z) = _
    rw [h.owner,team,he.2]
    rfl
  have sb : b.fixedSafe w pub z := by
    change (if z.reg 21=z.reg 5 then emit.fixedSafe w pub z else Code.nop.fixedSafe w pub z)
    split
    · exact he.1
    · trivial
  have same (r : Reg) (h19 : r ≠ 19) (h20 : r ≠ 20) : v.reg r=z.reg r := by
    rw [ev]; split <;> simp [both,h19,h20]
  have vx := (same 18 (by decide) (by decide)).trans idx
  have v1 := (same 1 (by decide) (by decide)).trans one
  have vj : v.reg 19=l.before mem (i+1) := by rw [ev,TypedTaskBuilder.Layout.before]; split <;> simp [both,cur,j]
  have vm : v.mem=l.image mem (i+1) := by rw [ev,Layout.image]; split <;> simp [both,hm,j]
  have s : commit.fixedSafe w pub z := by
    change b.fixedSafe w pub z ∧ v.reg 18 + v.reg 1 < 2^w
    refine ⟨sb,?_⟩; rw [vx,v1]; have := fit.result.1; omega
  have end' : commit.fixedEval pub z = ⟨Function.update v.reg 18 (i+1),v.mem⟩ := by
    change (Code.binary .add 18 18 1).fixedEval pub v=_
    simp only [Code.fixedEval,Code.evalNat,addressOp,vx,v1]
  rw [end']
  refine ⟨s,updated l i j _ z _ h.ready ?_ ?_ ?_,vm⟩
  · intro r hr h18 h19
    have h20 : r ≠ 20 := fun eq => by subst r; exact (by decide : ¬(20 : Reg).val < 20) hr
    exact (Function.update_of_ne h18 ..).trans (same r h19 h20)
  · change Function.update v.reg (18 : Reg) (i+1) 18=i+1
    simp
  · change Function.update v.reg (18 : Reg) (i+1) 19=l.before mem (i+1)
    rw [Function.update_of_ne (by decide : (19 : Reg) ≠ 18)]
    exact vj

private theorem body_run {w : ℕ} (l : Layout) (orig : ℕ → ℕ) (fit : l.Room w)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (i : ℕ) (hi : i < l.cells) (s : Bank w) (m : Memory w)
    (hr : l.Ready i (l.before orig i) (.ofWords s m)) (hm : readings m=l.image orig i) :
    BoundedRun pub mac body s m body.slots (fun z => l.Ready (i+1) (l.before orig (i+1)) z ∧ z.mem=l.image orig (i+1)) := by
  have read (a : ℕ) (ha : l.inputs i a) : readings m a=orig a := by
    rw [hm]
    exact image_outside l orig hi.le (fit.inputApart i hi a ha)
  apply (gather_run pub mac s m l orig fit i _ hi hr read).seq
  rintro u mu ⟨h,memory⟩
  have hh := commit_effect l orig (readings pub) i w (.ofWords u mu) fit hi h (memory.trans hm)
  exact (commit.runFixed pub mac u mu hh.1).mono le_rfl (fun out eq => eq ▸ hh.2)

private theorem finish_run {w : ℕ} (l : Layout) (orig : ℕ → ℕ) (fit : l.Room w)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (hp : (pub 0).val=l.frame) (s : Bank w) (m : Memory w)
    (r : l.Ready l.cells (l.before orig l.cells) (.ofWords s m)) (mem : readings m=l.image orig l.cells) :
    BoundedRun pub mac finish s m finish.slots (fun z => z.mem=l.published orig) := by
  have f : readings pub 0=l.frame := hp
  have n : readings s 19=l.before orig l.cells := r 19 (by decide)
  have hs : finish.fixedSafe w (readings pub) (.ofWords s m) := by
    simp (config := {decide:=true}) [finish,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,Code.evalNat,addressOpFits,f]
    have := fit.frame.1; omega
  apply (finish.runFixed pub mac s m hs).mono le_rfl
  rintro z rfl
  simp (config := {decide:=true}) [finish,Code.block,Code.fixedEval,Code.evalNat,addressOp,NatState.ofWords,f,n,mem,Layout.published]

/-- Real unsigned word-RAM execution producing both compact owned-cell tables and
their shared true count, before any private sidecar is parsed. -/
theorem program_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (l : Layout) (hp : (pub 0).val=l.frame) (fields : l.Fields (readings m)) (fit : l.Room w) :
    BoundedRun pub mac program s m (setup.slots+l.cells*(body.slots+1)+1+finish.slots)
      (fun z => z.mem=l.published (readings m)) := by
  let orig := readings m
  let P := fun i (z : NatState) => l.Ready i (l.before orig i) z ∧ z.mem=l.image orig i
  have first := (setup_run pub mac s m l hp fields fit).mono le_rfl (Q := P 0) (fun _ h => h)
  have loop (u : Bank w) (mu : Memory w) (start : P 0 (.ofWords u mu)) :
      BoundedRun pub mac (.whileLt 18 6 body) u mu (l.cells*(body.slots+1)+1) (P l.cells) := by
    apply run_counted_loop pub mac 18 6 body l.cells body.slots P _ _ 0 (Nat.zero_le _) u mu start
    · intro i z h; exact ⟨h.1 18 (by decide),h.1 6 (by decide)⟩
    · intro i hi z mz h; exact body_run l orig fit pub mac i hi z mz h.1 h.2
  have tail (u : Bank w) (mu : Memory w) (start : P 0 (.ofWords u mu)) :
      BoundedRun pub mac (.seq (.whileLt 18 6 body) finish) u mu (l.cells*(body.slots+1)+1+finish.slots)
        (fun z => z.mem=l.published orig) :=
    (loop u mu start).seq (fun v mv h => finish_run l orig fit pub mac hp v mv h.1 h.2)
  exact (first.seq tail).mono (by omega) (fun _ h => h)

/-- The native pre-sidecar producer has one positive execution and consumes no private
choice bits. Both compact output tables are determined by the live shared memory. -/
theorem native_program {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (l : Layout) (hp : (pub 0).val=l.frame) (fields : l.Fields (readings m)) (fit : l.Room w) :
    ∃ es t mt, Runs pub mac program s m es t mt ∧ readings mt=l.published (readings m) ∧
      traceCost es ≤ setup.slots+l.cells*(body.slots+1)+1+finish.slots ∧
      (∀ e ∈ es, e.choices=[] ∧ e.sign=.plus) ∧
      (∀ bits fs, TeamRAM.execute (program.program.fetch pub mac) ⟨0,s⟩ m bits = some fs ↔
        fs=es ∧ bits=es.map TeamRAM.Event.choices) := by
  obtain ⟨es,t,mt,run,cost,output⟩ := program_run pub mac s m l hp fields fit
  refine ⟨es,t,mt,run,output,cost,run.unsigned_events (by decide),?_⟩
  intro bits fs
  rw [Code.execute_iff_runs (by decide : program.withoutAccept=true)]
  constructor
  · rintro ⟨⟨u,mu,r⟩,hbits⟩
    obtain ⟨rfl,_,_⟩ := r.unique_of_deterministic (by decide) run
    exact ⟨rfl,hbits.symm⟩
  · rintro ⟨rfl,rfl⟩
    exact ⟨⟨t,mt,run⟩,rfl⟩

end RoutingISA.CellControlRows

end BorderVNP
end Computability
end OAI
