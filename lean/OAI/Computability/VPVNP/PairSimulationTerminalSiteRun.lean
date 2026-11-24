import OAI.Computability.VPVNP.PairSimulationTerminalSiteStart
import OAI.Computability.VPVNP.PairSimulationDFSDecode

/-! # Exact traces and private stack for the terminal-site guard -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalSiteStart

open BurstRAM PrivateRAM
open scoped Fin.CommRing
open private guessed_addFuel from OAI.Computability.VPVNP.PairSimulationDFSDecode
open private field from OAI.Computability.VPVNP.PairSimulationTerminalSiteStart

variable {w p r k : ℕ}

private theorem pre_eval (pub : Fin 11 → Word w) (st : Word w) (m : Memory w)
    (b : Reg → Word w) (priv : Word w → Word w) :
    let h := headerWord pub
    let v := eval pub st m pre b priv
    v.1 = guardTrace m h ∧ GuardReady h st m v.2.1 ∧ v.2.2 = priv := by
  refine ⟨?_, ⟨?_,?_,?_,?_⟩,?_⟩ <;> rfl

private theorem boot_eval (pub : Fin 11 → Word w) (st h : Word w) (m : Memory w)
    (b : Reg → Word w) (priv : Word w → Word w) (g : GuardReady h st m b) :
    let v := eval pub st m boot b priv
    v.1 = bootTrace m h ∧ BootReady (pub 6) h st m v.2.1 ∧
      v.2.2 = Function.update priv (pub 6-1) (m (h+6).val + m (h+15).val * st) := by
  dsimp only
  refine ⟨?_, ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩, ?_⟩ <;>
    simp [boot,field,eval,bootTrace,fieldTrace,BinaryOp.eval,
      g.header,g.ordinal,g.sites,g.one]

variable {M : Machine w p r k} {pc : Stage → Fin p} {reg : Reg ↪ Fin r} {pub : Fin 11 → Fin k}
variable {geometry : Fin p}

/-- A deterministic prefix has the indicated exact trace for every subsequent
fuel and choice suffix. Its external memory is available to the continuation. -/
def Continues (M : Machine w p r k) (m : Memory w) (c out : Config w p r) (es : List (Event w)) :=
  ∀ fuel bs, execute M.program (fuel+es.length) c m bs =
    (execute M.program fuel out m bs).map (fun rep => ⟨es ++ rep.events, rep.result⟩)

private theorem continues_tick {m : Memory w} {c out : Config w p r}
    (s : M.program.step c = .localStep out) : Continues M m c out [.tick] := by
  intro fuel bs
  change execute M.program (fuel+1) c m bs = _
  rw [execute,s]
  rfl

private theorem continues_trans {m : Memory w} {a b c : Config w p r} {es fs : List (Event w)}
    (he : Continues M m a b es) (hf : Continues M m b c fs) : Continues M m a c (es++fs) := by
  intro fuel bs
  rw [List.length_append,show fuel+(es.length+fs.length) = (fuel+fs.length)+es.length by omega,
    he _ _,hf _ _]
  simp [Option.map_map,Function.comp_def,List.append_assoc]

private theorem target_castSucc {n : ℕ} (label : Fin n → Fin p) (done : Fin p) (i : Fin n) :
    target label done i.castSucc = label i := by simp [target,i.isLt]

private theorem target_last {n : ℕ} (label : Fin n → Fin p) (done : Fin p) :
    target label done (Fin.last n) = done := by simp [target]

private theorem pre_run (link : StartLinked M pc reg pub geometry) (m : Memory w) (c : Config w p r)
    (hc : c.pc = pc entry) :
    let h := headerWord (M.publicData ∘ pub)
    ∃ out, out.pc = pc .equal ∧ out.persistent = c.persistent ∧ GuardReady h c.persistent m (out.reg ∘ reg) ∧
      out.privateMem = c.privateMem ∧ Continues M m c out (guardTrace m h) := by
  let atPc := target (pc ∘ Stage.pre) (pc .equal)
  have rows (i : Fin pre.length) : M.code (atPc i.castSucc) = Line.emit reg pub (atPc i.succ) pre[i] := by
    rw [show atPc i.castSucc = pc (.pre i) from target_castSucc .., link _ rfl]
    rfl
  obtain ⟨out, hp, hs, hr, hm, he⟩ := linear_run M reg pub m pre atPc rows c (by exact hc)
  have ⟨et, ready, priv⟩ := pre_eval (M.publicData ∘ pub) c.persistent m (c.reg ∘ reg) c.privateMem
  rw [et] at he
  exact ⟨out,hp.trans (target_last ..),hs,hr.symm ▸ ready,hm.trans priv,he⟩

private theorem boot_run (link : StartLinked M pc reg pub geometry) (m : Memory w) (c : Config w p r)
    (hc : c.pc = pc (.boot 0)) (h : Word w) (g : GuardReady h c.persistent m (c.reg ∘ reg)) :
    let n := M.publicData (pub 6)
    ∃ out, out.pc = geometry ∧ out.persistent = c.persistent ∧ BootReady n h c.persistent m (out.reg ∘ reg) ∧
      out.privateMem = Function.update c.privateMem (n-1) (m (h+6).val + m (h+15).val * c.persistent) ∧
      Continues M m c out (bootTrace m h) := by
  let atPc := target (pc ∘ Stage.boot) geometry
  have rows (i : Fin boot.length) : M.code (atPc i.castSucc) = Line.emit reg pub (atPc i.succ) boot[i] := by
    rw [show atPc i.castSucc = pc (.boot i) from target_castSucc .., link _ rfl]
    rfl
  obtain ⟨out, hp, hs, hr, hm, he⟩ := linear_run M reg pub m boot atPc rows c (by exact hc)
  have ⟨et,ready,priv⟩ := boot_eval (M.publicData ∘ pub) c.persistent h m (c.reg ∘ reg) c.privateMem g
  rw [et] at he
  exact ⟨out,hp.trans (target_last ..),hs,hr.symm ▸ ready,hm.trans priv,he⟩

private theorem step_at (link : StartLinked M pc reg pub geometry) (j : Stage) (hj : j.bootstrap = true) (c : Config w p r)
    (hc : c.pc = pc j) : M.program.step c = (instruction pc reg pub geometry j).run M.publicData c := by
  simp only [Machine.program,hc,link j hj]

/-- An active site supplies its exact root and both endpoint arrays to the geometry initializer. -/
theorem active_run (link : StartLinked M pc reg pub geometry) (m : Memory w) (c : Config w p r)
    (hc : c.pc = pc entry) (ha : c.persistent < m (headerWord (M.publicData ∘ pub)+7).val) :
    let h := headerWord (M.publicData ∘ pub)
    let n := M.publicData (pub 6)
    ∃ out, out.pc = geometry ∧ out.persistent = c.persistent ∧ BootReady n h c.persistent m (out.reg ∘ reg) ∧
      out.privateMem = Function.update c.privateMem (n-1) (m (h+6).val + m (h+15).val * c.persistent) ∧
      Continues M m c out (guardTrace m h ++ [.tick,.tick] ++ bootTrace m h) := by
  let h := headerWord (M.publicData ∘ pub)
  obtain ⟨a,hp,hs,g,hm,he⟩ := pre_run link m c hc
  have ho : a.reg (reg (saved 2)) = c.persistent := g.ordinal
  have hf : a.reg (reg (saved 5)) = m (h+7).val := g.sites
  let b := {a with pc := pc .less}
  let d := {a with pc := pc (.boot 0)}
  have s₁ : M.program.step a = .localStep b := by
    rw [step_at link .equal rfl _ hp]; simp [instruction,Instr.run,ho,hf,ne_of_lt ha,b,h]
  have s₂ : M.program.step b = .localStep d := by
    rw [step_at link .less rfl _ rfl]; simp [instruction,Instr.run,b,d,ho,hf,ha,h]
  have hd : GuardReady h d.persistent m (d.reg ∘ reg) := hs.symm ▸ g
  obtain ⟨out,hpc,hper,ready,hpriv,hboot⟩ := boot_run link m d rfl h hd
  have run := continues_trans (continues_trans he (continues_trans (continues_tick s₁) (continues_tick s₂))) hboot
  refine ⟨out,hpc,hper.trans hs,?_,?_,run⟩
  · simpa only [d,hs,h] using ready
  · simpa only [d,hm,hs,h] using hpriv

/-- Reaching the terminal ordinal accepts on the next test, consuming no choices. -/
theorem equal_run (link : StartLinked M pc reg pub geometry) (m : Memory w) (c : Config w p r)
    (hc : c.pc = pc entry) (ha : c.persistent = m (headerWord (M.publicData ∘ pub)+7).val)
    (fuel : ℕ) (bs : List Bool) :
    let h := headerWord (M.publicData ∘ pub)
    execute M.program (fuel+15) c m bs = if bs = [] then some ⟨guardTrace m h ++ [.tick],none⟩ else none := by
  obtain ⟨a,hp,_,g,_,he⟩ := pre_run link m c hc
  let d := {a with pc := pc .accept}
  have eq : a.reg (reg (saved 2)) = a.reg (reg (saved 5)) := g.ordinal.trans (ha.trans g.sites.symm)
  have s : M.program.step a = .localStep d := by
    rw [step_at link .equal rfl _ hp]; simp [instruction,Instr.run,eq,d]
  have fin : M.program.step d = .finish none := step_at link .accept rfl _ rfl
  change execute M.program ((fuel+2)+(guardTrace m (headerWord (M.publicData ∘ pub))).length) c m bs = _
  rw [he (fuel.succ.succ) bs]
  simp only [execute,s,fin]
  split <;> rfl

/-- An ordinal past the last site takes the rejecting branch. -/
theorem late_run (link : StartLinked M pc reg pub geometry) (m : Memory w) (c : Config w p r)
    (hc : c.pc = pc entry) (ha : m (headerWord (M.publicData ∘ pub)+7).val < c.persistent)
    (fuel : ℕ) (bs : List Bool) : execute M.program (fuel+16) c m bs = none := by
  obtain ⟨a,hp,_,g,_,he⟩ := pre_run link m c hc
  have lt : a.reg (reg (saved 5)) < a.reg (reg (saved 2)) := by
    change (a.reg ∘ reg) (saved 5) < (a.reg ∘ reg) (saved 2)
    rwa [g.sites,g.ordinal]
  let b := {a with pc := pc .less}
  let d := {a with pc := pc .reject}
  have s : M.program.step a = .localStep b := by
    rw [step_at link .equal rfl _ hp]; simp [instruction,Instr.run,ne_of_gt lt,b]
  have s' : M.program.step b = .localStep d := by
    rw [step_at link .less rfl _ rfl]; simp [instruction,Instr.run,b,d,not_lt_of_gt lt]
  have fin : M.program.step d = .reject := step_at link .reject rfl _ rfl
  change execute M.program ((fuel+3)+(guardTrace m (headerWord (M.publicData ∘ pub))).length) c m bs = none
  rw [he (fuel.succ.succ.succ) bs]
  simp only [execute,s,s',fin,Option.map_none]

/-- Sufficient fuel cannot turn a malformed ordinal into a returning path. -/
theorem late_reject (link : StartLinked M pc reg pub geometry) (m : Memory w) (c : Config w p r)
    (hc : c.pc = pc entry) (ha : m (headerWord (M.publicData ∘ pub)+7).val < c.persistent)
    (bs : List Bool) : ¬ DFS.Returns M c m bs := by
  rintro ⟨f,rep,he⟩
  obtain ⟨hg,hmem,hbits⟩ := execute_iff.mp he
  have big := execute_iff.mpr ⟨guessed_addFuel hg 16,hmem,hbits⟩
  rw [Nat.add_comm 16 f,late_run link m c hc ha] at big
  contradiction

/-- The terminal ordinal has exactly its empty-choice accepting path. -/
theorem equal_terminal (link : StartLinked M pc reg pub geometry) (m : Memory w) (c : Config w p r)
    (hc : c.pc = pc entry) (ha : c.persistent = m (headerWord (M.publicData ∘ pub)+7).val)
    (bs : List Bool) : DFS.Returns M c m bs ↔ bs = [] := by
  constructor
  · rintro ⟨f,rep,he⟩
    obtain ⟨hg,hmem,hbits⟩ := execute_iff.mp he
    have big := execute_iff.mpr ⟨guessed_addFuel hg 15,hmem,hbits⟩
    rw [Nat.add_comm 15 f,equal_run link m c hc ha] at big
    split at big <;> simp_all
  · rintro rfl
    exact ⟨15, _, by simpa using equal_run link m c hc ha 0 []⟩

private theorem finish_step (link : FinishLinked M pc reg pub geometry) (j : Stage) (hj : j.bootstrap = false)
    (c : Config w p r) (hc : c.pc = pc j) : M.program.step c = (instruction pc reg pub geometry j).run M.publicData c :=
  by simp only [Machine.program,hc,link j hj]

/-- After the histogram flush, read the original ordinal afresh and return
its successor. All four rows work with arbitrary registers and private cells. -/
theorem finish_run (link : FinishLinked M pc reg pub geometry) (m : Memory w) (c : Config w p r)
    (hc : c.pc = pc .increment) (fuel : ℕ) (bs : List Bool) :
    execute M.program fuel c m bs = if 4 ≤ fuel ∧ bs = [] then
      some ⟨[.tick,.tick,.tick],some (c.persistent+1)⟩ else none := by
  let a := c.put (pc .unit) (reg (saved 2)) c.persistent
  let b := a.put (pc .add) (reg (work 0)) 1
  let d := b.put (pc .finish) (reg (saved 2)) (c.persistent+1)
  have hs : M.program.step c = .localStep a := finish_step link .increment rfl _ hc
  have hs' : M.program.step a = .localStep b := finish_step link .unit rfl _ rfl
  have hs'' : M.program.step b = .localStep d := by
    rw [finish_step link .add rfl _ rfl]; simp [instruction,Instr.run,BinaryOp.eval,d,b,a,Config.put]
  have hfin : M.program.step d = .finish (some (c.persistent+1)) := by
    rw [finish_step link .finish rfl _ rfl]; simp [instruction,Instr.run,d]
  rcases fuel with _|(_|(_|(_|f))) <;>
    simp only [execute,hs,hs',hs'',hfin,Option.map_none] <;>
    first | rfl | (simp [show 4 ≤ f+1+1+1+1 by omega]; split <;> rfl)

theorem finish_terminal (link : FinishLinked M pc reg pub geometry) (m : Memory w) (c : Config w p r)
    (hc : c.pc = pc .increment) (bs : List Bool) : DFS.Returns M c m bs ↔ bs = [] := by
  constructor
  · rintro ⟨f,rep,hr⟩
    rw [finish_run link m c hc] at hr
    split at hr <;> simp_all
  · rintro rfl
    exact ⟨4, _, by simpa using finish_run link m c hc 4 []⟩

/-- The entry trace and continuation trace have fixed local and external costs. -/
theorem active_caps (m : Memory w) (h : Word w) :
    let es := guardTrace m h ++ [.tick,.tick] ++ bootTrace m h
    es.length = 44 ∧ countProbes es = 9 ∧ choiceBits es = [] := by
  exact ⟨rfl,rfl,rfl⟩

/-- A fresh burst starts with zero private cells. At geometry entry its one
pending descriptor is the root and all other cells still have value zero. -/
theorem fresh_stack (link : StartLinked M pc reg pub geometry) (m : Memory w) (st : Word w)
    (hc : M.entry = pc entry) (ha : st < m (headerWord (M.publicData ∘ pub)+7).val)
    (n : ℕ) (hn : M.publicData (pub 6) = (n : Word w)) (npos : 0 < n) (nfit : n < 2^w) :
    let h := headerWord (M.publicData ∘ pub)
    let root := m (h+6).val + m (h+15).val * st
    ∃ out, out.pc = geometry ∧ out.persistent = st ∧ BootReady (n : Word w) h st m (out.reg ∘ reg) ∧
      DFS.Represents out.privateMem (n-1) [root] ∧ out.privateMem = Function.update (fun _ => 0) ((n-1 : ℕ) : Word w) root ∧
      Continues M m (M.program.start st) out (guardTrace m h ++ [.tick,.tick] ++ bootTrace m h) := by
  obtain ⟨out,hp,hs,ready,hm,hr⟩ := active_run link m (M.program.start st) hc ha
  have sub : (n : Word w) - 1 = ((n-1 : ℕ) : Word w) := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp
  rw [hn,sub] at hm
  refine ⟨out,hp,hs,hn ▸ ready,⟨by simp; omega,?_⟩,hm,hr⟩
  intro i
  have hz : i.val = 0 := by have hi : i.val < 1 := i.isLt; omega
  have hi : i = 0 := Fin.ext hz
  subst i
  simp [hm, Machine.program]

end PairSimulation.TerminalSiteStart

end VPVNP
end Computability
end OAI
