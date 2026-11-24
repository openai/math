import OAI.Computability.VPVNP.PairSimulationStackMemory

/-! # Native realization of each elementary bit-stack instruction -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.StackMachine

open RAMTape BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {K Q : Type} {w p r k : ℕ}
  {M : Machine w p r k} {code : StackCode K Q} {pc : Q → Fin 7 → Fin p}
  {reg : Register K ↪ Fin r} {done : Fin p} (linked : Linked M code pc reg done)

/-- Frame condition across a native stack step, preserving the persistent state, registers
outside the stack bank, and private cells outside all stack intervals. -/
structure Frame (L : Layout K w) (reg : Register K ↪ Fin r) (c d : Config w p r) : Prop where
  persistent : d.persistent = c.persistent
  regs : ∀ i, i ∉ Set.range reg → d.reg i = c.reg i
  memory : ∀ a, (∀ j, a.val < L.base j ∨ L.base j+L.capacity ≤ a.val) → d.privateMem a = c.privateMem a

theorem Frame.trans {L : Layout K w} {c d e : Config w p r} (h : Frame L reg c d) (g : Frame L reg d e) :
    Frame L reg c e :=
  ⟨g.persistent.trans h.persistent,fun i hi => (g.regs i hi).trans (h.regs i hi),
    fun a ha => (g.memory a ha).trans (h.memory a ha)⟩

theorem Frame.refl (L : Layout K w) (c : Config w p r) : Frame L reg c c :=
  ⟨rfl,fun _ _ => rfl,fun _ _ => rfl⟩

private theorem pass_step {c : Config w p r} {next : Fin p}
    (hs : M.code c.pc = .copy (reg .tmp) (reg .tmp) next) :
    M.program.step c = .localStep {c with pc := next} := by
  simp [Machine.program,hs,Instr.run,Config.put,Function.update_eq_self]

variable [DecidableEq K] {L : Layout K w} {q : Q} {c : Config w p r} {s : Stacks K}

include linked

theorem push_prefix_memory {a : K} {bit : Bool} {next : Q} (hop : code q = .push a bit next)
    (atPC : c.pc = pc q 0) (rep : Represents L reg c s) (fit : ∀ j, (s j).length ≤ L.capacity)
    (space : (s a).length < L.capacity) :
    ∃ d, Prefix M c (List.replicate 4 .tick) d ∧ d.pc = pc next 0 ∧
      Represents L reg d (Function.update s a (bit :: s a)) ∧ d.privateMem = Function.update c.privateMem (L.address a (s a).length) (encodeBit w bit) ∧ Frame L reg c d := by
  let b := encodeBit w bit
  let ptr := L.address a (s a).length
  let c₁ := c.put (pc q 1) (reg .tmp) b
  let c₂ := c₁.store (pc q 2) ptr b
  let c₃ := c₂.put (pc q 3) (reg (.top a)) (ptr+1)
  let d := {c₃ with pc := pc next 0}
  have st₀ : M.program.step c = .localStep c₁ := by rw [linked.step c q 0 atPC]; simp [instruction,hop,Instr.run,c₁,b,encodeBit]
  have st₁ : M.program.step c₁ = .localStep c₂ := by
    rw [linked.step c₁ q 1 rfl]
    simp [instruction,hop,Instr.run,c₂,c₁,ptr,Config.put,rep.tops]
  have st₂ : M.program.step c₂ = .localStep c₃ := by
    rw [linked.step c₂ q 2 rfl]
    simp [instruction,hop,Instr.run,c₃,c₂,c₁,ptr,Config.put,Config.store,rep.unit,rep.tops,BinaryOp.eval]
  have st₃ : M.program.step c₃ = .localStep d := by
    apply pass_step (reg := reg)
    change M.code (pc q 3) = _
    rw [linked q 3]; simp [instruction,hop]
  refine ⟨d,.tick st₀ (.tick st₁ (.tick st₂ (.tick st₃ (.nil _)))),rfl,?_,rfl,?_⟩
  · refine ⟨?_,?_,?_,?_,L.contents_push c.privateMem s a bit rep.cells fit space⟩
    · simp [d,c₃,c₂,c₁,Config.put,Config.store,rep.unit]
    · simp [d,c₃,c₂,c₁,Config.put,Config.store,rep.zero]
    · intro j; simp [d,c₃,c₂,c₁,Config.put,Config.store,rep.bases]
    · intro j
      by_cases h : j = a
      · subst j; simp [d,c₃,c₂,c₁,ptr,Config.put,Config.store,Layout.address,add_assoc]
      · simp [d,c₃,c₂,c₁,Config.put,Config.store,h,rep.tops]
  · refine ⟨rfl,?_,?_⟩
    · intro i hi
      have ne (j : Register K) : i ≠ reg j := fun e => hi ⟨j,e.symm⟩
      simp [d,c₃,c₂,c₁,Config.put,Config.store,Function.update_of_ne (ne _)]
    · intro i hi
      have ne : i ≠ ptr := by
        intro e
        have hev := congrArg Fin.val e
        rw [show ptr = L.address a (s a).length from rfl,L.address_val a space.le] at hev
        rcases hi a with hlo | hhi <;> omega
      simp [d,c₃,c₂,c₁,Config.put,Config.store,Function.update_of_ne ne]

theorem push_prefix {a : K} {bit : Bool} {next : Q} (hop : code q = .push a bit next)
    (atPC : c.pc = pc q 0) (rep : Represents L reg c s) (fit : ∀ j, (s j).length ≤ L.capacity)
    (space : (s a).length < L.capacity) :
    ∃ d, Prefix M c (List.replicate 4 .tick) d ∧ d.pc = pc next 0 ∧
      Represents L reg d (Function.update s a (bit :: s a)) ∧ Frame L reg c d := by
  obtain ⟨d,run,dst,repr,_,frame⟩ := push_prefix_memory linked hop atPC rep fit space
  exact ⟨d,run,dst,repr,frame⟩

theorem pop_prefix_memory {a : K} {next : Option Bool → Q} (hop : code q = .pop a next)
    (atPC : c.pc = pc q 0) (rep : Represents L reg c s) (hw : 0 < w) (fit : (s a).length ≤ L.capacity) :
    ∃ d, Prefix M c (List.replicate 4 .tick) d ∧ d.pc = pc (next (s a).head?) 0 ∧
      Represents L reg d (Function.update s a (s a).tail) ∧ d.privateMem = c.privateMem ∧ Frame L reg c d := by
  cases eq : s a with
  | nil =>
    let pos (i : Fin 7) := {c with pc := pc q i}
    let d := {c with pc := pc (next none) 0}
    have st₀ : M.program.step c = .localStep (pos 4) := by
      rw [linked.step c q 0 atPC]
      simp [instruction,hop,Instr.run,rep.tops,rep.bases,eq,pos]
    have st₄ : M.program.step (pos 4) = .localStep (pos 5) := by
      apply pass_step (reg := reg); change M.code (pc q 4) = _; rw [linked q 4]; simp [instruction,hop]
    have st₅ : M.program.step (pos 5) = .localStep (pos 6) := by
      apply pass_step (reg := reg); change M.code (pc q 5) = _; rw [linked q 5]; simp [instruction,hop]
    have st₆ : M.program.step (pos 6) = .localStep d := by
      apply pass_step (reg := reg); change M.code (pc q 6) = _; rw [linked q 6]; simp [instruction,hop]
    have same : Function.update s a (s a).tail = s := by rw [eq]; change Function.update s a [] = s; rw [← eq,Function.update_eq_self]
    refine ⟨d,.tick st₀ (.tick st₄ (.tick st₅ (.tick st₆ (.nil _)))),by simp [d],?_,rfl,⟨rfl,fun _ _ => rfl,fun _ _ => rfl⟩⟩
    rw [← eq,same]
    exact ⟨rep.unit,rep.zero,rep.bases,rep.tops,rep.cells⟩
  | cons b tail =>
    let c₁ := {c with pc := pc q 1}
    let ptr := L.address a tail.length
    let c₂ := c₁.put (pc q 2) (reg (.top a)) ptr
    let c₃ := c₂.put (pc q 3) (reg .tmp) (encodeBit w b)
    let d := {c₃ with pc := pc (next (some b)) 0}
    have hn : c.reg (reg (.top a)) ≠ c.reg (reg (.base a)) := by
      rw [rep.tops,rep.bases]
      intro h
      have he := congrArg Fin.val h
      rw [L.address_val a fit,L.address_val a (Nat.zero_le _),eq] at he
      simp at he
    have st₀ : M.program.step c = .localStep c₁ := by
      rw [linked.step c q 0 atPC]; simp [instruction,hop,Instr.run,hn,c₁]
    have st₁ : M.program.step c₁ = .localStep c₂ := by
      rw [linked.step c₁ q 1 rfl]
      simp [instruction,hop,Instr.run,c₂,c₁,ptr,rep.tops,rep.unit,eq,Layout.address,← add_assoc,BinaryOp.eval]
    have st₂ : M.program.step c₂ = .localStep c₃ := by
      rw [linked.step c₂ q 2 rfl]
      have cell := rep.cells a [] b tail eq
      simp [instruction,hop,Instr.run,c₃,c₂,c₁,ptr,Config.put,cell]
    have st₃ : M.program.step c₃ = .localStep d := by
      rw [linked.step c₃ q 3 rfl]
      have hone : (1 : Word w) ≠ 0 := by
        intro h
        have hv := congrArg Fin.val h
        simp [Nat.mod_eq_of_lt (Nat.one_lt_two_pow hw.ne')] at hv
      cases b <;> simp [instruction,hop,Instr.run,d,c₃,c₂,c₁,Config.put,encodeBit,rep.zero,hone]
    refine ⟨d,.tick st₀ (.tick st₁ (.tick st₂ (.tick st₃ (.nil _)))),rfl,?_,rfl,?_⟩
    · refine ⟨?_,?_,?_,?_,?_⟩
      · simp [d,c₃,c₂,c₁,Config.put,rep.unit]
      · simp [d,c₃,c₂,c₁,Config.put,rep.zero]
      · intro j; simp [d,c₃,c₂,c₁,Config.put,rep.bases]
      · intro j
        by_cases h : j = a
        · subst j; simp [d,c₃,c₂,c₁,ptr,Config.put]
        · simp [d,c₃,c₂,c₁,Config.put,h,rep.tops]
      · change L.Contents c.privateMem (Function.update s a (b::tail).tail)
        simpa only [eq] using L.contents_pop c.privateMem s a rep.cells
    · refine ⟨rfl,?_,fun _ _ => rfl⟩
      intro i hi
      have ne (j : Register K) : i ≠ reg j := fun e => hi ⟨j,e.symm⟩
      simp [d,c₃,c₂,c₁,Config.put,Function.update_of_ne (ne _)]


theorem pop_prefix {a : K} {next : Option Bool → Q} (hop : code q = .pop a next)
    (atPC : c.pc = pc q 0) (rep : Represents L reg c s) (hw : 0 < w) (fit : (s a).length ≤ L.capacity) :
    ∃ d, Prefix M c (List.replicate 4 .tick) d ∧ d.pc = pc (next (s a).head?) 0 ∧
      Represents L reg d (Function.update s a (s a).tail) ∧ Frame L reg c d := by
  obtain ⟨d,run,dst,repr,_,frame⟩ := pop_prefix_memory linked hop atPC rep hw fit
  exact ⟨d,run,dst,repr,frame⟩

omit [DecidableEq K] linked in
private theorem three_passes (atPC : c.pc = pc q 0)
    (op₀ : M.code (pc q 0) = .copy (reg .tmp) (reg .tmp) (pc q 1))
    (op₁ : M.code (pc q 1) = .copy (reg .tmp) (reg .tmp) (pc q 2))
    (op₂ : M.code (pc q 2) = .copy (reg .tmp) (reg .tmp) (pc q 3)) :
    Prefix M c [.tick,.tick,.tick] {c with pc := pc q 3} := by
  refine .tick (pass_step (reg := reg) (atPC ▸ op₀)) ?_
  refine .tick (pass_step (reg := reg) op₁) ?_
  exact .tick (pass_step (reg := reg) op₂) (.nil _)

omit [DecidableEq K] in
theorem goto_prefix_memory {next : Q} (hop : code q = .goto next) (atPC : c.pc = pc q 0)
    (rep : Represents L reg c s) :
    ∃ d, Prefix M c (List.replicate 4 .tick) d ∧ d.pc = pc next 0 ∧
      Represents L reg d s ∧ d.privateMem = c.privateMem ∧ Frame L reg c d := by
  have pad := three_passes (reg := reg) (M := M) atPC
    (by rw [linked q 0]; simp [instruction,hop])
    (by rw [linked q 1]; simp [instruction,hop])
    (by rw [linked q 2]; simp [instruction,hop])
  let d := {c with pc := pc next 0}
  have last : M.program.step {c with pc := pc q 3} = .localStep d := by
    apply pass_step (reg := reg)
    change M.code (pc q 3) = _
    rw [linked q 3]; simp [instruction,hop]
  exact ⟨d,pad.append (.tick last (.nil _)),rfl,⟨rep.unit,rep.zero,rep.bases,rep.tops,rep.cells⟩,rfl,
    ⟨rfl,fun _ _ => rfl,fun _ _ => rfl⟩⟩

omit [DecidableEq K] in
theorem goto_prefix {next : Q} (hop : code q = .goto next) (atPC : c.pc = pc q 0)
    (rep : Represents L reg c s) :
    ∃ d, Prefix M c (List.replicate 4 .tick) d ∧ d.pc = pc next 0 ∧
      Represents L reg d s ∧ Frame L reg c d := by
  obtain ⟨d,run,dst,repr,_,frame⟩ := goto_prefix_memory linked hop atPC rep
  exact ⟨d,run,dst,repr,frame⟩

omit [DecidableEq K] in
theorem choose_prefix_memory {lo hi : Q} (hop : code q = .choose lo hi) (atPC : c.pc = pc q 0)
    (rep : Represents L reg c s) (b : Bool) :
    ∃ d, Prefix M c [.tick,.tick,.tick,.choice b] d ∧ d.pc = pc (if b then hi else lo) 0 ∧
      Represents L reg d s ∧ d.privateMem = c.privateMem ∧ Frame L reg c d := by
  have pad := three_passes (reg := reg) (M := M) atPC
    (by rw [linked q 0]; simp [instruction,hop])
    (by rw [linked q 1]; simp [instruction,hop])
    (by rw [linked q 2]; simp [instruction,hop])
  let d (t : Bool) := {c with pc := pc (if t then hi else lo) 0}
  have last : M.program.step {c with pc := pc q 3} = .branch d := by
    rw [linked.step _ q 3 rfl]; simp [instruction,hop,Instr.run,d]
    funext t; cases t <;> rfl
  exact ⟨d b,pad.append (.choice last (.nil _)),rfl,⟨rep.unit,rep.zero,rep.bases,rep.tops,rep.cells⟩,rfl,
    ⟨rfl,fun _ _ => rfl,fun _ _ => rfl⟩⟩

omit [DecidableEq K] in
theorem choose_prefix {lo hi : Q} (hop : code q = .choose lo hi) (atPC : c.pc = pc q 0)
    (rep : Represents L reg c s) (b : Bool) :
    ∃ d, Prefix M c [.tick,.tick,.tick,.choice b] d ∧ d.pc = pc (if b then hi else lo) 0 ∧
      Represents L reg d s ∧ Frame L reg c d := by
  obtain ⟨d,run,dst,repr,_,frame⟩ := choose_prefix_memory linked hop atPC rep b
  exact ⟨d,run,dst,repr,frame⟩

omit [DecidableEq K] in
theorem halt_prefix_memory (hop : code q = .halt true) (atPC : c.pc = pc q 0)
    (rep : Represents L reg c s) :
    ∃ d, Prefix M c [.tick] d ∧ d.pc = done ∧ Represents L reg d s ∧ d.privateMem = c.privateMem ∧ Frame L reg c d := by
  let d := {c with pc := done}
  have st : M.program.step c = .localStep d := by
    apply pass_step (reg := reg); rw [atPC,linked q 0]; simp [instruction,hop]
  exact ⟨d,.tick st (.nil _),rfl,⟨rep.unit,rep.zero,rep.bases,rep.tops,rep.cells⟩,rfl,
    ⟨rfl,fun _ _ => rfl,fun _ _ => rfl⟩⟩

omit [DecidableEq K] in
theorem halt_prefix (hop : code q = .halt true) (atPC : c.pc = pc q 0)
    (rep : Represents L reg c s) :
    ∃ d, Prefix M c [.tick] d ∧ d.pc = done ∧ Represents L reg d s ∧ Frame L reg c d := by
  obtain ⟨d,run,dst,repr,_,frame⟩ := halt_prefix_memory linked hop atPC rep
  exact ⟨d,run,dst,repr,frame⟩

omit [DecidableEq K] in
theorem halt_reject (hop : code q = .halt false) (atPC : c.pc = pc q 0) :
    M.program.step c = .reject := by
  rw [linked.step c q 0 atPC]; simp [instruction,hop,Instr.run]

end PairSimulation.StackMachine

end VPVNP
end Computability
end OAI
