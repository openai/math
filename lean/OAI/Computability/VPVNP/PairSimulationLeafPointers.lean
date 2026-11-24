import OAI.Computability.VPVNP.PairSimulationLeafScalarLoad

/-!
# Allocating the auxiliary validator's private stack ports

The loop is unrolled only over the fixed set of machine ports. Each port
receives two equal pointers at its empty interval. Existing cells may hold
arbitrary values. The capacity and first address come from the enclosing
call's registers, so the instruction table is independent of the input length.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafPointers

open BurstRAM PrivateRAM PrimedCounter.GuessWord RAMTape StackMachine
open scoped Fin.CommRing

variable {K : Type} {N w p r k : ℕ}

/-- The validator's stack registers together with the allocation cursor and per-stack address
stride. -/
inductive Reg (K : Type) where
  | stack (j : Register K) | cursor | stride
  deriving DecidableEq, Fintype

/-- Physical embedding of the stack registers inside the pointer allocator's register bank. -/
def stack (reg : Reg K ↪ Fin r) : Register K ↪ Fin r :=
  ⟨fun i => reg (.stack i),fun _ _ h => Reg.stack.inj (reg.injective h)⟩

@[simp] theorem stack_apply (reg : Reg K ↪ Fin r) (j : Register K) :
    stack reg j = reg (.stack j) := rfl

/-- The final two rows initialize the permanent zero and unit operands. -/
def finish (pc : Fin 2 → Fin p) (reg : Reg K ↪ Fin r) (done : Fin p) : Fin 2 → Instr w p r k :=
  ![.constant (reg (.stack .zero)) 0 (pc 1), .constant (reg (.stack .one)) 1 done]

/-- Three instructions set a port's base and top to the current cursor, then advance the cursor
by one stack stride. -/
def allocate (a : K) (pc : Fin 3 → Fin p) (reg : Reg K ↪ Fin r) (next : Fin p) :
    Fin 3 → Instr w p r k :=
  ![.copy (reg (.stack (.base a))) (reg .cursor) (pc 1),
    .copy (reg (.stack (.top a))) (reg .cursor) (pc 2),
    .binary .add (reg .cursor) (reg .cursor) (reg .stride) next]

theorem resize_allocate (a : K) (pc : Fin 3 → Fin p) (reg : Reg K ↪ Fin r) (next : Fin p)
    (i : Fin 3) : (allocate (w := 1) (k := k) a pc reg next i).resize w = allocate a pc reg next i := by
  fin_cases i <;> rfl

theorem resize_finish (pc : Fin 2 → Fin p) (reg : Reg K ↪ Fin r) (done : Fin p) (i : Fin 2) :
    (finish (w := 1) (k := k) pc reg done i).resize w = finish pc reg done i := by fin_cases i <;> rfl

variable (M : Machine w p r k) (reg : Reg K ↪ Fin r)

/-- Continue at the first allocation instruction of the next port, or at the end label once the
list is empty. -/
def next (todo : List K) (pc : K → Fin 3 → Fin p) (endPC : Fin p) : Fin p :=
  todo.head?.elim endPC (fun a => pc a 0)

/-- The host code allocates each port in the given order and links the last allocation to the
specified end label. -/
def Rows (pc : K → Fin 3 → Fin p) (endPC : Fin p) : List K → Prop
  | [] => True
  | a::as => (∀ i, M.code (pc a i) = allocate a (pc a) reg (next as pc endPC) i) ∧ Rows pc endPC as

private theorem walk (pc : K → Fin 3 → Fin p) (endPC : Fin p) (todo : List K)
    (hl : Rows M reg pc endPC todo) (hn : todo.Nodup) (base stride : ℕ) (c : Config w p r)
    (hc : c.pc = next todo pc endPC) (hbase : c.reg (reg .cursor) = (base : Word w))
    (hstride : c.reg (reg .stride) = (stride : Word w)) :
    ∃ out, Prefix M c (List.replicate (3*todo.length) .tick) out ∧ out.pc = endPC ∧
      (∀ j : Fin todo.length, let a := todo[j.val]
        out.reg (reg (.stack (.base a))) = ((base+j.val*stride : ℕ) : Word w) ∧
        out.reg (reg (.stack (.top a))) = ((base+j.val*stride : ℕ) : Word w)) ∧
      (∀ i, i ≠ reg .cursor → (∀ a ∈ todo, i ≠ reg (.stack (.base a)) ∧ i ≠ reg (.stack (.top a))) →
        out.reg i = c.reg i) ∧ out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  induction todo generalizing base c with
  | nil => exact ⟨c,.nil _,hc,fun i => i.elim0,fun _ _ _ => rfl,rfl,rfl⟩
  | cons a as ih =>
    have hrows := hl.1
    have hnodup := List.nodup_cons.mp hn
    let ptr := (base : Word w)
    let c₁ := c.put (pc a 1) (reg (.stack (.base a))) ptr
    let c₂ := c₁.put (pc a 2) (reg (.stack (.top a))) ptr
    let mid := c₂.put (next as pc endPC) (reg .cursor) ((base+stride : ℕ) : Word w)
    have st₀ : M.program.step c = .localStep c₁ := by
      change (M.code c.pc).run _ _ = _
      rw [hc,show next (a::as) pc endPC = pc a 0 from rfl,hrows 0]; simp [allocate,Instr.run,c₁,ptr,hbase]
    have st₁ : M.program.step c₁ = .localStep c₂ := by
      change (M.code (pc a 1)).run _ c₁ = _
      rw [hrows 1]; simp [allocate,Instr.run,c₂,c₁,Config.put,hbase,ptr]
    have st₂ : M.program.step c₂ = .localStep mid := by
      change (M.code (pc a 2)).run _ c₂ = _
      rw [hrows 2]; simp [allocate,Instr.run,mid,c₂,c₁,Config.put,BinaryOp.eval,hbase,hstride]
    have head : Prefix M c (List.replicate 3 .tick) mid := .tick st₀ (.tick st₁ (.tick st₂ (.nil _)))
    obtain ⟨out,run,hd,values,frame,mem,state⟩ := ih hl.2 hnodup.2 (base+stride) mid rfl
      (by simp [mid,Config.put]) (by simp [mid,c₂,c₁,Config.put,hstride])
    have all := head.append run
    rw [← List.replicate_add,show 3+3*as.length=3*(a::as).length by simp; omega] at all
    refine ⟨out,all,hd,?_,?_,mem,state⟩
    · intro j
      induction j using Fin.cases with
      | zero =>
        change out.reg (reg (.stack (.base a))) = _ ∧ out.reg (reg (.stack (.top a))) = _
        constructor
        · rw [frame _ (by simp) (fun b hb => by have hn := ne_of_mem_of_not_mem hb hnodup.1; simp [Ne.symm hn])]
          simp [mid,c₂,c₁,ptr,Config.put]
        · rw [frame _ (by simp) (fun b hb => by have hn := ne_of_mem_of_not_mem hb hnodup.1; simp [Ne.symm hn])]
          simp [mid,c₂,c₁,ptr,Config.put]
      | succ j =>
        simpa [Nat.succ_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using values j
    · intro i hi ha
      have hhead := ha a (List.mem_cons_self ..)
      rw [frame _ hi (fun b hb => ha b (List.mem_cons_of_mem _ hb))]
      simp [mid,c₂,c₁,Config.put,Function.update_of_ne hi,Function.update_of_ne hhead.1,
        Function.update_of_ne hhead.2]

/-- From the caller's base address and stride, install the actual pointer registers
and represent an empty bank even when this is a later leaf reusing the same region. -/
theorem initialize_pointers (L : Layout K w) (order : Fin N ≃ K) (base : ℕ)
    (hlayout : ∀ i, L.base (order i) = base+i.val*L.capacity) (pc : K → Fin 3 → Fin p)
    (endPC : Fin 2 → Fin p) (done : Fin p) (hl : Rows M reg pc (endPC 0) (List.ofFn order))
    (hf : ∀ i, M.code (endPC i) = finish endPC reg done i) (c : Config w p r)
    (hc : c.pc = next (List.ofFn order) pc (endPC 0))
    (hbase : c.reg (reg .cursor) = (base : Word w)) (hstride : c.reg (reg .stride) = (L.capacity : Word w)) :
    ∃ out, Prefix M c (List.replicate (3*N+2) .tick) out ∧ out.pc = done ∧
      Represents L (stack reg) out (fun _ => []) ∧ out.privateMem = c.privateMem ∧
      out.persistent = c.persistent ∧ ∀ i, i ∉ Set.range reg → out.reg i = c.reg i := by
  have hn : (List.ofFn order).Nodup := List.nodup_ofFn.mpr order.injective
  obtain ⟨mid,run,hm,values,frame,mem,state⟩ := walk M reg pc (endPC 0) _ hl hn base L.capacity c hc hbase hstride
  let u := mid.put (endPC 1) (reg (.stack .zero)) 0
  let out := u.put done (reg (.stack .one)) 1
  have h₀ : M.program.step mid = .localStep u := by
    change (M.code mid.pc).run _ _ = _; rw [hm,hf 0]; rfl
  have h₁ : M.program.step u = .localStep out := by
    change (M.code (endPC 1)).run _ _ = _; rw [hf 1]; rfl
  have fin : Prefix M mid (List.replicate 2 .tick) out := .tick h₀ (.tick h₁ (.nil _))
  have hr := run.append fin
  rw [List.length_ofFn,← List.replicate_add] at hr
  have ptr (a : K) : mid.reg (reg (.stack (.base a))) = L.address a 0 ∧
      mid.reg (reg (.stack (.top a))) = L.address a 0 := by
    obtain ⟨i,rfl⟩ := order.surjective a
    have eq := values (i.cast (List.length_ofFn.symm))
    simpa [List.getElem_ofFn,Layout.address,hlayout] using eq
  refine ⟨out,hr,rfl,?_,mem,state,?_⟩
  · refine ⟨?_,?_,?_,?_,?_⟩
    · simp [out,Config.put]
    · simp [out,u,Config.put]
    · intro a; simpa [out,u,Config.put] using (ptr a).1
    · intro a; simpa [out,u,Config.put] using (ptr a).2
    · intro a pre bit tail he; simp at he
  · intro i hi
    have ne (j : Reg K) : i ≠ reg j := fun e => hi ⟨j,e.symm⟩
    rw [show out.reg i = mid.reg i by simp [out,u,Config.put,Function.update_of_ne (ne _)]]
    exact frame _ (ne _) (fun _ _ => ⟨ne _,ne _⟩)

end PairSimulation.LeafPointers

end VPVNP
end Computability
end OAI
