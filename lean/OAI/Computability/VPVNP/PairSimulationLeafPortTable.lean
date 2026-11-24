import OAI.Computability.VPVNP.PairSimulationLeafPortWalk

/-! # Finite instruction table allocating and filling every scalar leaf port -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafPortTable

open BurstRAM PrivateRAM PrimedCounter.GuessWord RAMTape StackMachine
open LeafStartup LeafRegisterBank
open scoped Fin.CommRing

variable {K : Type} [DecidableEq K] {d e w k p r pubs N : ℕ}

/-- Rows for allocating a port, finishing allocation, staging its scalar field and filling its
private stack. -/
inductive Label (K : Type) where
  | pointer (a : K) (i : Fin 3)
  | finish (i : Fin 2)
  | stage (a : K) (i : Fin 4)
  | fill (a : K) (i : Fin 6)
  deriving DecidableEq, Fintype

/-- Construct the successor-port lookup for a fixed traversal list, using the head of the
remaining suffix at each port. -/
def followers : List K → K → Option K
  | [] => fun _ => none
  | a::as => Function.update (followers as) a as.head?

/-- The successor lookup agrees with the traversal list at every port, including the final
port's empty successor. -/
def Follows (next : K → Option K) : List K → Prop
  | [] => True
  | a::as => next a = as.head? ∧ Follows next as

omit [DecidableEq K] in
private theorem follows_congr {f g : K → Option K} {todo : List K}
    (he : ∀ a ∈ todo, f a = g a) (hf : Follows f todo) : Follows g todo := by
  induction todo with
  | nil => trivial
  | cons a as ih =>
    exact ⟨(he a (List.mem_cons_self ..)).symm.trans hf.1, ih (fun j hj => he j (List.mem_cons_of_mem a hj)) hf.2⟩

theorem follows (todo : List K) (hn : todo.Nodup) : Follows (followers todo) todo := by
  induction todo with
  | nil => trivial
  | cons a as ih =>
    have h := List.nodup_cons.mp hn
    refine ⟨Function.update_self ..,follows_congr ?_ (ih h.2)⟩
    intro j hj
    exact (Function.update_of_ne (ne_of_mem_of_not_mem hj h.1) ..).symm

variable (tag : K → Field k) (pc : Label K → Fin p) (reg : Reg K k ↪ Fin r) (done : Fin p)

/-- Map a staging index to that port's staging row, with the final index pointing to the first
scalar fill instruction. -/
def stagePC : StageLabels tag p := fun a i =>
  let len := (Staging.code (scalarField (tag a))).length
  if h : i.val < len then pc (.stage a ⟨i.val,h.trans_le (Staging.length_le _)⟩) else pc (.fill a 0)

/-- The allocation, staging or fill instruction for one labeled row of the port list, including
its continuation to the following port. -/
def instruction (todo : List K) : Label K → Instr w p r pubs
  | .pointer a i => LeafPointers.allocate a (fun j => pc (.pointer a j)) (LeafFill.pointers (load reg))
      ((followers todo a).elim (pc (.finish 0)) fun b => pc (.pointer b 0)) i
  | .finish i => LeafPointers.finish (fun j => pc (.finish j)) (LeafFill.pointers (load reg))
      (first tag (stagePC tag pc) done todo) i
  | .stage a i =>
    let ls := Staging.code (scalarField (tag a))
    if h : i.val < ls.length then
      Staging.instruction (stage reg) (stagePC tag pc a (Fin.succ ⟨i.val,h⟩)) ls[i.val]
    else .reject
  | .fill a i => LeafScalarLoad.instruction (mode (scalarField (tag a))) (fun j => pc (.fill a j))
      (LeafFill.fieldRegisters (load reg) a)
      ((followers todo a).elim done fun b => stagePC tag pc b 0) i

theorem resize_instruction (todo : List K) (label : Label K) :
    (instruction (w := 1) (pubs := pubs) tag pc reg done todo label).resize w =
      instruction tag pc reg done todo label := by
  cases label with
  | pointer a i => simp only [instruction, LeafPointers.resize_allocate]
  | finish i => simp only [instruction, LeafPointers.resize_finish]
  | stage a i =>
    simp only [instruction]
    split <;> first | exact Staging.resize_instruction .. | rfl
  | fill a i => simp only [instruction, LeafScalarLoad.resize_instruction]

variable (M : Machine w p r pubs)

theorem rows (allPorts : List K) (hn : allPorts.Nodup)
    (link : ∀ j, M.code (pc j) = instruction tag pc reg done allPorts j) :
    LeafPointers.Rows M (LeafFill.pointers (load reg)) (fun a i => pc (.pointer a i)) (pc (.finish 0)) allPorts ∧
    ScalarRows tag M reg (stagePC tag pc) (fun a i => pc (.fill a i)) done allPorts := by
  have sub (todo : List K) (hf : Follows (followers allPorts) todo) :
      LeafPointers.Rows M (LeafFill.pointers (load reg)) (fun a i => pc (.pointer a i)) (pc (.finish 0)) todo ∧
      ScalarRows tag M reg (stagePC tag pc) (fun a i => pc (.fill a i)) done todo := by
    induction todo with
    | nil => exact ⟨trivial,trivial⟩
    | cons a as ih =>
      obtain ⟨ptr,sc⟩ := ih hf.2
      refine ⟨⟨?_,ptr⟩,?_,?_,?_,sc⟩
      · intro i
        simpa only [instruction,hf.1,LeafPointers.next] using link (.pointer a i)
      · simp [stagePC]
      · intro i
        let j : Fin 4 := ⟨i.val,i.isLt.trans_le (Staging.length_le _)⟩
        have hpc : stagePC tag pc a i.castSucc = pc (.stage a j) := by simp [stagePC,j,i.isLt]
        rw [hpc,link]
        simp [instruction,j,i.isLt]
      · intro i
        simpa only [instruction,hf.1,first] using link (.fill a i)
  exact sub allPorts (follows _ hn)

/-- Native scalar startup from the fixed rows. Its label set, register wiring,
and instructions are independent of the input values and widths. -/
theorem startup (order : Fin N ≃ K) (L : Layout K w) (base : ℕ)
    (hlayout : ∀ i, L.base (order i) = base+i.val*L.capacity)
    (x : VirtualSite.Input d e w) (args : Fin k → Word w)
    (link : ∀ j, M.code (pc j) = instruction tag pc reg done (List.ofFn order) j)
    (c : Config w p r) (hc : c.pc = LeafPointers.next (List.ofFn order) (fun a i => pc (.pointer a i)) (pc (.finish 0)))
    (hbase : c.reg (LeafFill.pointers (load reg) .cursor) = (base : Word w))
    (hstride : c.reg (LeafFill.pointers (load reg) .stride) = (L.capacity : Word w))
    (inputs : ∀ j, c.reg (reg (.inr j)) = sourceWord x args j) (room : ∀ a, (scalarBank tag x args a).length ≤ L.capacity) :
    ∃ out, Prefix M c (List.replicate (3*N+2+((List.ofFn order).map (ticks tag x args)).sum) .tick) out ∧
      out.pc = done ∧ Represents L (stack reg) out (scalarBank tag x args) ∧
      Staging.Sources x args (out.reg ∘ stage reg) ∧ out.persistent = c.persistent ∧
      (∀ i, i ∉ Set.range reg → out.reg i = c.reg i) ∧
      ∀ u, (∀ a, u.val < L.base a ∨ L.base a+(scalarBank tag x args a).length ≤ u.val) →
        out.privateMem u = c.privateMem u := by
  obtain ⟨hp,hs⟩ := rows tag pc reg done M (List.ofFn order) (List.nodup_ofFn.mpr order.injective) link
  exact scalar_startup tag x args M reg L (stagePC tag pc) (fun a i => pc (.fill a i)) done order base
    hlayout (fun a i => pc (.pointer a i)) (fun i => pc (.finish i)) hp (fun i => link (.finish i)) hs c hc hbase hstride inputs room

end PairSimulation.LeafPortTable

end VPVNP
end Computability
end OAI
