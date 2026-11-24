import OAI.Computability.VPVNP.PairSimulationLeafCacheWrite
import OAI.Computability.VPVNP.CompressorRecordRegisterSetup

/-!
# Publishing computed operand words to a private call descriptor

The same two-instruction store and increment used for the native scalar cache installs
an arbitrary fixed bank of words here. A two-instruction prelude copies the preserved
descriptor pointer and sets the increment to one. Every source register survives.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PrivateDescriptor

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord PairSimulation.LeafSourceLoad
open scoped Fin.CommRing

variable {n w p r k : ℕ}

/-- The instruction that stores the selected register value at the private descriptor cursor
and jumps to its increment. -/
def store (values : Fin n → Fin r) (cursor : Fin r) (inc : Fin n → Fin p) (j : Fin n) : Instr w p r k :=
  .storePrivate cursor (values j) (inc j)

/-- The linked instruction addresses that copy the descriptor pointer, set a unit increment,
and store and advance through all values. -/
structure Linked (M : Machine w p r k) (values : Fin n → Fin r) (ptr cursor unit : Fin r)
    (header : Fin 2 → Fin p) (pc : Fin (n+1) → Fin p) (inc : Fin n → Fin p) : Prop where
  copy : M.code (header 0) = .copy cursor ptr (header 1)
  one : M.code (header 1) = .constant unit 1 (pc 0)
  write : ∀ i, M.code (pc i.castSucc) = store values cursor inc i
  advance : ∀ i, M.code (inc i) = incInstr cursor unit (pc i.succ)

/-- The computed words are published contiguously while preserving the call pointer
and all private data outside its exact interval. -/
theorem publish (M : Machine w p r k) (values : Fin n → Fin r) (ptr cursor unit : Fin r)
    (header : Fin 2 → Fin p) (pc : Fin (n+1) → Fin p) (inc : Fin n → Fin p)
    (link : Linked M values ptr cursor unit header pc inc)
    (separate : unit ≠ cursor) (ptrCursor : ptr ≠ cursor) (ptrUnit : ptr ≠ unit)
    (valuesApart : ∀ i, values i ≠ cursor ∧ values i ≠ unit)
    (c : Config w p r) (entry : c.pc = header 0) (room : (c.reg ptr).val+n ≤ 2^w) :
    ∃ out, Prefix M c (List.replicate (2+2*n) .tick) out ∧ out.pc = pc (Fin.last n) ∧
      out.persistent = c.persistent ∧ out.reg ptr = c.reg ptr ∧
      (∀ i : Fin n, out.privateMem (out.reg ptr+(i.val : Word w)) = c.reg (values i)) ∧
      (∀ a : Word w, a.val < (c.reg ptr).val ∨ (c.reg ptr).val+n ≤ a.val → out.privateMem a = c.privateMem a) ∧
      ∀ j, j ≠ cursor → j ≠ unit → out.reg j = c.reg j := by
  let c₁ := c.put (header 1) cursor (c.reg ptr)
  let c₂ := c₁.put (pc 0) unit 1
  have first : M.program.step c = .localStep c₁ := by
    change (M.code c.pc).run M.publicData c = _
    rw [entry,link.copy]; rfl
  have second : M.program.step c₁ = .localStep c₂ := by
    change (M.code (header 1)).run M.publicData c₁ = _
    rw [link.one]; rfl
  have head : Prefix M c [.tick,.tick] c₂ := .tick first (.tick second (.nil _))
  let ls := (List.finRange n).map (Static.operand (k := n))
  have len : ls.length = n := by simp [ls]
  let source : Static n → Fin r := fun x => match x with
    | .operand i => values i
    | _ => unit
  have hsource : ∀ i, source i ≠ cursor := by intro i; cases i <;> first | exact separate | exact (valuesApart _).1
  let addr := (c.reg ptr).val
  let loc := fun i : Fin (ls.length+1) => pc (Fin.cast (by omega) i)
  let next := fun i : Fin ls.length => inc (Fin.cast len i)
  have writes (i : Fin ls.length) :
      M.code (loc i.castSucc) = storeInstr source cursor (next i) ls[i.val] := by
    let j := Fin.cast len i
    have h := link.write j
    change M.code (pc j.castSucc) = storeInstr source cursor (inc j) _
    rw [h]
    simp only [ls,List.getElem_map,List.getElem_finRange,source,store,storeInstr]
    congr 2
  have advance (i : Fin ls.length) : M.code (next i) = incInstr cursor unit (loc i.succ) := link.advance (Fin.cast len i)
  have ha : (addr : Word w) = c.reg ptr := Fin.ext (Nat.mod_eq_of_lt (c.reg ptr).isLt)
  have atCursor : c₂.reg cursor = (addr : Word w) := by
    simp [c₂,c₁,Config.put,separate.symm,ha]
  obtain ⟨out,tail,last,mem⟩ := write_rows M source cursor unit hsource separate ls (fun j => c₂.reg (source j)) loc next
    writes advance addr c₂ rfl atCursor (Function.update_self ..) (fun _ => rfl) (by simpa only [len] using room)
  have run := head.append tail
  rw [len] at run
  have frame (j : Fin r) (hc : j ≠ cursor) (hu : j ≠ unit) : out.reg j = c.reg j := by
    rw [mem.frame _ hc]; simp only [c₂,c₁,Config.put,Function.update_of_ne hu,Function.update_of_ne hc]
  have ptrEq := frame _ ptrCursor ptrUnit
  have finalPC : loc (Fin.last ls.length) = pc (Fin.last n) := congrArg pc (Fin.ext len)
  refine ⟨out,by simpa only [List.replicate_add,List.replicate_succ,List.replicate_zero,List.nil_append,List.cons_append] using run,
    last.trans finalPC,mem.persistent,ptrEq,fun i => ?_,fun a h => mem.outside a (by simpa only [addr,List.length_map,len] using h),frame⟩
  let j : Fin (ls.map (fun x => c₂.reg (source x))).length := ⟨i.val,by simpa only [List.length_map,len] using i.isLt⟩
  have hv := mem.values j
  rw [ptrEq,← ha]
  change out.privateMem ((addr : Word w)+(i.val : Word w)) = _
  rw [← Nat.cast_add]
  have h' : out.privateMem ((addr+i.val : ℕ) : Word w) = c₂.reg (values i) := by
    simp only [ls,Fin.getElem_fin,List.getElem_map,List.getElem_finRange,source,j] at hv
    exact hv.trans (congrArg (fun u => c₂.reg (values u)) (Fin.ext rfl))
  rw [h']
  simp only [c₂,c₁,Config.put,Function.update_of_ne (valuesApart i).2,Function.update_of_ne (valuesApart i).1]

end CompressorRecords.PrivateDescriptor

end VPVNP
end Computability
end OAI
