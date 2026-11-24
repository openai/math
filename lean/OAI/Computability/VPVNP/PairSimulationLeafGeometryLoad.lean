import OAI.Computability.VPVNP.PairSimulationLeafImage

/-!
# Reloading leaf operands at the descriptor visit

Private word `endAddr` points to the geometry array. Its first ten consecutive
words supply the leaf's descriptor fields, argument arena, and input length.
The native loader uses the DFS end pointer and the DFS unit register.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafGeometryLoad

open BurstRAM PrivateRAM PrimedCounter.GuessWord LeafRegisterBank LeafSourceLoad
open scoped Fin.CommRing

/-- The location of each leaf operand in the ten-word private geometry record. Address fields
occupy slots 0 through 5, arena fields occupy 6 through 8, and the input size occupies slot
9. -/
def slot : LeafImage.Pub ≃ Fin 10 where
  toFun
    | .address .base => 0
    | .address .stride => 1
    | .address .radixB => 2
    | .address .radixL => 3
    | .address .shadow => 4
    | .address .span => 5
    | .arena .start => 6
    | .arena .stride => 7
    | .arena .cache => 8
    | .size => 9
  invFun := ![.address .base, .address .stride, .address .radixB, .address .radixL,
    .address .shadow, .address .span, .arena .start, .arena .stride, .arena .cache, .size]
  left_inv j := by cases j <;> (try casesm* LeafAddress.Field) <;> (try casesm* RoutePrepare.Field) <;> rfl
  right_inv j := by fin_cases j <;> rfl

/-- Instruction labels for the initial geometry-pointer load and the ten pairs of field loads
and cursor increments. -/
abbrev Label := Unit ⊕ Fin 10 ⊕ Fin 10

private def fields (i : Fin 10) : Static 6 := (slots 6)[i.val]'i.isLt

private def offset (s : Static 6) : Fin 10 := ⟨s.offset,by cases s <;> simp [Static.offset]; omega⟩

private theorem offset_field (i : Fin 10) : offset (fields i) = i :=
  Fin.ext (slot_offset (k := 6) ⟨i.val,i.isLt⟩)

variable {p r k w : ℕ} (pc : Label → Fin p) (dfs : Fin 9 ↪ Fin r) (ports : Source 6 ↪ Fin r)
  (cursor : Fin r) (done : Fin p)

/-- Physical destination register for the operand in the given geometry slot. -/
def bank (i : Fin 10) : Fin r := ports (fields i).dest

private def readPC (i : Fin 11) := if h : i.val < 10 then pc (.inr (.inl ⟨i.val,h⟩)) else done

/-- Fetch the private geometry pointer, load each of its ten consecutive words into the
assigned register, and advance the pointer with the DFS unit register. -/
def instruction : Label → Instr w p r k
  | .inl _ => .loadPrivate cursor (dfs 6) (readPC pc done 0)
  | .inr (.inl i) => .loadPrivate (bank ports i) cursor (pc (.inr (.inr i)))
  | .inr (.inr i) => .binary .add cursor cursor (dfs 3) (readPC pc done i.succ)

theorem resize_instruction (i : Label) :
    (instruction (w := 5) (k := k) pc dfs ports cursor done i).resize w =
      instruction pc dfs ports cursor done i := by
  rcases i with i | i | i <;> rfl

/-- The contents of the geometry record, independent of the incoming leaf
registers. The assembler also uses slots ten and eleven for other vertex roles. -/
structure Stored (endAddr base : ℕ) (mem : Word w → Word w) (values : Fin 10 → Word w) : Prop where
  pointer : mem (endAddr : Word w) = (base : Word w)
  values_at : ∀ i : Fin 10, mem ((base+i.val : ℕ) : Word w) = values i

/-- One private pointer read and ten private loads with address increments.
Registers outside the ten destinations and the cursor are preserved. -/
theorem run (M : Machine w p r k) (rows : ∀ i, M.code (pc i) = instruction pc dfs ports cursor done i)
    (endAddr base : ℕ) (values : Fin 10 → Word w) (c : Config w p r) (entry : c.pc = pc (.inl ()))
    (ptr : c.reg (dfs 6) = (endAddr : Word w)) (one : c.reg (dfs 3) = 1)
    (saved : Stored endAddr base c.privateMem values)
    (apart : ∀ j, cursor ≠ ports j) (unit_sep : ∀ j, dfs 3 ≠ ports j) (unit_cursor : dfs 3 ≠ cursor) :
    ∃ out, Prefix M c (List.replicate 21 .tick) out ∧ out.pc = done ∧
      (∀ i, out.reg (bank ports i) = values i) ∧ out.privateMem = c.privateMem ∧
      out.persistent = c.persistent ∧ ∀ j, j ≠ cursor → (∀ i, j ≠ ports i) → out.reg j = c.reg j := by
  let start := c.put (readPC pc done 0) cursor (base : Word w)
  have first : M.program.step c = .localStep start := by
    change (M.code c.pc).run _ _ = _
    rw [entry,rows]
    simp only [instruction,Instr.run,ptr,saved.pointer,start]
  let vals := fun j : Static 6 => values (offset j)
  let inc := fun i : Fin (slots 6).length => pc (.inr (.inr i))
  have rd (i : Fin (slots 6).length) : M.code (readPC pc done i.castSucc) =
      readInstr ports cursor (inc i) (slots 6)[i] := by
    have hr : readPC pc done i.castSucc = pc (.inr (.inl i)) := by
      simp [readPC,show i.val < 10 from i.isLt]; rfl
    rw [hr]
    exact rows (.inr (.inl i))
  have adv (i : Fin (slots 6).length) : M.code (inc i) =
      incInstr cursor (dfs 3) (readPC pc done i.succ) := rows (.inr (.inr i))
  have path := cached_rows M ports cursor (dfs 3) (fun j => apart j.dest)
    (fun j => unit_sep j.dest) unit_cursor vals (slots 6) (readPC pc done) inc rd adv base start rfl
    (Function.update_self ..) (by simp [start,Config.put,Function.update_of_ne unit_cursor,one])
    (fun i => by
      change c.privateMem ((base+i.val : ℕ) : Word w) = values (offset (fields i))
      exact (saved.values_at i).trans (congrArg values (offset_field i)).symm)
  refine ⟨_, .tick first path, rfl, ?_, rfl, rfl, ?_⟩
  · intro i
    change Function.update ((slots 6).foldl (setStatic ports vals) start.reg) cursor _ (ports (fields i).dest) = values i
    rw [Function.update_of_ne (apart _).symm, fold_at, ite_eq_left (mem_slots _)]
    exact congrArg values (offset_field i)
  · intro j hj hu
    change Function.update ((slots 6).foldl (setStatic ports vals) start.reg) cursor _ j = c.reg j
    rw [Function.update_of_ne hj,fold_outside ports vals (slots 6) start.reg j (fun i => hu i.dest)]
    exact Function.update_of_ne hj ..

end PairSimulation.LeafGeometryLoad

end VPVNP
end Computability
end OAI
