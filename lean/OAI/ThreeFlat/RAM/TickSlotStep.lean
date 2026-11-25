import OAI.ThreeFlat.RAM.TickSlotWrites

namespace OAI
/-! # A native test-and-append instruction loop for group/slot ownership -/

namespace ThreeFlat.RAM.TickSlotLookup

open Computability.VPVNP.BurstRAM PrivateRAM Fin.CommRing

variable {w p r k : ℕ}

/-- Registers hold the vertex index, stop, owner-table cursor, output cursor,
selected count, group, slot, unit, and scratch word, respectively. -/
def code (pc : Fin 11 → Fin p) (R : Fin 9 ↪ Fin r) (exit : Fin p) : Fin 11 → Instr w p r k
  | 0 => .jumpLt (R 0) (R 1) (pc 1) exit
  | 1 => .readExternal (R 8) (R 2) (pc 2)
  | 2 => .binary .add (R 2) (R 2) (R 7) (pc 3)
  | 3 => .jumpEq (R 8) (R 5) (pc 4) (pc 9)
  | 4 => .readExternal (R 8) (R 2) (pc 5)
  | 5 => .jumpEq (R 8) (R 6) (pc 6) (pc 9)
  | 6 => .writeExternal (R 3) (R 0) (pc 7)
  | 7 => .binary .add (R 3) (R 3) (R 7) (pc 8)
  | 8 => .binary .add (R 4) (R 4) (R 7) (pc 9)
  | 9 => .binary .add (R 2) (R 2) (R 7) (pc 10)
  | _ => .binary .add (R 0) (R 0) (R 7) (pc 0)

def Ready (R : Fin 9 ↪ Fin r) (c : Config w p r) (i n src dst count : ℕ) (g s : Word w) : Prop :=
  c.reg (R 0) = (i : Word w) ∧ c.reg (R 1) = (n : Word w) ∧ c.reg (R 2) = (src : Word w) ∧
  c.reg (R 3) = (dst : Word w) ∧ c.reg (R 4) = (count : Word w) ∧ c.reg (R 5) = g ∧
  c.reg (R 6) = s ∧ c.reg (R 7) = 1

/-- Test the two physical owner words and conditionally write the current
vertex at the dense cursor. A failed comparison skips the write. -/
theorem advance_row (M : Machine w p r k) (pc : Fin 11 → Fin p) (R : Fin 9 ↪ Fin r) (exit : Fin p)
    (rom : ∀ j, M.code (pc j) = code pc R exit j) (own : Owner w) (g s : Word w)
    (i n src dst count : ℕ) (c : Config w p r) (m : Memory w) (atHead : c.pc = pc 0)
    (h : Ready R c i n src dst count g s) (row : i < n) (nw : n < 2^w)
    (sw : src+1 < 2^w) (dw : dst < 2^w)
    (first : m src = (own i).1) (second : m (src+1) = (own i).2) :
    let hit := matchesOwner own g s i
    ∃ t ≤ 11, ∃ d, advance M.program t c m = some (d,if hit then put m dst i else m) ∧
      d.pc = pc 0 ∧ Ready R d (i+1) n (src+2) (dst+hit.toNat) (count+hit.toNat) g s ∧
      d.persistent = c.persistent ∧ d.privateMem = c.privateMem := by
  obtain ⟨hi,hn,hs,hd,hc,hg,ht,hu⟩ := h
  have checked : (i : Word w) < (n : Word w) := by
    change ((i : Word w)).val < ((n : Word w)).val
    rwa [Fin.val_cast_of_lt (row.trans nw),Fin.val_cast_of_lt nw]
  have read0 : (src : Word w).val = src := Fin.val_cast_of_lt (by omega)
  have read1 : ((src : Word w)+1).val = src+1 := by
    simpa only [Nat.cast_add,Nat.cast_one] using (Fin.val_cast_of_lt sw : ((src+1 : ℕ) : Word w).val = src+1)
  have written : writeMemory m (dst : Word w) (i : Word w) = put m dst i := by
    funext j
    simp only [writeMemory,put,Fin.val_cast_of_lt dw]
  let t : ℕ := if (own i).1 = g then (if (own i).2 = s then 11 else 8) else 6
  refine ⟨t,by dsimp [t]; split_ifs <;> decide,?_⟩
  by_cases ag : (own i).1 = g <;> by_cases aslot : (own i).2 = s <;>
    simp (config := {decide := true}) [advance,Machine.program,atHead,rom,code,Instr.run,
      Config.put,Function.update,R.injective.eq_iff,BinaryOp.eval,Ready,
      hi,hn,hs,hd,hc,hg,ht,hu,checked,read0,read1,first,second,matchesOwner,Prod.ext_iff,
      t,ag,aslot,written,Nat.cast_add,add_assoc,one_add_one_eq_two]

end ThreeFlat.RAM.TickSlotLookup

end OAI
