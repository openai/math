import OAI.Computability.VPVNP.PairSimulationLeafPointers

/-!
# Installing a scalar field in the validator's represented stack bank

Only the selected top pointer and its occupied cells change. The proof also
covers empty fields and allows later leaves to reuse a previously occupied
region. All reads and writes in the initialization are private.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafFill

open RAMTape BurstRAM PrivateRAM PrimedInputRAM PrimedCounter.GuessWord StackMachine
open scoped Fin.CommRing

variable {K : Type} {w p r k : ℕ}

/-- Registers for a scalar stack fill, combining the stack allocation registers with the
field's length and source word. -/
inductive Reg (K : Type) where | pointers (j : LeafPointers.Reg K) | length | value
  deriving DecidableEq, Fintype

/-- Embed the stack allocation registers into the physical register placement of the scalar
fill loop. -/
def pointers (reg : Reg K ↪ Fin r) : LeafPointers.Reg K ↪ Fin r :=
  ⟨fun i => reg (.pointers i),fun _ _ h => Reg.pointers.inj (reg.injective h)⟩

/-- The host placement of stack registers reached through the fill loop's allocation registers. -/
def stack (reg : Reg K ↪ Fin r) := LeafPointers.stack (pointers reg)

@[simp] theorem pointers_at (reg : Reg K ↪ Fin r) (i : LeafPointers.Reg K) :
    pointers reg i = reg (.pointers i) := rfl

@[simp] theorem stack_at (reg : Reg K ↪ Fin r) (i : Register K) :
    stack reg i = reg (.pointers (.stack i)) := rfl

/-- The six physical registers of a port's scalar write loop, in order from its top pointer
through length, value, zero, one and scratch. -/
def fieldRegisters (reg : Reg K ↪ Fin r) (a : K) : Fin 6 ↪ Fin r where
  toFun := ![stack reg (.top a),reg .length,reg .value,stack reg .zero,stack reg .one,stack reg .tmp]
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

@[simp] theorem fieldRegisters_at (reg : Reg K ↪ Fin r) (a : K) (i : Fin 6) :
    fieldRegisters reg a i = ![stack reg (.top a),reg .length,reg .value,stack reg .zero,stack reg .one,
      stack reg .tmp] i := rfl

variable [DecidableEq K]

theorem contents_install (L : Layout K w) (a : K) (s : Stacks K) (xs : List Bool)
    (old new : Word w → Word w) (hs : L.Contents old s) (hfit : ∀ j, (s j).length ≤ L.capacity)
    (written : ∀ i : Fin xs.reverse.length, new (L.address a i.val) = encodeBit w xs.reverse[i.val])
    (frame : ∀ u, u.val < L.base a ∨ L.base a+L.capacity ≤ u.val → new u = old u) :
    L.Contents new (Function.update s a xs) := by
  intro j pre b tail he
  by_cases hj : j = a
  · subst j
    rw [Function.update_self] at he
    have lt : tail.length < xs.reverse.length := by simp [he]
    simpa [he, List.reverse_append, List.reverse_cons, List.append_assoc] using written ⟨tail.length,lt⟩
  · rw [Function.update_of_ne hj] at he
    have lt : tail.length < (s j).length := by simp [he]; omega
    rw [frame]
    · exact hs j pre b tail he
    · rw [L.address_val j (lt.le.trans (hfit j))]
      rcases L.apart j a hj with left | right
      · exact .inl ((Nat.add_lt_add_left (lt.trans_le (hfit j)) _).trans_le left)
      · exact .inr (right.trans (Nat.le_add_right ..))

/-- Deterministic execution of a scalar-port load, starting from a represented
bank and the two runtime operands. The destination port is empty at entry. -/
theorem install_scalar {M : Machine w p r k} {mode : LeafScalarLoad.Mode} {pc : Fin 6 → Fin p}
    {done : Fin p} (L : Layout K w) (reg : Reg K ↪ Fin r) (a : K) (s : Stacks K) (xs : List Bool)
    (value : Word w) (c : Config w p r) (link : LeafScalarLoad.Linked M mode pc (fieldRegisters reg a) done)
    (hw : 0 < w) (hc : c.pc = pc 0) (rep : Represents L (stack reg) c s) (ha : s a = [])
    (fit : ∀ j, (s j).length ≤ L.capacity) (room : xs.length ≤ L.capacity)
    (hlen : c.reg (reg .length) = (xs.length : Word w)) (hval : c.reg (reg .value) = value)
    (bits : LeafScalarLoad.payload mode value xs.length = xs.reverse) :
    ∃ out, Prefix M c (List.replicate (6*xs.length+1) .tick) out ∧ out.pc = done ∧
      Represents L (stack reg) out (Function.update s a xs) ∧ out.persistent = c.persistent ∧
      (∀ i, i ∉ Set.range reg → out.reg i = c.reg i) ∧
      ∀ u, u.val < L.base a ∨ L.base a+xs.length ≤ u.val → out.privateMem u = c.privateMem u := by
  have bound := (Nat.add_le_add_left room (L.base a)).trans_lt (L.fits a)
  have hp : c.reg (fieldRegisters reg a 0) = (L.base a : Word w) := by
    change c.reg (stack reg (.top a)) = _
    rw [rep.tops,ha]; rfl
  obtain ⟨out,run,res⟩ := LeafScalarLoad.load_prefix link hw xs.length (L.base a) value c hc hp
    hlen hval rep.zero rep.unit bound
  have dst := res.destination
  change out.reg (stack reg (.top a)) = _ at dst
  rw [bits,List.length_reverse] at dst
  have mem := res.memory
  rw [bits] at mem
  have unchanged (u : Word w) (hu : u.val < L.base a ∨ L.base a+xs.length ≤ u.val) :
      out.privateMem u = c.privateMem u := by
    rw [mem]
    exact PrivateFields.storeBits_outside (L.base a) xs.reverse c.privateMem u (by simpa using bound.le)
      (by simpa using hu)
  have keep (i : Register K) (hne : i ≠ .top a) (ht : i ≠ .tmp) :
      out.reg (stack reg i) = c.reg (stack reg i) :=
    res.frame _ (by simpa using hne) (by simp) (by simpa using ht)
  refine ⟨out,run,res.pc,?_,res.persistent,?_,unchanged⟩
  · refine ⟨(keep .one nofun nofun).trans rep.unit,(keep .zero nofun nofun).trans rep.zero,
      fun j => (keep (.base j) nofun nofun).trans (rep.bases j),?_,?_⟩
    · intro j
      by_cases hj : j = a
      · subst j; rw [Function.update_self]; exact dst
      · rw [Function.update_of_ne hj,keep (.top j) (by simpa using hj) nofun,rep.tops]
    · apply contents_install L a s xs c.privateMem out.privateMem rep.cells fit
      · intro i
        rw [mem]
        exact PrivateFields.storeBits_read (L.base a) xs.reverse c.privateMem (by simpa using bound.le) i
      · intro u hu
        exact unchanged u (hu.imp_right ((Nat.add_le_add_left room _).trans ·))
  · intro i hi
    have ne (j : Reg K) : i ≠ reg j := fun he => hi ⟨j,he.symm⟩
    exact res.frame _ (ne _) (ne _) (ne _)

end PairSimulation.LeafFill

end VPVNP
end Computability
end OAI
