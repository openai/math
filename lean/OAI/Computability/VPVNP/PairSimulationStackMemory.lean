import OAI.Computability.VPVNP.PairSimulationStackTable
import OAI.Computability.VPVNP.PrimedInputRAMHeaders

/-!
# Private bit-stack storage of the virtual validator

Each finite port has a disjoint private interval. Its empty pointer is
the interval base and its top pointer is the exclusive end of the occupied
cells. The top-first bit list occupies those cells in reverse order.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.StackMachine

open RAMTape BurstRAM BurstRAM.PrivateRAM PrimedInputRAM
open scoped Fin.CommRing

variable {K : Type} {w p r : ℕ}

/-- Private memory layout for named bit stacks, with a base for each stack and a common
capacity whose disjoint intervals and exclusive ends fit the machine address space. -/
structure Layout (K : Type) (w : ℕ) where
  /-- Natural address of the first private bit cell reserved for each named stack. -/
  base : K → ℕ
  /-- Number of private bit cells reserved for each stack. -/
  capacity : ℕ
  fits : ∀ a, base a + capacity < 2^w
  apart : ∀ a b, a ≠ b → base a + capacity ≤ base b ∨ base b + capacity ≤ base a

/-- Machine-word address of the cell at offset `i` from the base of stack `a`. -/
def Layout.address (L : Layout K w) (a : K) (i : ℕ) : Word w := ((L.base a+i : ℕ) : Word w)

theorem Layout.address_val (L : Layout K w) (a : K) {i : ℕ} (hi : i ≤ L.capacity) :
    (L.address a i).val = L.base a+i :=
  Nat.mod_eq_of_lt ((Nat.add_le_add_left hi _).trans_lt (L.fits a))

/-- Cell at offset equal to the length of the suffix after this bit. -/
def Layout.Contents (L : Layout K w) (mem : Word w → Word w) (s : Stacks K) : Prop :=
  ∀ a pre bit tail, s a = pre ++ bit :: tail → mem (L.address a tail.length) = encodeBit w bit

/-- The RAM configuration realizes the logical stack bank by holding zero and one, the base and
exclusive top pointers, and the occupied cells in bottom-to-top order. -/
structure Represents (L : Layout K w) (reg : Register K ↪ Fin r) (c : Config w p r) (s : Stacks K) : Prop where
  unit : c.reg (reg .one) = 1
  zero : c.reg (reg .zero) = 0
  bases : ∀ a, c.reg (reg (.base a)) = L.address a 0
  tops : ∀ a, c.reg (reg (.top a)) = L.address a (s a).length
  cells : L.Contents c.privateMem s

theorem Layout.contents_of_reverse (L : Layout K w) (mem : Word w → Word w) (s : Stacks K)
    (h : ∀ a (i : Fin (s a).reverse.length), mem (L.address a i.val) = encodeBit w ((s a).reverse[i.val])) :
    L.Contents mem s := by
  intro a pre b tail eq
  have hi : tail.length < (s a).reverse.length := by simp [eq]
  have hc := h a ⟨tail.length,hi⟩
  simpa [eq,List.reverse_append,List.reverse_cons,List.append_assoc] using hc

theorem Layout.contents_push [DecidableEq K] (L : Layout K w) (mem : Word w → Word w)
    (s : Stacks K) (k : K) (bit : Bool) (old : L.Contents mem s)
    (fit : ∀ a, (s a).length ≤ L.capacity) (space : (s k).length < L.capacity) :
    L.Contents (Function.update mem (L.address k (s k).length) (encodeBit w bit))
      (Function.update s k (bit :: s k)) := by
  intro a pre b tail h
  by_cases hk : a = k
  · subst a
    rw [Function.update_self] at h
    cases pre with
    | nil =>
      obtain ⟨rfl,rfl⟩ := List.cons.inj h
      exact Function.update_self ..
    | cons x pre =>
      have hs : s k = pre ++ b :: tail := (List.cons.inj h).2
      have hlen : tail.length < (s k).length := by rw [hs]; simp; omega
      have hne : L.address k tail.length ≠ L.address k (s k).length := by
        intro haddr
        have he := congrArg Fin.val haddr
        rw [L.address_val _ (hlen.le.trans space.le), L.address_val _ space.le] at he
        omega
      rw [Function.update_of_ne hne]
      exact old k pre b tail hs
  · rw [Function.update_of_ne hk] at h
    have hlen : tail.length < (s a).length := by rw [h]; simp; omega
    have hne : L.address a tail.length ≠ L.address k (s k).length := by
      intro haddr
      have he := congrArg Fin.val haddr
      rw [L.address_val _ (hlen.le.trans (fit a)), L.address_val _ space.le] at he
      rcases L.apart a k hk with sep | sep <;> have := fit a <;> omega
    rw [Function.update_of_ne hne]
    exact old a pre b tail h

theorem Layout.contents_pop [DecidableEq K] (L : Layout K w) (mem : Word w → Word w)
    (s : Stacks K) (k : K) (old : L.Contents mem s) :
    L.Contents mem (Function.update s k (s k).tail) := by
  intro a pre b tail h
  by_cases hk : a = k
  · subst a
    rw [Function.update_self] at h
    cases he : s k with
    | nil => simp [he] at h
    | cons x xs =>
      have hs : s k = (x::pre) ++ b :: tail := by simpa [he] using congrArg (x::·) h
      exact old k (x::pre) b tail hs
  · rw [Function.update_of_ne hk] at h
    exact old a pre b tail h

end PairSimulation.StackMachine

end VPVNP
end Computability
end OAI
