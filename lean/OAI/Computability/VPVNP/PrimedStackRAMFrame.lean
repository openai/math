import OAI.Computability.VPVNP.PrimedStackRAMChildren
import OAI.Computability.VPVNP.PrimedCounterVisit

/-!
# Memory represented at each node visit

Input, mark and count cells occupy disjoint regions from the frame planes.
The external stack instructions leave the full input rectangle, every mark
and every production count intact.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedStackRAM

open BurstRAM PrimedCounter
open scoped Fin.CommRing

variable {base R n m H w : ℕ}

/-- Recognize an input cell, leaf-position mark, or production counter among the parser’s
scratch locations. -/
def dataCell : Locations R n m H → Bool
  | .inl _ | .inr (.inr (.inr (.inl _))) | .inr (.inr (.inr (.inr (.inl _)))) => true
  | _ => false

/-- Agreement of two memories on the assembled inputs, leaf marks, and production counts of the
scratch rectangle based at `base`. -/
def DataEq (base R n m H : ℕ) (m₀ m₁ : Memory w) : Prop :=
  ∀ c : Locations R n m H, dataCell c → view base m₁ c = view base m₀ c

theorem DataEq.trans {m₀ m₁ m₂ : Memory w} (h₀ : DataEq base R n m H m₀ m₁)
    (h₁ : DataEq base R n m H m₁ m₂) : DataEq base R n m H m₀ m₂ :=
  fun c hc => (h₁ c hc).trans (h₀ c hc)

private theorem dataEq_store {mem : Memory w} (c : Locations R n m H) (v : Word w)
    (hf : base + size R n m (labelCount n m H) ≤ 2^w) (hc : dataCell c = false) :
    DataEq base R n m H mem (store base mem c v) := by
  intro a ha
  rw [view_store_apply base mem c a v hf, ite_eq_right (by rintro rfl; simp [hc] at ha)]

private theorem depth_mem {mem : Memory w} {stack : List (Word w × Word w)}
    (hr : Represents (R := R) (n := n) (m := m) (H := H) base mem stack)
    (hf : base + size R n m (labelCount n m H) ≤ 2^w) :
    mem (publicData w base R n m H 4).val = (stack.length : Word w) := by
  rw [public_depth_val base hf]
  exact len_word hr

theorem push_data {state : Word w} {regs rs : Regs w 16} {mem m' : Memory w} {es : List (Event w)}
    {stack : List (Word w × Word w)} (hr : Represents (R := R) (n := n) (m := m) (H := H) base mem stack)
    (hf : base + size R n m (labelCount n m H) ≤ 2^w) (hc : stack.length < n)
    (ht : trace (publicData w base R n m H) state push regs mem = some (es, rs, m')) :
    DataEq base R n m H mem m' := by
  let pub := publicData w base R n m H
  let i : Fin n := ⟨stack.length,hc⟩
  have hd := depth_mem hr hf
  have hn : n < 2^w := by unfold size at hf; omega
  have hlt : mem (pub 4).val < pub 5 := by
    rw [hd]
    change (stack.length : Word w).val < (n : Word w).val
    simpa only [Fin.val_natCast, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (hc.trans hn)] using hc
  obtain ⟨_, _, h, _⟩ := push_spec pub state regs mem hlt
  have he := congrArg (fun z : List (Event w) × Regs w 16 × Memory w => z.2.2) (Option.some.inj (ht.symm.trans h))
  dsimp only at he
  rw [he]
  have ad : pub 0 + mem (pub 4).val = (address base (degCell i : Locations R n m H) : Word w) := by
    rw [hd]; exact public_degree base i
  have ast : pub 1 + mem (pub 4).val = (address base (stateCell i : Locations R n m H) : Word w) := by
    rw [hd]; exact public_state base i
  have ap : pub 4 = (address base (depthCell : Locations R n m H) : Word w) := public_depth base
  rw [ad, ast, ap]
  exact (dataEq_store (degCell i) _ hf rfl).trans
    ((dataEq_store (stateCell i) _ hf rfl).trans (dataEq_store depthCell _ hf rfl))

theorem pop_data {state : Word w} {regs rs : Regs w 16} {mem m' : Memory w} {es : List (Event w)}
    {stack : List (Word w × Word w)} {f : Word w × Word w}
    (hr : Represents (R := R) (n := n) (m := m) (H := H) base mem (f :: stack))
    (hf : base + size R n m (labelCount n m H) ≤ 2^w)
    (ht : trace (publicData w base R n m H) state pop regs mem = some (es, rs, m')) :
    DataEq base R n m H mem m' := by
  let pub := publicData w base R n m H
  have hw : (f::stack).length < 2^w := hr.fits.trans_lt (by unfold size at hf; omega)
  have hd := depth_mem hr hf
  have hlt : 0 < mem (pub 4).val := by
    rw [hd]
    change 0 < ((f::stack).length : Word w).val
    rw [Fin.val_natCast, Nat.mod_eq_of_lt hw]
    simp
  obtain ⟨_, _, h, _⟩ := pop_spec pub state regs mem hlt
  have he := congrArg (fun z : List (Event w) × Regs w 16 × Memory w => z.2.2) (Option.some.inj (ht.symm.trans h))
  dsimp only at he
  rw [he]
  have ap : pub 4 = (address base (depthCell : Locations R n m H) : Word w) := public_depth base
  rw [ap]
  exact dataEq_store depthCell _ hf rfl

/-- The frame list encoded as exact machine words (top first). -/
def frames (w : ℕ) (stack : List (Frame n (Fin H))) : List (Word w × Word w) :=
  stack.map fun (d,h) => (↑d.val, ↑h.val)

/-- One complete logical visit state together with its assembled input rectangle. -/
structure Holds (base : ℕ) (x : Fin 2 → Fin R → Fin m → Bool)
    (st : VisitState n m H) (mem : Memory w) : Prop where
  pending : Represents (R := R) (n := n) (m := m) (H := H) base mem (frames w st.pending)
  input (g : Fin 2) (s : Fin R) (j : Fin m) :
    view base mem (.inl ((g,s),j) : Locations R n m H) = (↑(x g s j).toNat : Word w)
  marked (j : Fin m) :
    view base mem (markCell j : Locations R n m H) = (if j ∈ st.marked then 1 else 0)
  counts (a : Label n m (Fin H)) :
    (view base mem (countCell (labelIndex n m H a) : Locations R n m H)).val = st.counts a

theorem Holds.withStack {mem m' : Memory w} {x : Fin 2 → Fin R → Fin m → Bool} {st : VisitState n m H}
    (hr : Holds base x st mem) (stack : List (Frame n (Fin H))) (he : DataEq base R n m H mem m')
    (hs : Represents (R := R) (n := n) (m := m) (H := H) base m' (frames w stack)) :
    Holds base x {st with pending := stack} m' where
  pending := hs
  input g s j := (he _ rfl).trans (hr.input g s j)
  marked j := (he _ rfl).trans (hr.marked j)
  counts a := (congrArg Fin.val (he _ rfl)).trans (hr.counts a)

end PrimedStackRAM

end VPVNP
end Computability
end OAI
