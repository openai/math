import OAI.Hierarchy.TaggedShorterChronoArray
import OAI.Hierarchy.TaggedShorterHistorySort
import OAI.Hierarchy.TaggedShorterClock

namespace OAI
/-! # Physical controller cut with observed final-memory output words

The CPU array has a fixed bit width. Its local tests, the encoder of the
chronological probe array and the stable memory sort share those very pins.
All record bits are internal. There is one exposed simultaneous product of
the width-m tagged sorts used for the memory audit.
-/

noncomputable section
namespace Hierarchy.TaggedShorterControlHistory
open ThreeFlat Routing Diagonal TraceRows TraceBanks
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory Computability.VPVNP.RAMSerialization
open Tagged TaggedShorterChronology
open scoped Classical BigOperators

variable {F : Type*} [CommRing F] {w p r k f S u m a : ℕ}
abbrev Hole := ControlSort.Hole
abbrev Pin (S f u w r m a : ℕ) := TaggedShorterChronoArray.Input S f u w r ⊕ Hole m a
private abbrev Bus := TaggedShorterChronoArray.Output

private def Port (S f u w r m a : ℕ) : Option Bool → Type
  | none => TaggedShorterClock.Pin w r f
  | some false => TaggedShorterChronoArray.Pin S f u w r m
  | some true => TaggedShorterHistoryOrder.CutPins m (w+1) a

private instance (i : Option Bool) : Fintype (Port S f u w r m a i) := by
  cases i with
  | none => exact inferInstanceAs (Fintype (TaggedShorterClock.Pin w r f))
  | some b => cases b <;> dsimp [Port] <;> infer_instance

private def tap : (i : Option Bool) → Port S f u w r m a i → Pin S f u w r m a ⊕ Bus m w
  | none,b => .inl (.inl (.inr (.inl b)))
  | some false,.inl d => .inl (.inl d)
  | some false,.inr y => .inr y
  | some true,.inl y => .inr y
  | some true,.inr z => .inl (.inr z)

private def part (M : Machine w p r k) (hw : 3≤w+1) (hp : p≤2^(w+1)) (st : Word w)
    (hs : S≤2^(w+1)) (ht : f+u≤2^(w+1)) (addr : Fin u → Word (w+1)) :
    (i : Option Bool) → BitNetwork F (Fintype.card (Port S f u w r m a i))
  | none => TaggedShorterClock.network M hw hp st
  | some false => TaggedShorterChronoArray.network hw hs ht addr
  | some true => TaggedShorterHistoryOrder.audit (by omega)

def network (M : Machine w p r k) (hw : 3≤w+1) (hp : p≤2^(w+1)) (st : Word w)
    (hs : S≤2^(w+1)) (ht : f+u≤2^(w+1)) (addr : Fin u → Word (w+1)) :
    BitNetwork F (Fintype.card (Pin S f u w r m a)) := TypedWiring.glue (part M hw hp st hs ht addr) tap

def controls (header : ℕ → Word (w+1)) (raw : TaggedShorterClock.Pin w r f → Bool)
    (out : Fin u → Word (w+1)) : TaggedShorterChronoArray.Input S f u w r → Bool :=
  Sum.elim (fun atBit => TraceWords.bits (header atBit.1.val) atBit.2)
    (Sum.elim raw (fun atBit => TraceWords.bits (out atBit.1) atBit.2))

def Valid (M : Machine w p r k) (hw : 3≤w+1) (hp : p≤2^(w+1)) (st : Word w) (S : ℕ)
    (addr : Fin u → Word (w+1)) (header : ℕ → Word (w+1))
    (raw : TaggedShorterClock.Pin w r f → Bool) (out : Fin u → Word (w+1)) : Prop :=
  let xs:=readCpu hw hp (Function.curry raw)
  let log:=List.ofFn xs
  writeCpu hw hp xs=Function.curry raw ∧
  Local (exposed M) ((exposed M).start (wide st)) log ∧
  Correct (initialMemory S header) (report log).events ∧
  ∀ i, out i = after (initialMemory S header) (report log).events (addr i).val

private theorem network_eval (M : Machine w p r k) (hw : 3≤w+1) (hp : p≤2^(w+1)) (st : Word w)
    (hs : S≤2^(w+1)) (ht : f+u≤2^(w+1)) (addr : Fin u → Word (w+1))
    (header : ℕ → Word (w+1)) (raw : TaggedShorterClock.Pin w r f → Bool) (out : Fin u → Word (w+1))
    (z : Hole m a → Bool) :
    TypedWiring.value (network (F:=F) M hw hp st hs ht addr) (Sum.elim (controls header raw out) z) =
      TypedWiring.value (TaggedShorterClock.network M hw hp st) raw *
      ∑ y : Bus m w → Bool,
      TypedWiring.value (TaggedShorterChronoArray.network hw hs ht addr) (Sum.elim (controls header raw out) y) *
      TypedWiring.value (TaggedShorterHistoryOrder.audit (by omega : 2≤w+1)) (Sum.elim y z) := by
  rw [network,TypedWiring.glue_value,Finset.mul_sum]
  apply Finset.sum_congr (congrArg (@Finset.univ (Bus m w → Bool)) (Subsingleton.elim _ _))
  intro y _
  rw [Fintype.prod_option,Fintype.prod_bool]
  apply congrArg₂ (·*·)
  · rfl
  · rw [mul_comm]
    apply congrArg₂ (·*·)
    · apply congrArg (TypedWiring.value (TaggedShorterChronoArray.network (F:=F) hw hs ht addr))
      funext j
      cases j <;> rfl
    · apply congrArg (TypedWiring.value (TaggedShorterHistoryOrder.audit (F:=F) (by omega : 2≤w+1)))
      funext j
      cases j <;> rfl

theorem contract (M : Machine w p r k) (hw : 3≤w+1) (hp : p≤2^(w+1)) (st : Word w)
    (hs : S≤2^(w+1)) (ht : f+u≤2^(w+1)) (addr : Fin u → Word (w+1)) (fits : S+(f+u)≤2^m)
    (positive : 0<a) (room : TaggedShorterHistoryOrder.RecordWidth (w+1)≤a*m)
    (header : ℕ → Word (w+1)) (raw : TaggedShorterClock.Pin w r f → Bool) (out : Fin u → Word (w+1)) :
    (∑ z : Hole m a → Bool,
      TypedWiring.value (network (F:=F) M hw hp st hs ht addr) (Sum.elim (controls header raw out) z) *
       ∏ b : Fin a, Tagged.coeff F m m (fun j => z (b,j))) =
      if Valid M hw hp st S addr header raw out then 1 else 0 := by
  let xs := readCpu hw hp (Function.curry raw)
  let localOK := Local (exposed M) ((exposed M).start (wide st)) (List.ofFn xs)
  by_cases admitted : writeCpu hw hp xs=Function.curry raw ∧ localOK
  · have inputs : controls (S:=S) header raw out=TaggedShorterChronoArray.external hw hp header xs out := by
      change Sum.elim _ (Sum.elim raw _) = Sum.elim _ (Sum.elim (Function.uncurry (writeCpu hw hp xs)) _)
      rw [admitted.1]
      rfl
    let sig := fun j : Fin (2^m) => slot S hs ht header (events xs addr out) j.val
    have step (z : Hole m a → Bool) :
        TypedWiring.value (network (F:=F) M hw hp st hs ht addr) (Sum.elim (controls header raw out) z) =
          TypedWiring.value (TaggedShorterHistoryOrder.audit (by omega : 2≤w+1))
            (Sum.elim (Function.uncurry (TaggedShorterHistoryOrder.bits (by omega) ∘ sig)) z) := by
      rw [network_eval,TaggedShorterClock.checks,ite_eq_left admitted,one_mul,inputs]
      simp_rw [TaggedShorterChronoArray.eval]
      simp [sig]
    simp_rw [step]
    rw [TaggedShorterHistoryOrder.checks (by omega) positive room S header (List.ofFn (events xs addr out))
      (by simpa using fits) sig (slot_input S m hs ht header _)]
    have cc := correct_events (exposed M) xs admitted.2 addr out (initialMemory S header)
    have iffValid : Correct (initialMemory S header) (List.ofFn (events xs addr out)) ↔
        Valid M hw hp st S addr header raw out :=
      ⟨fun h => ⟨admitted.1,admitted.2,cc.mp h⟩,fun h => cc.mpr h.2.2⟩
    by_cases h : Valid M hw hp st S addr header raw out
    · rw [ite_eq_left h,ite_eq_left (iffValid.mpr h)]
    · rw [ite_eq_right h,ite_eq_right (fun q => h (iffValid.mp q))]
  · have denied : ¬ Valid M hw hp st S addr header raw out := fun h => admitted ⟨h.1,h.2.1⟩
    have blank (z : Hole m a → Bool) :
        TypedWiring.value (network (F:=F) M hw hp st hs ht addr)
          (Sum.elim (controls header raw out) z) = 0 := by
      rw [network_eval,TaggedShorterClock.checks,ite_eq_right admitted,zero_mul]
    simp only [blank,zero_mul,Finset.sum_const_zero,ite_eq_right denied]

end Hierarchy.TaggedShorterControlHistory

end
end OAI
