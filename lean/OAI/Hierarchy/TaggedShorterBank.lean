import OAI.Hierarchy.TaggedShorterCompaction
import OAI.ThreeFlat.BitNetwork.UsedHidden

namespace OAI
/-! # One cut-open oracle for an entire shorter type

The public hole is the product of all installed modules. The checks below
contract it only once, independently of how many modules are empty.
-/

noncomputable section
namespace Hierarchy.TaggedShorterBank
open ThreeFlat Routing Spill TaggedShorterCompaction
open scoped Classical BigOperators

variable {F : Type*} [CommSemiring F] {S D H M m : ℕ} {Q : Type} [Fintype Q]

abbrev OpenPins (S D M m : ℕ) (Q : Type) := Input S D m ⊕ (Fin M × Q)

private def Port (S D H M m : ℕ) (Q : Type) : Option (Fin M) → Type
  | none => Input S D m ⊕ Output M H m
  | some _ => Option (Pair H m) ⊕ Q

private instance (i : Option (Fin M)) : Fintype (Port S D H M m Q i) := by
  cases i <;> dsimp [Port] <;> infer_instance

private def wire (S D H M m : ℕ) (Q : Type) : (i : Option (Fin M)) →
    Port S D H M m Q i → OpenPins S D M m Q ⊕ Output M H m
  | none, .inl p => .inl (.inl p)
  | none, .inr p => .inr p
  | some i, .inl none => .inr (i,none)
  | some i, .inl (some p) => .inr (i,some (Fintype.equivFin (Pair H m) p))
  | some i, .inr p => .inl (.inr (i,p))

variable (near : Compactor F D H m) (far : Compactor F S M (Width H m))
    (lane : BitNetwork F (Fintype.card (Option (Pair H m) ⊕ Q)))

private def part : (i : Option (Fin M)) → BitNetwork F (Fintype.card (Port S D H M m Q i))
  | none => network near far
  | some _ => lane

def cut := TypedWiring.glue (part near far lane) (wire S D H M m Q)

theorem cut_cells : (cut near far lane).cells =
    far.network.cells + (2*S)*near.network.cells + M*lane.cells := by
  simp [cut,TypedWiring.glue_cells,Fintype.sum_option,part,network_cells]

/-- Normalize the resulting cut-open circuit, charging three hidden bits per
local table plus one scalar table regardless of the number of idle modules. -/
theorem cut_size : (cut near far lane).compactHidden.cells + (cut near far lane).compactHidden.internal ≤
    4*(far.network.cells + (2*S)*near.network.cells + M*lane.cells)+1 := by
  simpa only [cut_cells] using BitNetwork.compactHidden_size (cut near far lane)

def readOut (z : Output M H m → Bool) (i : Fin M) : Option (Pair H m) → Bool
  | none => z (i,none)
  | some p => z (i,some (Fintype.equivFin _ p))

def closeLane (lane : BitNetwork F (Fintype.card (Option (Pair H m) ⊕ Q))) (oracle : (Q → Bool) → F)
    (data : Option (Pair H m) → Bool) := ∑ v : Q → Bool, TypedWiring.value lane (Sum.elim data v) * oracle v

def close (N : BitNetwork F (Fintype.card (OpenPins S D M m Q)))
    (oracle : (Q → Bool) → F) (x : Input S D m → Bool) :=
  ∑ v : (Fin M × Q) → Bool, TypedWiring.value N (Sum.elim x v) * ∏ i, oracle (fun p => v (i,p))

theorem cut_eval (x : Input S D m → Bool) (z : Output M H m → Bool)
    (hit : ∀ z', TypedWiring.value (network near far) (Sum.elim x z') = if z=z' then 1 else 0)
    (v : Fin M × Q → Bool) :
    TypedWiring.value (cut near far lane) (Sum.elim x v) =
      ∏ i, TypedWiring.value lane (Sum.elim (readOut z i) (fun p => v (i,p))) := by
  let : DecidableEq (Output M H m) := Classical.decEq _
  rw [cut,TypedWiring.glue_value]
  let term h i := TypedWiring.value (part near far lane i)
    (fun p => Sum.elim (Sum.elim x v) h (wire S D H M m Q i p))
  have board h : term h none = if z = h then 1 else 0 := by
    apply Eq.trans _ (hit h)
    apply congrArg (TypedWiring.value (network near far))
    funext p; cases p <;> rfl
  have socket h i : term h (some i) = TypedWiring.value lane (Sum.elim (readOut h i) (fun p => v (i,p))) := by
    apply congrArg (TypedWiring.value lane)
    funext p; rcases p with (_ | p) | p <;> rfl
  change (∑ h, ∏ i, term h i) = _
  simp only [Fintype.prod_option,board,socket,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,
    Finset.mem_univ,ite_true]

theorem close_eq (x : Input S D m → Bool) (z : Output M H m → Bool)
    (hit : ∀ z', TypedWiring.value (network near far) (Sum.elim x z') = if z=z' then 1 else 0)
    (oracle : (Q → Bool) → F) :
    close (cut near far lane) oracle x = ∏ i, closeLane lane oracle (readOut z i) := by
  unfold close closeLane
  simp_rw [cut_eval near far lane x z hit,←Finset.prod_mul_distrib]
  rw [Fintype.prod_sum]
  apply Fintype.sum_equiv (Equiv.curry (Fin M) Q Bool)
  intro v
  rfl

private theorem row_product {s w : ℕ} (z : RecordPins s w → Bool) (f : (Fin w → Bool) → F) :
    (∏ i, if z (i,none) = true then f (fun j => z (i,some j)) else 1) =
      ((payloads z).map f).prod := by
  rw [←Finset.prod_filter]
  unfold payloads
  rw [Multiset.map_map]
  rfl

/-- Every occupied candidate pays one module factor. The output may contain
equal pairs of lists, and the product uses their full multiplicities. -/
theorem physical_product (x : Input S D m → Bool) (y : Bus S H m → Bool) (z : Output M H m → Bool)
    (preserves : payloads z = payloads (packedPairs x y)) (blanks : ZeroBlanks z)
    (f : (Option (Pair H m) → Bool) → F) (idle : f (fun _ => false) = 1) :
    (∏ i, f (readOut z i)) = ∏ s, if x (.inl s) = true then
      f (fun p => p.elim true (fun t => y (s,t))) else 1 := by
  let g (bits : Fin (Width H m) → Bool) := f (fun p => p.elim true (bits ∘ Fintype.equivFin _))
  have normalize i : f (readOut z i) =
      (if z (i,none) = true then g (fun j => z (i,some j)) else 1) := by
    cases hb : z (i,none) with
    | true =>
      simp only [ite_true]
      apply congrArg f
      funext p; cases p <;> simp [readOut,hb]
    | false =>
      have he : readOut z i = fun _ => false := by
        funext p; cases p with
        | none => exact hb
        | some p => exact blanks _ hb _
      simpa only [he,Bool.false_eq_true,ite_false] using idle
  simp_rw [normalize]
  rw [row_product,preserves,←row_product]
  apply Finset.prod_congr rfl
  intro s _
  have hw : g (fun j => packedPairs x y (s,some j)) =
      f (fun p => p.elim true (fun t => y (s,t))) := by
    apply congrArg f
    funext p; cases p <;> simp [packedPairs]
  by_cases occupied : x (.inl s)=true
  · simp only [packedPairs,occupied,ite_true]
    exact hw
  · simp [packedPairs,occupied]

end Hierarchy.TaggedShorterBank

end
end OAI
