import OAI.Hierarchy.TaggedData
import OAI.Computability.VPVNP.LiveHeaderBits
import OAI.ThreeFlat.Routing.BitonicSortNetwork
import OAI.ThreeFlat.Routing.CompareWord
import OAI.ThreeFlat.Routing.TypedWiring

namespace OAI
/-! # An exact network for the exposed tagged permutation

The sorter reads a target payload in the low bits and its tag in the high bits.
Its proposed output at position `i` reads the source payload and the constant
binary address `i`. The sorted tags therefore check bijectivity, and the
sorted payloads check every prescribed match.
-/

noncomputable section
namespace Hierarchy.Tagged.Exact

open ThreeFlat Routing
open LinearAlgebra.SpectralBooks.Batcher
open SortNetwork (Payload Records pack)
open Computability.VPVNP.RAMSerialization (wordBits)
open scoped Classical

variable {h w : ℕ}

/-- The payload occupies the low bits and the tag occupies the high bits. -/
def row (payload : Bits w) (a : Row h) : Bits (w+h) :=
  Fin.append payload (wordBits h a)

private theorem address_wordBits (a : Row h) : addressEquiv h (wordBits h a) = a := by
  apply (addressEquiv h).symm.injective
  rw [Equiv.symm_apply_apply]
  funext j
  exact (Computability.VPVNP.LiveHeader.testBit_wordBits a j).symm

private theorem row_inj {x y : Bits w} {a b : Row h} (he : row x a = row y b) :
    x = y ∧ a = b := by
  refine ⟨funext fun i => ?_, (wordBits h).injective (funext fun j => ?_)⟩
  · simpa only [row, Fin.append_left] using congrFun he (Fin.castAdd h i)
  · simpa only [row, Fin.append_right] using congrFun he (Fin.natAdd w j)

private theorem ordered (s : Row h → Bits w) :
    StrictMono (fun i => addressEquiv (w+h) (row (s i) i)) := by
  intro i j hij
  change (addressEquiv _ _).val < (addressEquiv _ _).val
  simp only [← wordValue_addressEquiv, row, wordValue_append_lt_iff,
    Prod.Lex.toLex_lt_toLex, address_wordBits]
  exact Or.inl hij

/-- The sorted target records equal the prescribed source records exactly for
a bijective tag assignment carrying each target payload from its source. -/
theorem sorted_iff (s : Row h → Bits w) (a : Row h → Row h) (t : Row h → Bits w) :
    (fun i => row (s i) i) = BitonicSort.sorted (fun i => row (t i) (a i)) ↔
      Valid s a t := by
  let X (i : Row h) := addressEquiv (w+h) (row (t i) (a i))
  let Y (i : Row h) := addressEquiv (w+h) (row (s i) i)
  have sorted : (fun i => row (s i) i) = BitonicSort.sorted (fun i => row (t i) (a i)) ↔
      Y = (sortNet h).eval X := by
    constructor
    · intro he
      funext i
      simpa only [BitonicSort.sorted, BitonicSchedule.sorted, Equiv.apply_symm_apply, X, Y] using
        congrArg (addressEquiv (w+h)) (congrFun he i)
    · intro he
      funext i
      apply (addressEquiv (w+h)).injective
      simpa only [BitonicSort.sorted, BitonicSchedule.sorted, Equiv.apply_symm_apply, X, Y] using
        congrFun he i
  rw [sorted]
  obtain ⟨mono, e, perm⟩ := sortNet_correct X
  constructor
  · intro he
    have matchRow (i : Row h) : row (s i) i = row (t (e i)) (a (e i)) :=
      (addressEquiv _).injective (congrFun (he.trans perm) i)
    have tagEq : a = ⇑e.symm := by
      funext j
      simpa using (row_inj (matchRow (e.symm j))).2.symm
    constructor
    · rw [tagEq]
      exact e.symm.bijective
    · intro j
      rw [tagEq]
      simpa using (row_inj (matchRow (e.symm j))).1.symm
  · rintro ⟨bij, agree⟩
    let p := Equiv.ofBijective a bij
    have hX : X = Y ∘ p := funext fun i =>
      congrArg (addressEquiv _) (congrArg (fun z => row z (a i)) (agree i))
    have pX : (List.ofFn X).Perm (List.ofFn Y) := by
      rw [hX]
      exact Equiv.Perm.ofFn_comp_perm p Y
    have pSort : (List.ofFn ((sortNet h).eval X)).Perm (List.ofFn X) := by
      rw [perm]
      exact e.ofFn_comp_perm X
    apply List.ofFn_injective
    exact (pX.symm.trans pSort.symm).eq_of_pairwise' (ordered s).monotone.sortedLE_ofFn.pairwise
      mono.sortedLE_ofFn.pairwise

private def inputBit {h w : ℕ} (i : Row h) : Fin (w+h) → BitSource 0 (pins h w) :=
  Fin.append (fun j => .pin (portIndex h w (.inr (.inr (i,j)))))
    (fun j => .pin (portIndex h w (.inr (.inl (i,j)))))

private def outputBit {h w : ℕ} (i : Row h) : Fin (w+h) → BitSource 0 (pins h w) :=
  Fin.append (fun j => .pin (portIndex h w (.inl (i,j))))
    (fun j => .constant (wordBits h i j))

private def wire (h w : ℕ) :
    Fin (Fintype.card (Payload h (w+h)) + Fintype.card (Payload h (w+h))) →
      BitSource 0 (pins h w) :=
  let addr := (Fintype.equivFin (Payload h (w+h))).symm
  Fin.append (fun j => inputBit (addr j).1 (addr j).2)
    (fun j => outputBit (addr j).1 (addr j).2)

/-- An exact bitonic network with source, tag, and target ports in row-major order. -/
def network (F : Type*) [Zero F] [One F] (h w : ℕ) : BitNetwork F (pins h w) :=
  BitNetwork.glue (fun _ : Unit => BitonicSort.network F h (w+h)) (fun _ => wire h w)

private theorem input_read {h w : ℕ} (x : Fin (pins h w) → Bool) (hid : Fin 0 → Bool)
    (i : Row h) (j : Fin (w+h)) :
    (inputBit i j).read hid x = Fin.append (target x i) (wordBits h (tag x i)) j := by
  cases j using Fin.addCases <;>
    simp [inputBit, target, tag, BitSource.read, -Fin.natAdd_eq_addNat]

private theorem output_read {h w : ℕ} (x : Fin (pins h w) → Bool) (hid : Fin 0 → Bool)
    (i : Row h) (j : Fin (w+h)) :
    (outputBit i j).read hid x = Fin.append (source x i) (wordBits h i) j := by
  cases j using Fin.addCases <;>
    simp [outputBit, source, BitSource.read, -Fin.natAdd_eq_addNat]

private theorem wire_read {h w : ℕ} (x : Fin (pins h w) → Bool) (hid : Fin 0 → Bool) :
    (fun j => (wire h w j).read hid x) =
      Fin.append (pack (fun i => Fin.append (target x i) (wordBits h (tag x i))))
        (pack (fun i => Fin.append (source x i) (wordBits h i))) := by
  funext j
  cases j using Fin.addCases <;>
    simp [wire, pack, Function.uncurry, input_read, output_read, -Fin.natAdd_eq_addNat]

private theorem network_eval_sort (F : Type*) [CommSemiring F] (h w : ℕ)
    (x : Fin (pins h w) → Bool) :
    (network F h w).eval x = if (fun i => Fin.append (source x i) (wordBits h i)) =
        BitonicSort.sorted (fun i => Fin.append (target x i) (wordBits h (tag x i))) then 1 else 0 := by
  simp [network, BitNetwork.glue_eval, wire_read, BitonicSort.network_eval]

theorem network_size (F : Type*) [Zero F] [One F] (h w : ℕ) :
    (network F h w).cells + (network F h w).internal ≤
      8192*(w+h+1)*2^h*(h+1)^2 := by
  have hc := BitonicSort.network_cells F h (w+h)
  have hi := BitonicSort.network_internal F h (w+h)
  simp only [network, BitNetwork.glue_cells, BitNetwork.glue_internal, Fintype.sum_unique, zero_add]
  nlinarith only [hc,hi]

/-- Reindex the same exposed network for the finite-label correction interface. -/
def typedNetwork (F : Type*) [Zero F] [One F] (h w : ℕ) :
    BitNetwork F (Fintype.card (Fin (pins h w))) :=
  BitNetwork.glue (fun _ : Unit => network F h w)
    (fun _ j => (BitSource.pin (Fintype.equivFin _ j) : BitSource 0 _))

private theorem typedNetwork_value_eq (F : Type*) [CommSemiring F] (h w : ℕ)
    (x : Fin (pins h w) → Bool) : TypedWiring.value (typedNetwork F h w) x =
      (network F h w).eval x := by
  simp [TypedWiring.value, typedNetwork, BitNetwork.glue_eval, BitSource.read]

theorem typedNetwork_size (F : Type*) [Zero F] [One F] (h w : ℕ) :
    (typedNetwork F h w).cells + (typedNetwork F h w).internal ≤
      8192*(w+h+1)*2^h*(h+1)^2 := by
  simpa [typedNetwork] using network_size F h w

/-- Correctness over every commutative semiring, including every field. -/
theorem network_eval (F : Type*) [CommSemiring F] (h w : ℕ)
    (x : Fin (pins h w) → Bool) : (network F h w).eval x = coeff F h w x := by
  rw [network_eval_sort]
  change (if (fun i => row (source x i) i) = BitonicSort.sorted
      (fun i => row (target x i) (tag x i)) then (1 : F) else 0) = _
  simp only [sorted_iff, coeff]

/-- The typed form computes exactly the function supplied to the correction module. -/
theorem typedNetwork_value (F : Type*) [CommSemiring F] (h w : ℕ)
    (x : Fin (pins h w) → Bool) : TypedWiring.value (typedNetwork F h w) x = coeff F h w x :=
  (typedNetwork_value_eq F h w x).trans (network_eval F h w x)


end Hierarchy.Tagged.Exact

end
end OAI
