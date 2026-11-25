import OAI.Computability.NearSquareRoot.SynchronizedRadixAddressTape
import OAI.Computability.IntegerMultiplication.Code.Iter

/-! # Swapping the outer half selector with a radix stage bit on tape

A setup query stores the selector, the unary stage index, and the full
most-significant-first address. Its output spells the permuted address in
the same order. Supplying the output to the same query reverses the swap.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.RadixAddressTape

open IntegerMultiplication Code Bits Net.Walsh

abbrev HalfQuery := Bool × Query

/-- Split before the selected bit and exchange its value with the supplied selector. -/
def halfReply (q : HalfQuery) : Bool × Word :=
  let parts := cutLists q.2
  (parts.2.headD false, parts.1 ++ q.1 :: parts.2.tail)

theorem easy_halfReply : Easy halfReply := by
  have tail : Easy (fun l : Word ↦ l.tail) := by
    suffices eq : (fun l : Word ↦ l.tail) = (fun l ↦
        List.casesOn (motive := fun _ ↦ Word) l [] (fun _ s ↦ s)) from
      eq ▸ Easy.listCase [] Easy.snd
    funext l; cases l <;> rfl
  have parts := easy_cut (Easy.snd (X := Bool) (Y := Query))
  have bit := parts.sndCompose.compose (Iter.leader false)
  have word := easy_append parts.fstCompose
    ((Easy.fst.pair (parts.sndCompose.compose tail)).compose Easy.cons)
  exact bit.pair word

variable {k : ℕ}

private theorem address_withBit (i : Fin k) (r : Fin (2 ^ k)) (b : B) :
    (address r).set i.val (decide (b = 1)) = address (withBit i r b) := by
  apply List.ext_getElem (by simp)
  intro j _ hj
  let a : Fin k := ⟨j, by simpa using hj⟩
  rw [List.getElem_set]
  change (if i.val = a.val then _ else (address r)[a.val]) =
    (address (withBit i r b))[a.val]
  have hd (u : Fin (2 ^ k)) :
      (address u)[a.val]'(by simp) = decide (rankBits u a = 1) := digit_faceWord _ _
  simp only [hd, rankBits_withBit]
  by_cases he : a = i
  · simp [he]
  · have hn : i.val ≠ a.val := fun h ↦ he (Fin.ext h.symm)
    simp [he, hn]

/-- Link the list operation to the physical rank and selector used by the
butterfly permutation, including the MSF position of the bit. -/
theorem halfReply_rank (i : Fin k) (b : B) (r : Fin (2^k)) :
    halfReply (decide (b = 1), tally i.val, address r) =
      let t := swapHalf i (b, r)
      (decide (t.1 = 1), address t.2) := by
  have hi : i.val < (address r).length := by simp
  simp only [halfReply, cutLists, tally_length, List.drop_eq_getElem_cons hi, List.headD_cons,
    List.tail_cons, swapHalf_apply]
  have hword := address_withBit i r b
  rw [List.set_eq_take_append_cons_drop, ite_eq_left hi] at hword
  exact Prod.ext (digit_faceWord _ _) hword

/-- One finite deterministic multitape program generates every half-swap
query's address in polynomially many initial-to-output steps and visited cells. -/
theorem half_queries_on_tapes :
    let X := (k : ℕ) × (Fin k × B × Fin (2 ^ k))
    let query (x : X) : HalfQuery := (decide (x.2.2.1 = 1), tally x.2.1.val, address x.2.2.2)
    let answer (x : X) := swapHalf x.2.1 (x.2.2.1, x.2.2.2)
    PolyTreeMachine (fun x : X ↦ x.1) (fun x ↦ send (query x))
      (fun x ↦ send (decide ((answer x).1 = 1), address (answer x).2)) := by
  dsimp only
  let X := (k : ℕ) × (Fin k × B × Fin (2^k))
  let query (x : X) : HalfQuery := (decide (x.2.2.1 = 1), tally x.2.1.val, address x.2.2.2)
  have hw : Dom (fun x : X ↦ x.1) (fun x ↦ size (query x)) := by
    refine ⟨1, 6, fun x ↦ ?_⟩
    simp only [query, size_prod, size_tally, size_word, tally_length, length_address, pow_one]
    have hbit (b : Bool) : size b = 1 := by cases b <;> rfl
    rw [hbit]
    have hi := x.2.1.isLt
    omega
  have h := polyTreeMachine_of_BT (easy_halfReply.poly.on hw) hw
  simpa only [query, halfReply_rank] using h

/-- The physical query, including input decoding and output, takes linear
time and visited space in the binary address width. -/
theorem half_queries_linear_on_tapes :
    let X := (k : ℕ) × (Fin k × B × Fin (2 ^ k))
    let query (x : X) : HalfQuery := (decide (x.2.2.1 = 1), tally x.2.1.val, address x.2.2.2)
    let answer (x : X) := swapHalf x.2.1 (x.2.2.1, x.2.2.2)
    LinearTreeMachine (fun x : X ↦ x.1 + 1) (fun x ↦ send (query x))
      (fun x ↦ send (decide ((answer x).1 = 1), address (answer x).2)) := by
  dsimp only
  let X := (k : ℕ) × (Fin k × B × Fin (2^k))
  let query (x : X) : HalfQuery := (decide (x.2.2.1 = 1), tally x.2.1.val, address x.2.2.2)
  suffices h : LinearTreeMachine (fun x : X ↦ x.1+1) (fun x ↦ send (query x))
      (fun x ↦ send (halfReply (query x))) by
    simpa only [query, halfReply_rank] using h
  apply linearTreeMachine_of_carries
  apply Carries.func (fun x ↦ by exact_mod_cast Nat.le_add_left 1 x.1) _ _ easy_halfReply
  refine ⟨6, fun x ↦ ?_⟩
  change (size (query x) : ℝ) ≤ (6 : ℕ) * ((x.1 + 1 : ℕ) : ℝ)
  exact_mod_cast (show size (query x) ≤ 6 * (x.1 + 1) by
    simp only [query, size_prod, size_tally, size_word, tally_length, length_address]
    have hbit (b : Bool) : size b = 1 := by cases b <;> rfl
    rw [hbit]
    have hi := x.2.1.isLt
    omega)

end ShortFourier.RadixAddressTape

end NearSquareRoot
end Computability
end OAI
