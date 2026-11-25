import OAI.Computability.NearSquareRoot.CRTControlledFlatGateKey
import OAI.Computability.NearSquareRoot.PrecisionWalshWidth
import OAI.Computability.IntegerMultiplication.Code.Pace

/-! # Materializing the headers of a flat swap program -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled
open IntegerMultiplication IntegerMultiplication.Code NearSquareRoot.Space

/-- Shared register width together with the two positions of each move. -/
def flatSwapInput (k : ℕ) (moves : List (Fin k × Fin k)) : Tally × List (Tally × Tally) :=
  (tally k, moves.map (fun z => (tally z.1.val, tally z.2.val)))

/-- Each gate receives the register width and its ordered little-endian positions. -/
def flatSwapKeys (k : ℕ) (moves : List (Fin k × Fin k)) : List (Tally × Tally × Tally) :=
  moves.map fun z => (tally k,tally (max z.1.val z.2.val),tally (min z.1.val z.2.val))

private def orderedKey (q : Tally × Tally × Tally) : Tally × Tally × Tally :=
  let clipped := cutLists q.2
  (q.1, q.2.1 ++ clipped.2, clipped.1)

private theorem orderedKey_easy : Easy orderedKey := by
  have h := easy_cut (show Easy (fun q : Tally × Tally × Tally => q.2) from Easy.snd)
  exact Easy.fst.pair ((((show Easy (fun q : Tally × Tally × Tally => q.2.1) by fun_prop).pair
    h.sndCompose).compose Easy.append).pair h.fstCompose)

private theorem orderedKey_values (k a b : ℕ) :
    orderedKey (tally k,tally a,tally b) = (tally k,tally (max a b),tally (min a b)) := by
  simp only [orderedKey,cutLists,tally_length]
  simp only [tally,List.take_replicate,List.drop_replicate,← List.replicate_add]
  rw [show a + (b - a) = max a b by omega]

private def buildSwapKeys (backwards : Bool) (q : Tally × List (Tally × Tally)) :=
  let keys := polyPush orderedKey q
  if backwards then keys.reverse else keys

private theorem buildSwapKeys_poly (backwards : Bool) : Poly (buildSwapKeys backwards) := by
  have f := Poly.push ([] : Tally) (([],[]) : Tally × Tally) orderedKey_easy.poly
  cases backwards
  · exact f
  · exact f.rev

private theorem buildSwapKeys_values (backwards : Bool) (k : ℕ) (s : List (Fin k × Fin k)) :
    buildSwapKeys backwards (flatSwapInput k s) = flatSwapKeys k (if backwards then s.reverse else s) := by
  cases backwards <;> simp [buildSwapKeys,flatSwapInput,flatSwapKeys,polyPush,List.map_map,
    Function.comp_def,orderedKey_values,List.map_reverse]

theorem flatSwapKeys_size (k : ℕ) (s : List (Fin k × Fin k)) :
    size (flatSwapKeys k s) ≤ (6*k+6)*s.length + 1 := by
  induction s with
  | nil => rfl
  | cons z s ih =>
    simp only [flatSwapKeys,List.map_cons,size_cons,size_prod,size_tally,tally_length,
      List.length_cons,Nat.mul_succ]
    have hmax := max_le z.1.isLt.le z.2.isLt.le
    have hmin := (min_le_left z.1.val z.2.val).trans z.1.isLt.le
    change size (s.map _) ≤ _ at ih
    omega

private theorem flatSwapInput_size (k : ℕ) (s : List (Fin k × Fin k)) :
    size (flatSwapInput k s) ≤ (4*k+4)*s.length + 2*k+3 := by
  have cap (l : List (Fin k × Fin k)) :
      size (l.map fun z => (tally z.1.val,tally z.2.val)) ≤ (4*k+4)*l.length+1 := by
    induction l with
    | nil => rfl
    | cons z l ih =>
      simp only [List.map_cons,size_cons,size_prod,size_tally,tally_length,List.length_cons,Nat.mul_succ]
      have := z.1.isLt
      have := z.2.isLt
      omega
  simp only [flatSwapInput,size_prod,size_tally,tally_length]
  have := cap s
  omega

/-- All headers, including their list cells, fit a uniform multiple of the
record count whenever the number of transpositions is linear in the bit count. -/
theorem flatSwapKeys_cap (D : ℕ) : ∃ C : ℕ, ∀ (k : ℕ) (moves : List (Fin k × Fin k)),
    moves.length ≤ D*(k+1) → (send (flatSwapKeys k moves)).count ≤ C * 2^k := by
  obtain ⟨A,hA⟩ := polynomial_le_multiple_array_length 2
  refine ⟨(6*D+1)*A, fun k moves h => ?_⟩
  change size (flatSwapKeys k moves) ≤ _
  refine (flatSwapKeys_size k moves).trans ?_
  calc
    _ ≤ (6*k+6)*(D*(k+1))+1 := by gcongr
    _ ≤ (6*D+1)*(k+1)^2 := by nlinarith only [Nat.zero_le (k^2), Nat.zero_le k]
    _ ≤ _ := by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (hA k)

private theorem prepareFlatSwaps (backwards : Bool) {I : Type} (k : I → ℕ)
    (moves : (i:I) → List (Fin (k i) × Fin (k i))) (V : I → ℕ) (data : I → Tree)
    (D : ℕ) (hlen : ∀ i, (moves i).length ≤ D*(k i+1)) (hV : ∀ i, 2^(k i) ≤ V i)
    (hdata : ∀ i, (data i).count ≤ V i) :
    BoundedTask V V (fun i => .fork (send (flatSwapInput (k i) (moves i))) (data i))
      (fun i => .fork (send (flatSwapKeys (k i) (if backwards then (moves i).reverse else moves i))) (data i)) := by
  let header i := flatSwapInput (k i) (moves i)
  have src : Dom k (fun i => size (header i)) := by
    refine ⟨2,4*D+3,fun i => ?_⟩
    calc
      _ ≤ (4*k i+4)*(moves i).length + 2*k i+3 := flatSwapInput_size ..
      _ ≤ (4*k i+4)*(D*(k i+1)) + 2*k i+3 := by gcongr; exact hlen i
      _ ≤ _ := by nlinarith only [Nat.zero_le ((k i)^2), Nat.zero_le (k i)]
  have charge {t : I → ℕ} (h : Dom k t) : ∃ A : ℕ, ∀ i, t i ≤ A*V i := by
    obtain ⟨d,C,hh⟩ := h
    obtain ⟨E,he⟩ := polynomial_le_multiple_array_length d
    refine ⟨C*E,fun i => ?_⟩
    rw [Nat.mul_assoc]
    exact (hh i).trans (Nat.mul_le_mul_left _ ((he (k i)).trans (Nat.mul_le_mul_left _ (hV i))))
  obtain ⟨t,ht,prog⟩ := (buildSwapKeys_poly backwards).on (q := header) src
  obtain ⟨A,htime⟩ := charge ht
  obtain ⟨B,hsmall⟩ := charge src
  have hpos (i : I) : 1 ≤ V i := (Nat.two_pow_pos _).trans_le (hV i)
  have hh : Carries (fun i => (V i : ℝ)) (fun i => send (header i))
      (fun i => send (buildSwapKeys backwards (header i))) := by
    refine ⟨(Sized.natural prog).adapts (fun i => by exact_mod_cast hpos i) (A+1) ?_,B,?_⟩
    · intro i
      have := htime i
      have := hpos i
      exact_mod_cast (by rw [Nat.succ_mul]; omega : t i + 1 ≤ (A+1)*V i)
    · intro i
      change (size (header i) : ℝ) ≤ (B : ℝ) * (V i : ℝ)
      exact_mod_cast hsmall i
  have saved : Volume (fun i => (V i : ℝ)) data :=
    ⟨1,fun i => by simpa only [Nat.cast_one,one_mul] using Nat.cast_le.mpr (hdata i)⟩
  simpa only [header,buildSwapKeys_values] using boundedOfCarries (hh.first saved)

theorem prepareFlatSwapList {I : Type} (k : I → ℕ)
    (moves : (i:I) → List (Fin (k i) × Fin (k i))) (V : I → ℕ) (data : I → Tree)
    (D : ℕ) (hlen : ∀ i, (moves i).length ≤ D*(k i+1)) (hV : ∀ i, 2^(k i) ≤ V i)
    (hdata : ∀ i, (data i).count ≤ V i) :
    BoundedTask V V (fun i => .fork (send (flatSwapInput (k i) (moves i))) (data i))
      (fun i => .fork (send (flatSwapKeys (k i) (moves i))) (data i)) :=
  prepareFlatSwaps false k moves V data D hlen hV hdata

theorem prepareFlatSwapListReverse {I : Type} (k : I → ℕ)
    (moves : (i:I) → List (Fin (k i) × Fin (k i))) (V : I → ℕ) (data : I → Tree)
    (D : ℕ) (hlen : ∀ i, (moves i).length ≤ D*(k i+1)) (hV : ∀ i, 2^(k i) ≤ V i)
    (hdata : ∀ i, (data i).count ≤ V i) :
    BoundedTask V V (fun i => .fork (send (flatSwapInput (k i) (moves i))) (data i))
      (fun i => .fork (send (flatSwapKeys (k i) (moves i).reverse)) (data i)) :=
  prepareFlatSwaps true k moves V data D hlen hV hdata

end Controlled

end NearSquareRoot
end Computability
end OAI
