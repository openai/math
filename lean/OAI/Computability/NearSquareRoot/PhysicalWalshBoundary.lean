import OAI.Computability.NearSquareRoot.PhysicalWalshPieceExecution
import OAI.Computability.NearSquareRoot.PhysicalWalshPaddingSetup
import OAI.Computability.NearSquareRoot.PhysicalWalshPadProjection
import OAI.Computability.NearSquareRoot.BoundedProductRight

/-! # One physical selected-Walsh pass through both padding boundaries

The original descriptor is retained during zero extension. The saved length
survives the variable-time recursive sweep, and the final prefix extraction
restores the compact two-counter header used by the terminal parity branch.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.Pieces

open IntegerMultiplication Code Space

variable {I : Type}

/-- The infinite ordinal presentation of a zero-padded finite record stream. -/
def zeroAfter {Y : Type*} [Zero Y] (n : ℕ) (x : ℕ → Y) (j : ℕ) := if j < n then x j else 0

theorem map_range {Y : Type*} (n : ℕ) (x : ℕ → Y) :
    (List.range n).map x = List.ofFn (fun j : Fin n => x j) := by
  apply List.ext_getElem
  · simp
  · intro j _ _; simp

theorem words_ofFn {w : ℕ} (n : ℕ) (x : ℕ → Dusk.Grain w) :
    words n x = (List.ofFn (fun j : Fin n => x j)).map Dusk.mark := by
  rw [words,← List.map_map,map_range]

theorem words_size {w : ℕ} (n : ℕ) (x : ℕ → Dusk.Grain w) :
    size (words n x) = n*(4*(w+1)+4)+1 := by rw [words_ofFn,Padding.marks_size,List.length_ofFn]

theorem padded_words {w : ℕ} (n e : ℕ) (x : ℕ → Dusk.Grain w) :
    Padding.padded e ((List.range n).map x) = words (n+e) (zeroAfter n x) := by
  rw [map_range,Padding.padded_ofFn,words_ofFn]
  rfl

theorem take_words {w n m : ℕ} (hm : n ≤ m) (x : ℕ → Dusk.Grain w) :
    (((List.range m).map x).take n).map Dusk.mark = words n x := by
  rw [map_range,Padding.take_ofFn hm,words_ofFn]
  rfl

private abbrev H := (Tally × Tally) × Tally
private abbrev R := List Dusk.Pair
def beginPass (p : H × R) := (p.1,(p.1.1,p.2))
def enter (p : H × (Tally × R)) := ((p.1.1,p.2.1),(p.1,p.2.2))
def leavePass (p : ((Tally × Tally) × Tally) × R) := (p.1.1,(p.1.2,p.2))
theorem easy_begin : Easy beginPass := by unfold beginPass; fun_prop
theorem easy_enter : Easy enter := by unfold enter; fun_prop
theorem easy_leave : Easy leavePass := by unfold leavePass; fun_prop

/-- The two saved counters and all six tape scans fit in one boundary budget. -/
theorem boundaryBudget (A W : ℕ) (hw : 0<W) (k s w : I → ℕ) (x y : (i : I) → ℕ → Dusk.Grain (w i))
    (sel : ∀ i,s i≤k i) (occ : ∀ i,PaddingHeader.extra A W (k i) (s i) ≤ 2^k i)
    (t r : I → ℕ) :
    let h i := ((tally (k i),tally (s i)),tally (w i+1))
    let n i := 2^k i
    let m i := extent A W (k i) (s i)
    let V i := n i*(w i+1)
    let init i := (h i,words (n i) (x i))
    let full i := (h i,(tally (n i),words (m i) (zeroAfter (n i) (x i))))
    let tail i := (((h i).1,tally (n i)),words (m i) (y i))
    ∀ i,
      size (init i)+(size (h i)+V i)+size (full i)+(size ((h i).1,tally (n i))+t i)+
      size (tail i)+(size (h i).1+(m i+1)*(w i+1))+1 ≤ 200*(V i+t i+1) ∧
      max (max (max (max (max (size (init i)+size (init i)) (V i+size (h i)))
      (size (full i)+size (full i))) (r i+size ((h i).1,tally (n i)))) (size (tail i)+size (tail i)))
        ((m i+1)*(w i+1)+size (h i).1)+1 ≤ 200*(V i+r i+1) := by
  intro h n m V init full tail i
  let e i := PaddingHeader.extra A W (k i) (s i)
  have mEq (i : I) : n i + e i = m i := Padding.total A hw (sel i)
  have kn : k i < n i := Nat.lt_two_pow_self
  have nn : 0 < n i := Nat.two_pow_pos _
  have nv : n i ≤ V i := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have wv : w i+1 ≤ V i := Nat.le_mul_of_pos_left _ nn
  have mn : m i ≤ 2*(n i) := by have he := occ i; change e i ≤ n i at he; have := mEq i; omega
  have headerSize : size (h i) ≤ 10*V i+8 := by
    have := sel i; simp only [h,size_prod,size_tally,tally_length]; omega
  have keySize : size (h i).1 ≤ 5*V i+3 := by
    have := sel i; simp only [h,size_prod,size_tally,tally_length]; omega
  have ruler : size (tally (n i)) ≤ 2*V i+1 := by rw [size_tally,tally_length]; omega
  have wordsSize (q : ℕ) (hq : q ≤ 2*(n i)) (z : ℕ → Dusk.Grain (w i)) : size (words q z) ≤ 16*V i+1 := by
    rw [words_size]
    have he := Nat.mul_le_mul_right (4*(w i+1)+4) hq
    calc
      _ ≤ 2*(n i)*(4*(w i+1)+4)+1 := Nat.add_le_add_right he _
      _ ≤ _ := by dsimp only [V]; ring_nf; omega
  have start := wordsSize _ (show n i ≤ 2*n i by omega) (x i)
  have padded := wordsSize _ mn (zeroAfter (n i) (x i))
  have stop := wordsSize _ mn (y i)
  have cut : (m i+1)*(w i+1) ≤ 3*V i := by
    exact (Nat.mul_le_mul_right (w i+1) (show m i+1 ≤ 3*n i by omega)).trans_eq (Nat.mul_assoc ..)
  have parked : size ((h i).1,tally (n i)) ≤ 7*V i+5 := by change size (h i).1+size (tally (n i))+1 ≤ _; omega
  have A' : size (init i) ≤ 26*V i+10 := by change size (h i)+size (words (n i) (x i))+1 ≤ _; omega
  have C' : size (full i) ≤ 28*V i+12 := by change size (h i)+(size (tally (n i))+size (words (m i) (zeroAfter (n i) (x i)))+1)+1 ≤ _; omega
  have E' : size (tail i) ≤ 23*V i+8 := by change size ((h i).1,tally (n i))+size (words (m i) (y i))+1 ≤ _; omega
  constructor <;> omega

/-- Add both physical padding boundaries to a recursive sweep on an array in
spectator-row order. The original length, controller generation and output
truncation each cost one original bit volume. The final compact `(k,s)`
header remains available for the odd-bit pass. -/
theorem boundaries (A W : ℕ) (hw : 0<W) (k s w : I → ℕ) (x y : (i : I) → ℕ → Dusk.Grain (w i))
    (sel : ∀ i,s i≤k i) (occ : ∀ i,PaddingHeader.extra A W (k i) (s i) ≤ 2^k i)
    (t r : I → ℕ) :
    let h i := ((tally (k i),tally (s i)),tally (w i+1))
    let n i := 2^k i
    let m i := extent A W (k i) (s i)
    let V i := n i*(w i+1)
    BoundedTask t r (fun i => send (h i,words (m i) (zeroAfter (n i) (x i))))
      (fun i => send (words (m i) (y i))) →
    BoundedTask (fun i => V i+t i) (fun i => V i+r i) (fun i => send (h i,words (n i) (x i)))
      (fun i => send ((tally (k i),tally (s i)),words (n i) (y i))) := by
  intro h n m V sweep
  let e i := PaddingHeader.extra A W (k i) (s i)
  have mEq (i : I) : n i + e i = m i := Padding.total A hw (sel i)
  let init i := (h i,words (n i) (x i))
  let full i := (h i,(tally (n i),words (m i) (zeroAfter (n i) (x i))))
  let tail i := (((h i).1,tally (n i)),words (m i) (y i))
  let f i := (List.range (n i)).map (x i)
  have pad₀ := Padding.appendFromWidths A W k s w f (by intro i; simp [f,n]) sel occ
  have pad : BoundedTask V V (fun i => send ((h i).1,words (n i) (x i)))
      (fun i => send (tally (n i),words (m i) (zeroAfter (n i) (x i)))) := by
    apply pad₀.conform (fun _ => rfl) (fun _ => rfl) _ _
    · intro i; simp only [f,words,List.map_map,h,n]
    · intro i; rw [← mEq i,padded_words]
  have trim₀ := Padding.truncate w n (fun i => (List.range (m i)).map (y i)) (by
    intro i; simp only [List.length_map,List.length_range]; have := mEq i; omega)
  have trim : BoundedTask (fun i => (m i+1)*(w i+1)) (fun i => (m i+1)*(w i+1))
      (fun i => send (tally (n i),words (m i) (y i))) (fun i => send (words (n i) (y i))) := by
    apply trim₀.conform _ _ _ _
    · intro i; simp only [List.length_map,List.length_range]
    · intro i; simp only [List.length_map,List.length_range]
    · intro i; simp only [words,List.map_map]
    · intro i; rw [take_words (show n i ≤ m i by have := mEq i; omega)]
  have a := BoundedTask.of_time (easy_begin.on init)
  have c := BoundedTask.of_time (easy_enter.on full)
  have e' := BoundedTask.of_time (easy_leave.on tail)
  have chain := ((((a.compose (pad.right (fun i => send (h i)))).compose c).compose
    (sweep.right (fun i => send ((h i).1,tally (n i))))).compose e').compose
      (trim.right (fun i => send (h i).1))
  apply chain.bound 200 200
  · exact fun i => (boundaryBudget A W hw k s w x y sel occ t r i).1
  · exact fun i => (boundaryBudget A W hw k s w x y sel occ t r i).2

end PhysicalWalsh.Pieces

end NearSquareRoot
end Computability
end OAI
