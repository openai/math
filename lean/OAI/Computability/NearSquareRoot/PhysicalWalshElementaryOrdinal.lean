import OAI.Computability.NearSquareRoot.PhysicalWalshElementaryGate

/-! # Physical ordinal of a four-lane address-bit gate -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.ElementaryGate

open IntegerMultiplication Code Space

/-- Rank in prefix, high bit, gap, low bit, suffix order. -/
def rank (G B p h g l b : ℕ) := (((p*2+h)*G+g)*2+l)*B+b

def cells {R : Type} (P G B : ℕ) (x : ℕ → R) : Cell P G R := fun p h g l =>
  List.ofFn fun b : Fin B => x (rank G B p h g l b)

/-- Source ordinal of a physical gate output. -/
def natAction (G B : ℕ) (σ : Bits2 → Bits2) (n : ℕ) :=
  let lo : Fin 2 := ⟨n/B%2,Nat.mod_lt _ (by decide)⟩
  let hi : Fin 2 := ⟨n/B/2/G%2,Nat.mod_lt _ (by decide)⟩
  let t := σ (hi,lo)
  rank G B (n/B/2/G/2) t.1 (n/B/2%G) t.2 (n%B)

private theorem div_digit (n k j : ℕ) (hj : j < k) : (n*k+j)/k = n := by
  rw [Nat.mul_comm n k,Nat.mul_add_div (Nat.zero_lt_of_lt hj),Nat.div_eq_of_lt hj,Nat.add_zero]

private theorem mod_digit (n k j : ℕ) (hj : j < k) : (n*k+j)%k = j := by
  rw [Nat.mul_comm n k,Nat.mul_add_mod,Nat.mod_eq_of_lt hj]

theorem natAction_rank {P G B : ℕ} (σ : Bits2 → Bits2) (p : Fin P) (h : Fin 2) (g : Fin G) (l : Fin 2) (b : Fin B) :
    natAction G B σ (rank G B p h g l b) = rank G B p (σ (h,l)).1 g (σ (h,l)).2 b := by
  simp only [natAction,rank,div_digit _ _ _ b.isLt,mod_digit _ _ _ b.isLt,div_digit _ _ _ l.isLt,
    mod_digit _ _ _ l.isLt,div_digit _ _ _ g.isLt,mod_digit _ _ _ g.isLt,
    div_digit _ _ _ h.isLt,mod_digit _ _ _ h.isLt]

theorem flat_cells {R : Type} (P G B : ℕ) (x : ℕ → R) :
    flat P G (cells P G B x) = (List.range (P*2*G*2*B)).map x := by
  change ChildLanes.stream (List.finRange P) (fun p h => ChildLanes.stream (List.finRange G)
    (fun g l => List.ofFn fun b : Fin B => x (rank G B p h g l b))) = _
  simp_rw [ChildLanes.stream_rect]
  apply List.ext_getElem
  · simp [Nat.mul_assoc]
  · intro t ht hs
    simp only [List.getElem_ofFn,List.getElem_map,List.getElem_range]
    apply congrArg x
    let r := G*2*B
    change rank G B (t/r/2) (t/r%2) (t%r/B/2) (t%r/B%2) (t%r%B) = t
    have a := Nat.div_add_mod' (t/r) 2
    have b := Nat.div_add_mod' (t%r/B) 2
    unfold rank
    rw [a]
    calc
      _ = t/r*r + (((t%r/B/2)*2+t%r/B%2)*B+t%r%B) := by dsimp only [r]; ring
      _ = t := by rw [b,Nat.div_add_mod',Nat.div_add_mod']

theorem move_cells {R : Type} (P G B : ℕ) (σ : Bits2 → Bits2) (x : ℕ → R) :
    move σ (cells P G B x) = cells P G B (x ∘ natAction G B σ) := by
  funext p h g l
  apply congrArg List.ofFn
  funext b
  exact (congrArg x (natAction_rank σ p h g l b)).symm

/-- Run the two-bit rewiring on the single list used by the Walsh node. -/
theorem boundedOrdinal {I R : Type} [Codec R] (σ : Bits2 → Bits2) (P G B : I → ℕ) (x : I → ℕ → R) :
    let row i (f : ℕ → R) := (List.range (P i*2*G i*2*B i)).map f
    let h i := header (P i) (G i) (B i)
    let V i := budget (P i) (G i) (B i) (size (row i (x i)))
    BoundedTask V V (fun i => send (h i,row i (x i)))
      (fun i => send (h i,row i ((x i) ∘ natAction (G i) (B i) σ))) := by
  simpa only [move_cells,flat_cells] using
    bounded σ P G B (fun i => cells (P i) (G i) (B i) (x i)) (fun _ _ _ _ _ => List.length_ofFn)

end PhysicalWalsh.ElementaryGate

end NearSquareRoot
end Computability
end OAI
