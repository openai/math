import OAI.Computability.NearSquareRoot.CRTControlledFlatNumber
import OAI.Computability.IntegerMultiplication.Wave.Ordinal
import OAI.Computability.NearSquareRoot.InterchangeBoundedRectangular

/-! # Ordinals of the two wings in a rectangular interchange

The physical stock places its two active words on opposite sides of a fixed
gap. Each other coordinate may itself have an arbitrary mixed-radix layout.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.SwapOrdinal

open IntegerMultiplication Strip Strip.Dims Loom Adic Controlled Code InterchangePayload

/-- Row-major address with equal active dimensions `H` and spectator dimensions
`G` and `B` between and after them. -/
def rank (H G B p u g v b : ℕ) : ℕ := (((p*H+u)*G+g)*H+v)*B+b

/-- Source address obtained by interchanging the two active fields. -/
def source (H G B n : ℕ) : ℕ :=
  rank H G B (n/B/H/G/H) (n/B%H) (n/B/H%G) (n/B/H/G%H) (n%B)

private theorem div_digit {m x y : ℕ} (h : y < m) : (x*m+y)/m = x := by
  rw [Nat.mul_comm x m,Nat.mul_add_div (Nat.zero_lt_of_lt h), Nat.div_eq_of_lt h,Nat.add_zero]

private theorem mod_digit {m x y : ℕ} (h : y < m) : (x*m+y)%m = y := by
  rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt h]

theorem source_rank {H G B p u g v b : ℕ} (hu : u<H) (hg : g<G) (hv : v<H) (hb : b<B) :
    source H G B (rank H G B p u g v b) = rank H G B p v g u b := by
  simp only [source,rank,div_digit hb, mod_digit hb, div_digit hv, mod_digit hv,
    div_digit hg, mod_digit hg, div_digit hu, mod_digit hu]

/-- A rectangular swap preserves each prefix, hence every initial segment
consisting of complete prefix groups. -/
theorem source_lt_iff (H G B p n : ℕ) (hH : 0 < H) (hG : 0 < G) (hB : 0 < B) :
    source H G B n < p*H*G*H*B ↔ n < p*H*G*H*B := by
  have head_eq : source H G B n / B / H / G / H = n/B/H/G/H := by
    simp only [source,rank,div_digit (Nat.mod_lt _ hB),div_digit (Nat.mod_lt _ hH),
      div_digit (Nat.mod_lt _ hG)]
  rw [← Nat.div_lt_iff_lt_mul hB,← Nat.div_lt_iff_lt_mul hH,
      ← Nat.div_lt_iff_lt_mul hG,← Nat.div_lt_iff_lt_mul hH,head_eq,
      Nat.div_lt_iff_lt_mul hH,Nat.div_lt_iff_lt_mul hG,
      Nat.div_lt_iff_lt_mul hH,Nat.div_lt_iff_lt_mul hB]

/-- A zero-extended stream may be cropped at the original prefix boundary,
even if the original number of groups has no dyadic representation. -/
theorem binary_source_lt_iff (lo hi w stride p n : ℕ) (hs : 0 < stride) (apart : lo+w ≤ hi) :
    source (2^w) (2^(hi-(lo+w))) (2^lo*stride) n < p*2^(hi+w)*stride ↔
      n < p*2^(hi+w)*stride := by
  have eq : p*2^w*2^(hi-(lo+w))*2^w*(2^lo*stride) = p*2^(hi+w)*stride := by
    rw [Nat.mul_assoc p, ← pow_add, Nat.mul_assoc p, ← pow_add, ← Nat.mul_assoc,
      Nat.mul_assoc p, ← pow_add, show w+(hi-(lo+w))+w+lo=hi+w by omega]
  simpa only [eq] using source_lt_iff (2^w) (2^(hi-(lo+w))) (2^lo*stride) p n
    (Nat.two_pow_pos _) (Nat.two_pow_pos _) (Nat.mul_pos (Nat.two_pow_pos _) hs)

/-- Additional high address bits within each prefix group may also be left
in place. This form uses the total active width of a Walsh node directly. -/
theorem binary_source_lt_full (lo hi w K stride groups n : ℕ) (hs : 0 < stride)
    (apart : lo+w ≤ hi) (inside : hi+w ≤ K) :
    source (2^w) (2^(hi-(lo+w))) (2^lo*stride) n < groups*2^K*stride ↔
      n < groups*2^K*stride := by
  have e : groups*2^(K-(hi+w))*2^(hi+w)*stride = groups*2^K*stride := by
    rw [Nat.mul_assoc groups, ← pow_add, Nat.sub_add_cancel inside]
  simpa only [e] using binary_source_lt_iff lo hi w stride (groups*2^(K-(hi+w))) n hs apart

/-- Exact number of rows including all spectator fields. -/
theorem stock_count (P G B : Tape) (h : ℕ) :
    (stock 2 P G B h).count = room P * 2^h * room G * 2^h * room B := by
  simp only [stock,Loom.Path,Board,Series.count_cart,space,show room (field 2 h) = 2^h from (space _).symm.trans (lineSize _ _)]
  ring

/-- The series index of a boxed coordinate is its row-major ordinal. -/
theorem index_rank {P G B : Tape} {h : ℕ} (x : SpanKey P G B (Block 2 h)) :
    ((stock 2 P G B h).index x).val =
      rank (2^h) (room G) (room B) ((layout P).index x.1).val (number x.2.1)
        ((layout G).index x.2.2.1).val (number x.2.2.2.1) ((layout B).index x.2.2.2.2).val := by
  obtain ⟨p,u,g,v,b⟩ := x
  simp only [stock,Loom.Path,Board,Wave.cart_rank,Series.count_cart,space,show room (field 2 h) = 2^h from (space _).symm.trans (lineSize _ _),
    lineIndex_number,rank]
  ring

theorem index_swapper {P G B : Tape} {h : ℕ} (x : SpanKey P G B (Block 2 h)) :
    ((stock 2 P G B h).index (swapper _ _ _ x)).val =
      source (2^h) (room G) (room B) ((stock 2 P G B h).index x).val := by
  obtain ⟨p,u,g,v,b⟩ := x
  rw [index_rank,index_rank]
  exact (source_rank (number_lt u) (by simpa only [space] using ((layout G).index g).isLt)
    (number_lt v) (by simpa only [space] using ((layout B).index b).isLt)).symm

/-- A series tabulated by physical index spells the ordinary stream of increasing ordinals. -/
theorem tab_range {A R : Type} (s : Series A) (f : ℕ → R) :
    s.tab (fun a => f (s.index a).val) = (List.range s.count).map f := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have h : i < s.count := by simpa using hi
    rw [s.get _ ⟨i,h⟩ hi]
    simp

/-- The raw interchange output is the gridded stream with the two active
coordinates exchanged at every ordinary array address. -/
theorem tab_swapped {R : Type} (P G B : Tape) (h : ℕ) (f : ℕ → R) :
    let s := stock 2 P G B h
    s.tab (fun a => f (s.index (swapper _ _ _ a)).val) =
      (List.range s.count).map (f ∘ source (2^h) (room G) (room B)) := by
  dsimp only
  simp_rw [index_swapper]
  exact tab_range (stock 2 P G B h) (f ∘ source (2^h) (room G) (room B))

/-- The bounded rectangular command directly on ordinary streams of packed
bits. Its source index and its list representation agree with the array
ordinal above even when one of the active words has no bits. -/
theorem bounded_range {I : Type} {r : Regime I} {α : ℝ} (hα : 1/2 < α)
    (P G B : I → Tape) (n : I → ℕ) (hn : r.Has (tally ∘ n))
    (hp : Told r P) (hg : Told r G) (hb : Told r B)
    (guard : ∀ i d, d ∈ P i ++ G i ++ B i → d ≤ Net.Shuttle.base)
    (L width : I → ℕ) (bound : ∀ i, width i ≤ L i) (v : I → ℕ → List Bool)
    (hw : ∀ i j, j < (stock 2 (P i) (G i) (B i) (n i)).count → (v i j).length = width i) :
    let N i := (stock 2 (P i) (G i) (B i) (n i)).count
    BoundedBreeze (Spindle.modes n (τ:=α)) r N L
      (fun i => .fork (r.header i) (send ((List.range (N i)).map (v i))))
      (fun i => send ((List.range (N i)).map
        (v i ∘ source (2^(n i)) (room (G i)) (room (B i))))) := by
  let s i := stock 2 (P i) (G i) (B i) (n i)
  have run := bounded_bitstrings P G B n (nearRoot_bounded_rectInterchange hα r n)
    hn hp hg hb guard L width bound (fun i a => v i ((s i).index a).val)
    (fun i a => hw i _ ((s i).index a).isLt)
  unfold stackRun together at run
  simp_rw [stripe_eq'] at run
  simpa only [s,tab_range,tab_swapped] using run

end PhysicalWalshNode.SwapOrdinal

end NearSquareRoot
end Computability
end OAI
