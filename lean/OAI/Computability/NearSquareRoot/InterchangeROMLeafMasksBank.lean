import OAI.Computability.NearSquareRoot.InterchangeROMLeaf
import OAI.Computability.NearSquareRoot.InterchangeBQuestLocal
import OAI.Computability.NearSquareRoot.PrecisionCartesian
import OAI.Computability.IntegerMultiplication.Code.Iter

/-! # Generating the leaf mask queries in lexicographic rank order -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMLeafMasksBank

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  NearSquareRoot.InterchangeSpace NearSquareRoot.Space NearSquareRoot.InterchangeROMLeaf

abbrev Header := Tally × Tally × Tally × Tally × Tally
abbrev MaskQuery := Header × Tally × Tally

/-- Source and destination comparison queries for every ordered pair of ranks. -/
def queries (h : Header) : List (MaskQuery × MaskQuery) :=
  (ranks h.2.1.length).tab fun z =>
    ((h,tally z.1.val,tally z.2.val),(h,tally z.2.val,tally z.1.val))

private def rankPairs (d : Tally) := (Iter.lineup d).flatMap fun u =>
  (Iter.lineup d).map fun v => (u,v)

private theorem polynomialPairs : Poly rankPairs := by
  have cart := Cartesian.cartesianAll (X:=Tally) (Y:=Tally)
  have cc := Poly.of_bound cart (show Dom size _ from by
    refine ⟨2,2,fun s => ?_⟩
    have x : size s.1 ≤ size s+1 := by simp only [size_prod]; omega
    have y : size s.2 ≤ size s+1 := by simp only [size_prod]; omega
    have xl : s.1.length+1 ≤ size s+1 := (duration s.1).trans_le x
    have yl : s.2.length+1 ≤ size s+1 := (duration s.2).trans_le y
    have a := Nat.mul_le_mul x yl
    have b := Nat.mul_le_mul y xl
    change size s.1*(s.2.length+1) + size s.2*(s.1.length+1) ≤ _
    rw [sq]; omega)
  exact (Iter.poly_line.pair Iter.poly_line).compose cc

private def both (r : (Tally × Tally) × Header) : MaskQuery × MaskQuery :=
  ((r.2,r.1.1,r.1.2),(r.2,r.1.2,r.1.1))

private theorem rows_eq (h : Header) :
    ((rankPairs h.2.1).map (fun z => (z,h))).map both = queries h := by
  unfold queries ranks
  rw [Series.grouped]
  simp only [rankPairs,Iter.lineup,List.ofFn_eq_map,Series.natural,Series.tab,Series.fixed,
    List.flatMap_def,List.map_flatten,List.map_map,Function.comp_def,both]

private theorem scaled {I : Type} {fuel t : I → ℕ} {p q : I → Tree}
    (cmd : Task t p q) (C : ℕ) (ht : ∀ i, t i ≤ C*fuel i) :
    Sized (fun i => (fuel i:ℝ)+1) p q := by
  apply (Sized.natural cmd).adapts (fun i => by simp) (C+1)
  intro i
  have x : t i + 1 ≤ (C+1)*(fuel i+1) := by
    have := ht i
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    omega
  exact_mod_cast x

def cost (k : ℕ) (h : Header) := (h.2.1.length+1)^k * (size h+1)

/-- Only the rank dimension enters the polynomial. The other four tallies
contribute their serialized size once per generated descriptor. -/
theorem prepare : ∃ k, BoundedTask (cost k) (cost k) send (fun h => send (queries h)) := by
  have ds : Dom List.length (fun d : Tally => size d) :=
    ⟨1,2,fun d => by simp [size_tally]⟩
  obtain ⟨t,dt,run⟩ := polynomialPairs
  obtain ⟨k,C,cap⟩ := (((dt.add polynomialPairs.length).add (Dom.const size 1)).sub ds)
  let fuel := cost k
  let budget (h : Header) : ℝ := (fuel h:ℝ)+1
  have one (h : Header) : 1 ≤ budget h := by simp [budget]
  have hdr (h : Header) : size h ≤ fuel h := by
    exact (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (pow_pos (Nat.succ_pos _) _))
  have small : Volume budget (send (X:=Header)) := by
    refine ⟨1,fun h => ?_⟩
    change (size h:ℝ) ≤ ((1:ℕ):ℝ)*budget h
    simp only [Nat.cast_one,one_mul,budget]
    exact_mod_cast (hdr h).trans (Nat.le_succ _)
  have introPair := Carries.func one small (fun h : Header => (h.2.1,h)) (by fun_prop)
  have left := (run.on (fun h : Header => h.2.1)).left (fun h => send h)
  have ty (h : Header) : t h.2.1 + size (rankPairs h.2.1) + 1 ≤ C*(h.2.1.length+1)^k := cap _
  have top : Carries budget send (fun h : Header => send (rankPairs h.2.1,h)) := by
    apply introPair.sequence (scaled left C (fun h => ?_))
    exact (Nat.le_add_right _ _ |>.trans (Nat.le_succ _) |>.trans (ty h)).trans
      (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)))
  have broadcast := Cartesian.broadcastRight.on (fun h : Header => (rankPairs h.2.1,h))
  have dup := top.sequence (scaled broadcast C (fun h => by
    let v := rankPairs h.2.1
    have n : v.length + 1 ≤ size v := duration v
    have x : size v ≤ C*(h.2.1.length+1)^k := by have := ty h; dsimp only [v]; omega
    change size v + (v.length+1)*size h ≤ C*((h.2.1.length+1)^k*(size h+1))
    rw [← Nat.mul_assoc,Nat.mul_add,Nat.mul_one]
    exact Nat.add_le_add x (Nat.mul_le_mul_right _ (n.trans x)) |>.trans (Nat.add_comm ..).le))
  have arrange : Easy (List.map both) := Easy.mapping (show Easy both from by unfold both; fun_prop)
  have bank := carries_bounded (dup.chain (Carries.func one dup.out (List.map both) arrange))
  have ce (h : Header) : ⌈budget h⌉₊ = fuel h+1 := by
    change ⌈(fuel h:ℝ)+1⌉₊ = fuel h+1
    rw [← Nat.cast_add_one,Nat.ceil_natCast]
  have fit h : ⌈budget h⌉₊+1 ≤ 2*(fuel h+1) := by rw [ce]; omega
  exact ⟨k,(bank.bound 2 2 fit fit).conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun h => congrArg send (rows_eq h))⟩

end InterchangeROMLeafMasksBank

end NearSquareRoot
end Computability
end OAI
