import OAI.Computability.NearSquareRoot.InterchangeROMStarsNative
import OAI.Computability.NearSquareRoot.InterchangeROMRecursionThick

/-! # Uniform polynomial for the full-volume batch prelude -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMStars

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Adic IntegerMultiplication.Port
  IntegerMultiplication.Loom InterchangeAddress InterchangeROMAddress InterchangeROMRecursion
  InterchangeROMExpose

private theorem cuts_size (n : ℕ) (xs : List (ℕ × ℕ))
    (h : ∀ p∈xs, p.1≤n ∧ p.2≤n) :
    size (numericSpec 0 n xs).2 ≤ xs.length*(8*n+8)+1 := by
  induction xs with
  | nil => simp [numericSpec,size_nil]
  | cons p ps ih =>
    have left := h p List.mem_cons_self
    have rest := ih (fun p hp => h p (List.mem_cons_of_mem _ hp))
    rcases p with ⟨x,y⟩
    simp only [numericSpec,List.map_cons,List.length_cons,size_cons,size_prod,
      size_tally,tally_length,Nat.add_mul,Nat.one_mul] at *
    omega

theorem spec_size (b a m : ℕ) : size (spec b a m) ≤ 2*b+3+(2*a)*(8*(a+m+a)+8) := by
  let n := a+m+a
  have h := cuts_size n (ranks a m) (fun p hp => by
    rcases List.mem_append.mp hp with h | h
    all_goals obtain ⟨x,hx,rfl⟩ := List.mem_map.mp h
    all_goals simp only [List.mem_range] at hx
    all_goals dsimp only [n]; omega)
  have e : (ranks a m).length=2*a := by simp [ranks]; omega
  rw [e] at h
  dsimp only [n] at h
  change size (tally b) + size (numericSpec 0 (a+m+a) (ranks a m)).2 + 1 ≤ _
  rw [size_tally,tally_length]
  omega

private abbrev Config := (ℕ × ℕ) × InterchangeROMExpose.Input
private def scale (x : Config) := x.1.1+x.1.2+x.2.b+x.2.n+x.2.req.header.count

private theorem admin_all (K d : ℕ) :
    Dom scale (fun x => admin x.2.b x.1.1 x.1.2 (centerHeader x.2) K d) := by
  let p := scale
  have base := Dom.base p
  have a : Dom p (fun x : Config => x.1.1) := base.mono (fun _ => by dsimp [p,scale]; omega)
  have m : Dom p (fun x : Config => x.1.2) := base.mono (fun _ => by dsimp [p,scale]; omega)
  have b : Dom p (fun x : Config => x.2.b) := base.mono (fun _ => by dsimp [p,scale]; omega)
  let s (x : Config) := spec x.2.b x.1.1 x.1.2
  have hs : Dom p (fun x => size (s x)) := by
    have two := Dom.const p 2
    have eight := Dom.const p 8
    exact ((((two.mul b).add (Dom.const p 3)).add
      ((two.mul a).mul ((eight.mul ((a.add m).add a)).add eight)))).mono (fun _ => spec_size ..)
  let h (x : Config) := centerHeader x.2
  have header : Dom p (fun x => size (h x)) := by
    obtain ⟨k,C,hw⟩ := InterchangeROMExpose.header_budget
    have t : Dom p (fun x => size (template x.2)) := by
      apply ((Dom.const p 4).mul (base.add (Dom.const p 3))).mono
      intro x
      change (size (tally x.2.b) + size (tally x.2.n) + 1) + x.2.req.header.count + 1 ≤ _
      simp only [size_tally,tally_length]
      dsimp only [p,scale]
      omega
    exact ((Dom.const p C).mul ((t.add (Dom.const p 1)).pow k)).mono
      (fun x => (Nat.le_add_left _ _).trans (hw x.2))
  let input (x : Config) := (s x,h x)
  have whole : Dom p (fun x => size (input x)) := (hs.add header).add (Dom.const p 1)
  have result := (plan_poly.length.map input).sub whole
  have clock := (((Dom.const p 5).mul hs).add ((Dom.const p K).mul ((whole.add (Dom.const p 1)).pow d))).add
    (Dom.const p 20)
  have fee := clock.add ((Dom.const p 110).mul (result.add (Dom.const p 1)))
  exact (((fee.add ((Dom.const p 2).mul a)).add header).add (Dom.const p 4))

/-- The exponent is independent of the reserve lengths, radix, and request.
The remaining coefficient is a computable polynomial in the finite template
parameters once the two fixed command constants have been chosen. -/
theorem admin_bound (K d : ℕ) : ∃ k C : ℕ, ∀ a m (i : Input),
    admin i.b a m (centerHeader i) K d ≤
      (C*(a+m+i.b+i.n+1)^k)*(i.req.header.count+1)^k := by
  obtain ⟨k,C,h⟩ := admin_all K d
  refine ⟨k,C,fun a m i => ?_⟩
  have eq := h ((a,m),i)
  apply eq.trans
  simp only [scale]
  rw [Nat.mul_assoc,← Nat.mul_pow]
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  rw [Nat.add_mul,Nat.mul_add,Nat.mul_one,Nat.one_mul]
  omega

/-- A payload whose every record has the indicated physical size fits in
the ordinary volume, with the same exponent as the header work. -/
theorem local_price {b : ℕ} (r : Request b) (hb : 2≤b) (ok : r.Admissible)
    (k A C t : ℕ) (cells : ∀ j, (r.contents j).count≤A*(r.recordWidth+1))
    (adminCost : t ≤ C*(r.header.count+1)^k) :
    r.payload.count+t ≤ (A+C+3)*(localMass r k+1) := by
  have N : 0 < r.rows.count := (Nat.pow_pos (a:=2) (by decide)).trans_le (r.pow_digits_le hb ok)
  have power : 1 ≤ (r.header.count+1)^k := Nat.one_le_pow _ _ (by omega)
  have raw := stripe_size r.rows r.contents _ cells
  change r.payload.count ≤ _ at raw
  let p := (r.header.count+1)^k
  have hpow : p ≤ localMass r k := calc
    p ≤ r.recordWidth+p := Nat.le_add_left _ _
    _ ≤ localMass r k := Nat.le_mul_of_pos_left _ N
  have hN : r.rows.count ≤ localMass r k := Nat.le_mul_of_pos_right _ (by omega)
  have vol : r.rows.count*(r.recordWidth+1) ≤ localMass r k :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_left power _)
  have payloadBound : r.rows.count*(A*(r.recordWidth+1)) ≤ A*localMass r k := by
    rw [Nat.mul_left_comm]
    exact Nat.mul_le_mul_left _ vol
  have fee := adminCost.trans (Nat.mul_le_mul_left C hpow)
  rw [Nat.mul_add,Nat.mul_one] at raw
  rw [Nat.add_mul,Nat.add_mul,Nat.mul_add,Nat.mul_add]
  omega

end InterchangeROMStars

end NearSquareRoot
end Computability
end OAI
