import OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Inverse

section
/-! # A word program for pairing neighbors in sorted order -/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.RAM
open Coloring

theorem partner {w h k : ℕ} (hh : h ≤ w) (hk : k ≤ w) :
    RAM w (fun x : (B h → B k) × (B h → Bool) => Coloring.partner x.1 x.2)
      (2 ^ h * (100 + w) ^ 30) := by
  obtain ⟨inv, hi, ei⟩ := inverse hh
  have flip : RAM w (fun p : B h → B h => p ∘ Coloring.toggle h) (2 ^ h * 2) :=
    .tab hh _ (fun i => .at hh (Coloring.toggle h i))
  have nbr := (RAM.permutation hh hk).comp ((flip.pair hi).comp (gather hh hh))
  have mask : RAM w (fun (x : (B h → Bool) × (B h → B h)) i =>
      if x.1 i then x.2 i else i) (2 ^ h * 9) :=
    .tab hh _ (fun i => ((RAM.fst.comp (.at hh i)).pair
      ((RAM.snd.comp (.at hh i)).pair (.lit hh i))).comp .select)
  have H := (RAM.snd.pair nbr).comp mask
  convert H.mono (n := 2 ^ h * (100 + w) ^ 30) ?_ using 1
  · funext x i
    simp only [Function.comp_apply, Coloring.partner, ei]
  · have := Nat.two_pow_pos h
    have := budget_base h w 25
    have := budget_mono h w (by decide : 20 ≤ 25)
    have := (budget_step h w 25).trans (budget_mono h w (by decide : 26 ≤ 30))
    omega

end OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.RAM
end

section
/-!
# Alternating colours by pointer doubling

At round t the two arrays store a jump of length 2^t and the minimum
along that many consecutive edges. Each round costs linearly many loads
and comparisons. The arrays from the previous round are shared.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.RAM
open Coloring

private abbrev Table (h : ℕ) := B h → B h

variable {w h k : ℕ}

private theorem minimum (hh : h ≤ w) :
    RAM w (fun x : B h × B h => min x.1 x.2) 4 := by
  have H := ((RAM.lt hh).pair RAM.id).comp (RAM.select (A := B h))
  convert H using 1
  funext x
  simp only [Function.comp_apply, id_eq, decide_eq_true_eq]
  by_cases hs : x.1 < x.2
  · rw [ite_eq_left hs, min_eq_left hs.le]
  · rw [ite_eq_right hs, min_eq_right (le_of_not_gt hs)]

/-- Read a value at i and at the successor indexed by the first array. -/
private theorem two_values (hh : h ≤ w) (i : B h) :
    RAM w (fun x : Table h × Table h => (x.2 i, x.2 (x.1 i))) 8 :=
  (RAM.snd.comp (.at hh i)).pair ((RAM.snd.pair (RAM.fst.comp (.at hh i))).comp (.read hh))

private theorem double_step (hh : h ≤ w) :
    RAM w (fun x : Table h × Table h => (x.1 ∘ x.1, fun i => min (x.2 i) (x.2 (x.1 i))))
      (2 ^ h * 23) := by
  have J : RAM w (fun x : Table h × Table h => x.1 ∘ x.1) (3 + 2 ^ h * 6) :=
    (RAM.fst.pair RAM.fst).comp (gather hh hh)
  have M : RAM w (fun x : Table h × Table h => fun i => min (x.2 i) (x.2 (x.1 i)))
      (2 ^ h * 13) := .tab hh _ (fun i => (two_values hh i).comp (minimum hh))
  exact (J.pair M).mono (by have := Nat.two_pow_pos h; omega)

private theorem doubling (hh : h ≤ w) (t : ℕ) :
    RAM w (fun P : Table h => (jump P t, low P t)) (2 ^ h * (4 + 23 * t)) := by
  induction t with
  | zero =>
    have M : RAM w (fun _ : Table h => (_root_.id : Table h)) (2 ^ h * 2) :=
      .tab hh _ (fun i => .lit hh i)
    exact (RAM.id.pair M).mono (by have := Nat.two_pow_pos h; omega)
  | succ t ih =>
    exact (ih.comp (double_step hh)).mono (by ring_nf; rfl)

theorem colour (hh : h ≤ w) :
    RAM w (fun x : (B h → B h) × (B h → B h) => Coloring.colour h x.1 x.2) (2 ^ h * (100 + w) ^ 2) := by
  have J : RAM w (fun x : Table h × Table h => x.2 ∘ x.1) (3 + 2 ^ h * 6) :=
    (RAM.snd.pair RAM.fst).comp (gather hh hh)
  have M := (J.comp (doubling hh h)).comp RAM.snd
  have H : RAM w (fun x : Table h × Table h => fun i => decide (x.2 i < x.2 (x.1 i)))
      (2 ^ h * 10) := .tab hh _ (fun i => (two_values hh i).comp (.lt hh))
  apply ((RAM.fst.pair M).comp H).mono
  calc
    _ ≤ 2 ^ h * (26 + 23 * h) := by have := Nat.two_pow_pos h; ring_nf; omega
    _ ≤ _ := Nat.mul_le_mul_left _ (by nlinarith)

theorem split (hh : h ≤ w) (hk : k ≤ w) :
    RAM w (fun x : (B h → B k) × (B h → B k) × (B h → Bool) =>
      Coloring.split x.1 x.2.1 x.2.2) (2 ^ h * (100 + w) ^ 40) := by
  have part := RAM.partner hh hk
  let A := (B h → B k) × (B h → B k) × (B h → Bool)
  have L : RAM w (fun x : A => (x.1, x.2.2)) 4 := RAM.fst.pair (RAM.snd.comp RAM.snd)
  have R : RAM w (fun x : A => x.2) 1 := RAM.snd
  apply (((L.comp part).pair (R.comp part)).comp (colour hh)).mono
  have := Nat.two_pow_pos h
  have := budget_base h w 30
  have := budget_mono h w (by decide : 2 ≤ 30)
  have := (budget_step h w 30).trans (budget_mono h w (by decide : 31 ≤ 40))
  omega

end OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.RAM
end
