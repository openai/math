import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Nat.Prime.Basic

/-! # The remainder axis of a densely occupied coprime box

A list of odd coprime moduli occupies the axes with a common padded width. The
address bits left over from division by that width form one fully occupied
power-of-two axis. Widths precede moduli in the resulting pairs.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BoxShape

/-- Form the full-width axes and append the nonempty remainder axis. -/
def axes (k l : ℕ) (a : List ℕ) : List (ℕ × ℕ) :=
  a.map (fun x => (l, x)) ++ if k % l = 0 then [] else [(k % l, 2 ^ (k % l))]

/-- Address widths, local padding, coprimality, and occupied volume. -/
structure Valid (k l : ℕ) (box : List (ℕ × ℕ)) : Prop where
  widthSum : (box.map Prod.fst).sum = k
  axisBounds : ∀ p ∈ box, 0 < p.1 ∧ p.1 ≤ l ∧ 2 ≤ p.2 ∧ p.2 ≤ 2 ^ p.1
  coprime : (box.map Prod.snd).Pairwise Nat.Coprime
  axisCount : box.length ≤ k / l + 1
  density : 2 ^ k ≤ 2 * (box.map Prod.snd).prod

theorem valid_axes {k l : ℕ} (hl : 0 < l) (a : List ℕ)
    (hlen : a.length = k / l) (hsize : ∀ x ∈ a, 2 ≤ x ∧ x ≤ 2 ^ l)
    (hodd : ∀ x ∈ a, Odd x) (hcop : a.Pairwise Nat.Coprime)
    (hvol : (2 ^ l) ^ a.length ≤ 2 * a.prod) : Valid k l (axes k l a) := by
  have hsum : a.length * l + k % l = k := by
    simpa only [hlen, Nat.mul_comm (k / l)] using Nat.div_add_mod k l
  have hpow : 2 ^ k = (2 ^ l) ^ a.length * 2 ^ (k % l) := by
    conv_lhs => rw [← hsum, pow_add, Nat.mul_comm a.length l, pow_mul]
  have hmain : (a.map fun x => (l, x)).map Prod.snd = a := by simp [List.map_map]
  have hwidth : ((a.map fun x => (l, x)).map Prod.fst).sum = a.length * l := by
    simp [List.map_map, Function.comp_def]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold axes
    rw [List.map_append, List.sum_append, hwidth]
    split <;> simp_all
  · intro p hp
    obtain hp | hp := List.mem_append.mp hp
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
      exact ⟨hl, le_rfl, hsize x hx⟩
    · split at hp
      · simp at hp
      · rename_i hrem
        obtain rfl := List.mem_singleton.mp hp
        exact ⟨Nat.pos_of_ne_zero hrem, (Nat.mod_lt _ hl).le,
          Nat.one_lt_pow hrem (by decide), le_rfl⟩
  · unfold axes
    rw [List.map_append, hmain]
    split
    · simpa using hcop
    · simp only [List.map_cons, List.map_nil, List.pairwise_append,
        List.pairwise_singleton, List.mem_singleton, forall_eq, true_and]
      exact ⟨hcop, fun x hx => (hodd x hx).coprime_two_right.pow_right _⟩
  · unfold axes
    rw [List.length_append, List.length_map, hlen]
    split <;> simp
  · unfold axes
    rw [List.map_append, List.prod_append, hmain, hpow]
    have h := Nat.mul_le_mul_right (2 ^ (k % l)) hvol
    split <;> simp_all [Nat.mul_assoc]

/-- With `k = ⌈log₂(4h)⌉` there is room for every coefficient of the ordinary
product of two `h`-digit polynomials. -/
theorem Valid.capacity {k l h : ℕ} {box : List (ℕ × ℕ)}
    (hbox : Valid k l box) (hk : 4 * h ≤ 2 ^ k) : 2 * h ≤ (box.map Prod.snd).prod := by
  have := hbox.density
  omega

/-- At a depth of the CRT tree, the union of all left children has at most
half of the axes. The possible short axis costs at most `l` extra bits in
the doubled control width. -/
theorem Valid.controlWidth {k l : ℕ} {box controls : List (ℕ × ℕ)}
    (hbox : Valid k l box) (hsub : controls.Sublist box)
    (hcount : 2 * controls.length ≤ box.length) :
    2 * (controls.map Prod.fst).sum ≤ k + l := by
  have hwidth := List.sum_le_length_nsmul (controls.map Prod.fst) l (by
    intro w hw
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
    exact (hbox.axisBounds p (hsub.subset hp)).2.1)
  simp only [List.length_map, nsmul_eq_mul] at hwidth
  calc
    2 * (controls.map Prod.fst).sum ≤ 2 * (controls.length * l) :=
      Nat.mul_le_mul_left 2 hwidth
    _ = (2 * controls.length) * l := (Nat.mul_assoc ..).symm
    _ ≤ (k / l + 1) * l := Nat.mul_le_mul_right l (hcount.trans hbox.axisCount)
    _ ≤ k + l := by
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.add_le_add_right (Nat.div_mul_le_self k l) l

/-- A quarter of the padded address bits remain outside the controls as soon as
one full-width axis occupies at most half the address. -/
theorem Valid.controlFraction {k l : ℕ} {box controls : List (ℕ × ℕ)}
    (hbox : Valid k l box) (hsub : controls.Sublist box)
    (hcount : 2 * controls.length ≤ box.length) (hl : 2 * l ≤ k) :
    4 * (controls.map Prod.fst).sum ≤ 3 * k := by
  have := hbox.controlWidth hsub hcount
  omega

/-- All left children at one level of the balanced CRT recursion, in axis order. -/
def leftControls {α : Type*} (blocks : List (List α)) : List α :=
  blocks.flatMap fun block => block.take (block.length / 2)

theorem leftControls_bound {α : Type*} (blocks : List (List α)) :
    (leftControls blocks).Sublist blocks.flatten ∧
      2 * (leftControls blocks).length ≤ blocks.flatten.length := by
  induction blocks with
  | nil => simp [leftControls]
  | cons block blocks ih =>
    change (block.take _ ++ leftControls blocks).Sublist (block ++ blocks.flatten) ∧ _
    refine ⟨(List.take_sublist _ _).append ih.1, ?_⟩
    change 2 * (block.take _ ++ leftControls blocks).length ≤ (block ++ blocks.flatten).length
    rw [List.length_append, List.length_append, List.length_take,
      min_eq_left (Nat.div_le_self _ _)]
    have := ih.2
    omega

/-- Splitting every interval at half its axis count leaves at least a quarter
of all address bits free for the controlled permutations. -/
theorem Valid.leftControlsFraction {k l : ℕ} {blocks : List (List (ℕ × ℕ))}
    (hbox : Valid k l blocks.flatten) (hl : 2 * l ≤ k) :
    4 * ((leftControls blocks).map Prod.fst).sum ≤ 3 * k := by
  obtain ⟨hsub, hcount⟩ := leftControls_bound blocks
  exact hbox.controlFraction hsub hcount hl

end BoxShape

end NearSquareRoot
end Computability
end OAI
