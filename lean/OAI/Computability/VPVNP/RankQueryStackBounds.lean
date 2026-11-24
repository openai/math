import OAI.Computability.VPVNP.RankQueryStackSchur
import OAI.Computability.VPVNP.DeterminantQueries

/-!
# Time and live stack depth for determinant coefficient queries

The product and the matrix-power phases contribute their two binary logarithms
to the stack cap. Three intervening query tags connect a Schur factor to its
power query. The loop bounds include matrix indices and both coefficient
degrees.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack

variable {Q R : Type*}

namespace Node

/-- Every child of a branch has depth strictly below the given limit. Leaves satisfy the bound
unconditionally. -/
def Below (d : Q → ℕ) (limit : ℕ) : Node Q R → Prop
  | .leaf _ => True
  | .branch _ f => ∀ i, d (f i).1 < limit ∧ d (f i).2 < limit

/-- Number of product terms in a branch, with width zero for a leaf. -/
def width : Node Q R → ℕ
  | .leaf _ => 0
  | .branch t _ => t

theorem below_box {d : Q → ℕ} {limit n m : ℕ} {f : Fin n → Fin m → Q × Q}
    (h : ∀ i j, d (f i j).1 < limit ∧ d (f i j).2 < limit) :
    (box (R := R) n m f).Below d limit := fun k => h (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

theorem descends_iff (nodes : Q → Node Q R) (d : Q → ℕ) :
    (program nodes).Descends d ↔ ∀ q, (nodes q).Below d (d q) := by
  constructor
  · intro H q
    cases h : nodes q with
    | leaf => trivial
    | branch t f =>
      intro i
      have he : (program nodes).describe q = .inr t := by simp [program, h, describe]
      simpa only [program, h, children, dite_eq_left i.isLt] using H q t he i.val i.isLt
  · intro H q t he i hi
    specialize H q
    change (nodes q).describe = .inr t at he
    cases h : nodes q with
    | leaf r => simp [h, describe] at he
    | branch s f =>
      have hs : s = t := by simpa [h, describe] using he
      subst t
      rw [h] at H
      simpa only [program, h, children, dite_eq_left hi] using H ⟨i,hi⟩

theorem arity_iff (nodes : Q → Node Q R) (b : ℕ) :
    (program nodes).ArityLE b ↔ ∀ q, (nodes q).width ≤ b := by
  constructor
  · intro H q
    cases h : nodes q with
    | leaf => exact Nat.zero_le _
    | branch t f => exact H q t (by simp [program, h, describe])
  · intro H q t he
    specialize H q
    cases h : nodes q with
    | leaf r => simp [program, h, describe] at he
    | branch s f =>
      have ht : s = t := by simpa [program, h, describe] using he
      simpa [h, width, ht] using H

end Node

namespace SchurKey

variable {n U Z : ℕ} {F : Type*} [CommRing F]

/-- Depth measure on Schur query keys used to bound the stack of recursive calls. -/
def depth : K n U Z → ℕ
  | .product d _ _ _ => Nat.clog 2 U + 4 + d.val
  | .factor .. => Nat.clog 2 U + 3
  | .outer .. => Nat.clog 2 U + 2
  | .inner .. => Nat.clog 2 U + 1
  | .power _ q => q.depth
  | .scalar .. | .one => 0

/-- Uniform bound on the number of child pairs in any Schur query with parameters `n`, `U` and
`Z`. -/
def arityBound (n U Z : ℕ) := 1 + n * n + n * (Z+1) + (U+1)*(Z+1) + (Z+1)

private theorem below (entry : Entry n F) (q : K n U Z) :
    (q.node entry).Below depth q.depth := by
  cases q with
  | product d b u z =>
    simp only [node]
    split_ifs with hd hc
    · intro _
      simp [depth, hd]
    · trivial
    · apply Node.below_box
      intro s t
      simp only [depth, predBy]
      omega
  | factor a u z =>
    simp only [node]
    split_ifs
    · trivial
    · trivial
    · apply Node.below_box
      intro i j
      simp [depth]
  | outer a h i j z =>
    intro d
    simp [depth]
  | inner a h i j z =>
    intro d
    have hlt := Nat.clog_mono_right 2 (Nat.lt_succ_iff.mp h.isLt)
    simp only [depth, PowerKey.depth]
    omega
  | power a q =>
    have hp := (Node.descends_iff _ _).mp (PowerKey.descends (H := U) (Z := Z) (tailEntry entry a)) q
    change (q.node (tailEntry entry a)).Below PowerKey.depth q.depth at hp
    change ((q.node (tailEntry entry a)).map (.power a)).Below depth q.depth
    cases hn : q.node (tailEntry entry a) <;> rw [hn] at hp <;> exact hp
  | scalar | one => trivial

theorem descends (entry : Entry n F) : (program (U := U) (Z := Z) entry).Descends depth :=
  (Node.descends_iff _ _).mpr (below entry)

private theorem width_le (entry : Entry n F) (q : K n U Z) :
    (q.node entry).width ≤ arityBound n U Z := by
  unfold arityBound
  cases q with
  | product d b u z =>
    have hb : (u.val + 1) * (z.val + 1) ≤ (U+1)*(Z+1) := Nat.mul_le_mul u.isLt z.isLt
    simp only [node]
    split_ifs <;> simp only [Node.width, Node.box] <;> omega
  | factor a u z =>
    have hb := Nat.mul_le_mul (show n-a.val-1 ≤ n by omega) (show n-a.val-1 ≤ n by omega)
    simp only [node]
    split_ifs <;> simp only [Node.width, Node.box] <;> omega
  | outer a h i j z => change z.val + 1 ≤ _; have := z.isLt; omega
  | inner a h i j z => change z.val + 1 ≤ _; have := z.isLt; omega
  | power a q =>
    have hp := (Node.arity_iff _ _).mp (PowerKey.arity (H := U) (Z := Z) (tailEntry entry a)) q
    change (q.node (tailEntry entry a)).width ≤ (n-a.val-1)*(Z+1) at hp
    have hb := Nat.mul_le_mul_right (Z+1) (show n-a.val-1 ≤ n by omega)
    change ((q.node (tailEntry entry a)).map (SchurKey.power a)).width ≤ _
    cases hn : q.node (tailEntry entry a) <;> rw [hn] at hp <;> simp only [Node.map, Node.width] at hp ⊢ <;> omega
  | scalar | one => exact Nat.zero_le _

theorem arity (entry : Entry n F) : (program (U := U) (Z := Z) entry).ArityLE (arityBound n U Z) :=
  (Node.arity_iff _ _).mpr (width_le entry)

/-- The complete Schur stack machine computes the specified coefficient,
with a bound on the length of every intermediate continuation. -/
theorem run (M : Matrix (Fin n) (Fin n) (Polynomial F)) (entry : Entry n F)
    (he : ∀ i j z, entry i j z = (M i j).coeff z) (u : Limit U) (z : Limit Z) :
    let d := Nat.clog 2 U + 4 + Nat.clog 2 n
    ∃ t ≤ (5 + 6 * arityBound n U Z) ^ (d+1), (program entry).Runs d t (.enter (root u z), [])
      (.returned ((M.charpolyRev.coeff u.val).coeff z.val), []) := by
  have h := Program.run_bounded (program entry) (value entry) depth _ (realizes entry)
    (descends entry) (arity entry) (depth (root u z)) (root u z) le_rfl []
  have hd : depth (root (n := n) u z) = Nat.clog 2 U + 4 + Nat.clog 2 n := rfl
  simpa only [List.length_nil, Nat.zero_add, value_root, determinantQuery_eq M entry he, hd] using h

/-- A rank scan queries the same machine with scalar reads in the input
matrix. The weighted Gram coefficient requires at most two such reads. -/
theorem rankCoefficientRun {F : Type*} [Field F] {m : ℕ} (M : Matrix (Fin n) (Fin m) F)
    (u : Limit n) (z : Limit ((n+m)*n)) :
    let entry := weightedGramEntryCoeff M
    let d := Nat.clog 2 n + 4 + Nat.clog 2 n
    ∃ t ≤ (5 + 6 * arityBound n n ((n+m)*n)) ^ (d+1),
      (program entry).Runs d t (.enter (root u z), [])
        (.returned (((rankPolynomial M).coeff u.val).coeff z.val), []) :=
  run (weightedGram M) _ (weightedGramEntryCoeff_eq M) u z

end SchurKey

end RankQuery.Stack

end VPVNP
end Computability
end OAI
