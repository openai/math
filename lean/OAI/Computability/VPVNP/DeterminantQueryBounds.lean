import OAI.Computability.VPVNP.SchurCoefficientQueries
import Mathlib.Tactic.Ring

/-!
# Recomputation bounds for the determinant query

The call counts model the two nested recursions of Appendix D.2, including
every repeated request for a coefficient. A rank scan on a rectangular matrix
with dimensions bounded by `2^p` makes `2^O(p²)` scalar-query visits.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery

/-- Number of calls (including the root) made when every branch of a power
entry query on an `n × n` matrix is recomputed. Each degree split at each
intermediate index calls both children. -/
def powerQueryVisits (n h z : ℕ) : ℕ :=
  if h ≤ 1 then 1
  else 1 + n * ∑ d ∈ Finset.antidiagonal z,
      (powerQueryVisits n (h / 2) d.1 + powerQueryVisits n (h - h / 2) d.2)
termination_by Nat.clog 2 h
decreasing_by
  · exact (powerQuery_halves (by omega)).1
  · exact (powerQuery_halves (by omega)).2

/-- Full recomputation of a matrix-power coefficient makes at most
`(1 + 2n(z+1))^⌈log₂ h⌉` calls. -/
theorem powerQueryVisits_le (n h z : ℕ) :
    powerQueryVisits n h z ≤ (1 + 2 * n * (z + 1)) ^ Nat.clog 2 h := by
  let B := 1 + 2 * n * (z + 1)
  have aux (depth : ℕ) : ∀ t q, Nat.clog 2 t ≤ depth → q ≤ z →
      powerQueryVisits n t q ≤ B ^ depth := by
    induction depth with
    | zero =>
      intro t q ht _
      have hsmall := (Nat.clog_le_iff_le_pow (b := 2) (by decide)).mp ht
      have ht' : t ≤ 1 := by simpa using hsmall
      simp [powerQueryVisits, ht']
    | succ depth ih =>
      intro t q ht hq
      by_cases hsmall : t ≤ 1
      · rw [powerQueryVisits, ite_eq_left hsmall]
        exact Nat.one_le_pow _ _ (by dsimp [B]; omega)
      have hhalves := powerQuery_halves (Nat.lt_of_not_ge hsmall)
      have hsum : (∑ d ∈ Finset.antidiagonal q,
          (powerQueryVisits n (t / 2) d.1 + powerQueryVisits n (t - t / 2) d.2)) ≤
          (z + 1) * (B ^ depth + B ^ depth) := by
        calc
          _ ≤ ∑ _d ∈ Finset.antidiagonal q, (B ^ depth + B ^ depth) := by
            refine Finset.sum_le_sum fun d hd => ?_
            have hd' : d.1 + d.2 = q := Finset.mem_antidiagonal.mp hd
            exact Nat.add_le_add (ih _ _ (by omega) (by omega)) (ih _ _ (by omega) (by omega))
          _ = (q + 1) * (B ^ depth + B ^ depth) := by simp [Finset.Nat.card_antidiagonal]
          _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
      have hpos : 1 ≤ B ^ depth := Nat.one_le_pow _ _ (by dsimp [B]; omega)
      rw [powerQueryVisits, ite_eq_right hsmall, pow_succ]
      calc
        1 + _ ≤ B ^ depth + n * ((z + 1) * (B ^ depth + B ^ depth)) :=
          Nat.add_le_add hpos (Nat.mul_le_mul_left _ hsum)
        _ = B ^ depth * B := by dsimp [B]; ring
  exact aux _ h z le_rfl le_rfl

/-- For indices of at most exponential magnitude, the full tree of repeated
power coefficient queries has singly exponential size. -/
theorem powerQueryVisits_le_exp (n h z p : ℕ)
    (hn : n ≤ 2 ^ p) (hh : h ≤ 2 ^ p) (hz : z ≤ 2 ^ p) :
    powerQueryVisits n h z ≤ 2 ^ ((2 * p + 3) * p) := by
  have hdepth : Nat.clog 2 h ≤ p := Nat.clog_le_of_le_pow hh
  have hpos : 1 ≤ 2 ^ p := Nat.one_le_pow _ _ (by decide)
  have hz' : z + 1 ≤ 2 * 2 ^ p := by omega
  have hbase : 1 + 2 * n * (z + 1) ≤ 2 ^ (2 * p + 3) := calc
    _ ≤ 1 + 2 * 2 ^ p * (2 * 2 ^ p) :=
      Nat.add_le_add_left (Nat.mul_le_mul (Nat.mul_le_mul_left _ hn) hz') _
    _ ≤ 8 * (2 ^ p * 2 ^ p) := by
      have hp := Nat.mul_le_mul hpos hpos
      ring_nf at hp ⊢
      omega
    _ = 2 ^ (2 * p + 3) := by rw [two_mul p, pow_add, pow_add]; ring
  calc
    powerQueryVisits n h z ≤ _ := powerQueryVisits_le n h z
    _ ≤ (2 ^ (2 * p + 3)) ^ Nat.clog 2 h := Nat.pow_le_pow_left hbase _
    _ ≤ (2 ^ (2 * p + 3)) ^ p := Nat.pow_le_pow_right (Nat.pow_pos (by decide)) hdepth
    _ = _ := (pow_mul _ _ _).symm

/-- Count calls in the same balanced recursion as the bivariate coefficient query.
An empty leaf costs one visit. A nonempty leaf incurs its supplied cost, which
can include the recursion used to evaluate the factor. -/
def balancedBivariateVisits (leafCost : ℕ → ℕ → ℕ → ℕ) (depth first count u z : ℕ) : ℕ :=
  balancedProduct (fun _ : ℕ × ℕ => 1)
    (fun left right p => 1 + streamAntiSum p.1 fun a₁ a₂ => streamAntiSum p.2 fun b₁ b₂ =>
      left (a₁, b₁) + right (a₂, b₂))
    (fun i p => leafCost i p.1 p.2) depth first count (u, z)

/-- Count all recursive calls, including empty and padded leaves. No restriction
on the starting index or the number of factors is needed for the bound. -/
theorem balancedBivariateVisits_le (leafCost : ℕ → ℕ → ℕ → ℕ) (depth first count u z L : ℕ)
    (hL : 1 ≤ L) (hleaf : ∀ i a b, a ≤ u → b ≤ z → leafCost i a b ≤ L) :
    balancedBivariateVisits leafCost depth first count u z ≤
      L * (1 + 2 * (u + 1) * (z + 1)) ^ depth := by
  let B := 1 + 2 * (u + 1) * (z + 1)
  have aux (d : ℕ) : ∀ i c a b, a ≤ u → b ≤ z →
      balancedBivariateVisits leafCost d i c a b ≤ L * B ^ d := by
    induction d with
    | zero =>
      intro i c a b ha hb
      by_cases hc : c = 0 <;>
        simp [balancedBivariateVisits, balancedProduct, hc, hL, hleaf i a b ha hb]
    | succ d ih =>
      intro i c a b ha hb
      let W := L * B ^ d
      have hpos : 1 ≤ W := by
        exact Nat.mul_le_mul hL (Nat.one_le_pow _ _ (by dsimp [B]; omega))
      change 1 + (streamAntiSum a fun a₁ a₂ => streamAntiSum b fun b₁ b₂ =>
        balancedBivariateVisits leafCost d i (c / 2) a₁ b₁ +
        balancedBivariateVisits leafCost d (i + c / 2) (c - c / 2) a₂ b₂) ≤ _
      simp_rw [streamAntiSum_eq]
      calc
        1 + _ ≤ W + ∑ _e ∈ Finset.antidiagonal a, ∑ _f ∈ Finset.antidiagonal b, (W + W) := by
          refine Nat.add_le_add hpos (Finset.sum_le_sum fun e he => Finset.sum_le_sum fun f hf => ?_)
          have hea := Finset.mem_antidiagonal.mp he
          have hfb := Finset.mem_antidiagonal.mp hf
          exact Nat.add_le_add (ih _ _ _ _ (by omega) (by omega))
            (ih _ _ _ _ (by omega) (by omega))
        _ = W + (a + 1) * ((b + 1) * (W + W)) := by simp [Finset.Nat.card_antidiagonal]
        _ ≤ W + (u + 1) * ((z + 1) * (W + W)) :=
          Nat.add_le_add_left (Nat.mul_le_mul (by omega) (Nat.mul_le_mul_right _ (by omega))) _
        _ = L * B ^ (d + 1) := by dsimp [W]; rw [pow_succ]; dsimp [B]; ring
  exact aux depth first count u z le_rfl le_rfl

/-- With a unit cost per terminal coefficient query this counts the product
recursion alone. -/
theorem balancedBivariateVisits_unit_le (depth first count u z : ℕ) :
    balancedBivariateVisits (fun _ _ _ => 1) depth first count u z ≤
      (1 + 2 * (u + 1) * (z + 1)) ^ depth := by
  simpa using balancedBivariateVisits_le (fun _ _ _ => 1) depth first count u z 1
    le_rfl (fun _ _ _ _ _ => le_rfl)

/-- Exponential bounds on the degree ranges and on a leaf query compose with
the balanced recursion to give a singly exponential recomputation bound. -/
theorem balancedBivariateVisits_le_exp (leafCost : ℕ → ℕ → ℕ → ℕ)
    (depth first count u z p l : ℕ) (hd : depth ≤ p) (hu : u ≤ 2 ^ p) (hz : z ≤ 2 ^ p)
    (hleaf : ∀ i a b, a ≤ u → b ≤ z → leafCost i a b ≤ 2 ^ l) :
    balancedBivariateVisits leafCost depth first count u z ≤ 2 ^ (l + (2 * p + 4) * p) := by
  have hp : 1 ≤ 2 ^ p := Nat.one_le_pow _ _ (by decide)
  have hbase : 1 + 2 * (u + 1) * (z + 1) ≤ 2 ^ (2 * p + 4) := calc
    _ ≤ 1 + 2 * (2 * 2 ^ p) * (2 * 2 ^ p) :=
      Nat.add_le_add_left (Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)) _
    _ ≤ 16 * (2 ^ p * 2 ^ p) := by
      have hp' := Nat.mul_le_mul hp hp
      ring_nf at hp' ⊢
      omega
    _ = 2 ^ (2 * p + 4) := by rw [two_mul p, pow_add, pow_add]; ring
  apply (balancedBivariateVisits_le leafCost depth first count u z _ (Nat.one_le_pow _ _ (by decide))
    hleaf).trans
  rw [pow_add, pow_mul]
  apply Nat.mul_le_mul_left
  exact (Nat.pow_le_pow_left hbase _).trans (Nat.pow_le_pow_right (Nat.pow_pos (by decide)) hd)

/-- Number of scalar coefficient queries in one Schur factor, including the
factor query itself. A matrix-power base case counts as one visit. At each
higher bidegree, every degree split reads the last entry once and each inner
split reads the first entry and evaluates one trailing matrix power. -/
def headFactorVisits (n u z : ℕ) : ℕ :=
  match u with
  | 0 => 1
  | 1 => 2
  | h + 2 => 1 + n * n * streamAntiSum z fun d₁ _ =>
      1 + streamAntiSum d₁ fun _ e₂ => 1 + powerQueryVisits n h e₂

private theorem streamAntiSum_le (q W : ℕ) (f : ℕ → ℕ → ℕ)
    (hf : ∀ i j, i + j = q → f i j ≤ W) : streamAntiSum q f ≤ (q + 1) * W := by
  rw [streamAntiSum_eq]
  calc
    _ ≤ ∑ _e ∈ Finset.antidiagonal q, W :=
      Finset.sum_le_sum fun e he => hf _ _ (Finset.mem_antidiagonal.mp he)
    _ = _ := by simp [Finset.Nat.card_antidiagonal]

/-- Bounding the two matrix indices and both streamed degree splits, together
with all calls of the power-entry recursion, gives a singly exponential bound. -/
theorem headFactorVisits_le_exp (n u z p : ℕ) (hn : n ≤ 2 ^ p) (hu : u ≤ 2 ^ p)
    (hz : z ≤ 2 ^ p) : headFactorVisits n u z ≤ 2 ^ (4 * p + 5 + (2 * p + 3) * p) := by
  let N := 2 ^ p
  let E := 2 ^ ((2 * p + 3) * p)
  have hN : 1 ≤ N := Nat.one_le_pow _ _ (by decide)
  have hE : 1 ≤ E := Nat.one_le_pow _ _ (by decide)
  have hresult : 2 ^ (4 * p + 5 + (2 * p + 3) * p) = 32 * N ^ 4 * E := by
    rw [pow_add, pow_add, mul_comm 4 p, pow_mul]
    dsimp [N, E]
    ring
  rw [hresult]
  have hNE : 1 ≤ N * E := Nat.mul_le_mul hN hE
  have hN4E : 1 ≤ N ^ 4 * E := Nat.mul_le_mul (Nat.one_le_pow _ _ hN) hE
  rcases u with _ | _ | h
  · simp only [headFactorVisits]; rw [mul_assoc]; omega
  · simp only [headFactorVisits]; rw [mul_assoc]; omega
  have hsplit (d : ℕ) (hd : d ≤ z) :
      streamAntiSum d (fun _ e₂ => 1 + powerQueryVisits n h e₂) ≤ 4 * (N * E) := by
    calc
      _ ≤ (d + 1) * (2 * E) := streamAntiSum_le _ _ _ fun i j hij => by
        have ht := powerQueryVisits_le_exp n h j p hn (by omega) (by omega)
        change powerQueryVisits n h j ≤ E at ht
        omega
      _ ≤ (2 * N) * (2 * E) := Nat.mul_le_mul_right _ (by change z ≤ N at hz; omega)
      _ = _ := by ring
  have houter : streamAntiSum z (fun d _ => 1 +
      streamAntiSum d (fun _ e₂ => 1 + powerQueryVisits n h e₂)) ≤ 16 * N ^ 2 * E := by
    calc
      _ ≤ (z + 1) * (8 * (N * E)) := streamAntiSum_le _ _ _ fun i j hij => by
        have ht := hsplit i (by omega)
        omega
      _ ≤ (2 * N) * (8 * (N * E)) := Nat.mul_le_mul_right _ (by change z ≤ N at hz; omega)
      _ = _ := by ring
  change 1 + n * n * _ ≤ _
  calc
    _ ≤ 1 + N * N * (16 * N ^ 2 * E) :=
      Nat.add_le_add_left (Nat.mul_le_mul (Nat.mul_le_mul hn hn) houter) _
    _ = 1 + 16 * (N ^ 4 * E) := by ring
    _ ≤ 32 * N ^ 4 * E := by rw [mul_assoc]; omega

/-- Calls made by one determinant coefficient query. Its leaves use the
corresponding trailing matrix size, and all identity leaves cost one visit. -/
def determinantQueryVisits (n u z : ℕ) : ℕ :=
  balancedBivariateVisits
    (fun i a b => if i < n then headFactorVisits (n - i - 1) a b else 1)
    (Nat.clog 2 n) 0 n u z

/-- The complete coefficient query, including both the product recursion and
the Schur-factor power recursions, makes at most exponentially many visits
when the dimension and both degrees have at most `p + 1` bits. -/
theorem determinantQueryVisits_le_exp (n u z p : ℕ)
    (hn : n ≤ 2 ^ p) (hu : u ≤ 2 ^ p) (hz : z ≤ 2 ^ p) :
    determinantQueryVisits n u z ≤ 2 ^ (4 * p + 5 + (2 * p + 3) * p + (2 * p + 4) * p) := by
  apply balancedBivariateVisits_le_exp _ _ _ _ _ _ _ _ (Nat.clog_le_of_le_pow hn) hu hz
  intro i a b ha hb
  split_ifs
  · exact headFactorVisits_le_exp _ _ _ p (by omega) (ha.trans hu) (hb.trans hz)
  · exact Nat.one_le_pow _ _ (by decide)

/-- Total scalar-query visits over the complete rectangular scan used by
`rankQuery`, with full recomputation at every bidegree. -/
def rankQueryVisits (n m : ℕ) : ℕ :=
  ∑ u : Fin (n + 1), ∑ z : Fin ((n + m) * n + 1), determinantQueryVisits n u.val z.val

/-- The complete rank scan is singly exponential when both dimensions have
at most `p + 1` bits. Its inner degree needs at most `2*p+2` bits. -/
theorem rankQueryVisits_le_exp (n m p : ℕ) (hn : n ≤ 2 ^ p) (hm : m ≤ 2 ^ p) :
    let s := 2 * p + 1
    rankQueryVisits n m ≤ 2 ^ (p + 1 + (s + 1) +
      (4 * s + 5 + (2 * s + 3) * s + (2 * s + 4) * s)) := by
  let s := 2 * p + 1
  let c := 4 * s + 5 + (2 * s + 3) * s + (2 * s + 4) * s
  have hdim : n ≤ 2 ^ s := hn.trans (Nat.pow_le_pow_right (by decide) (by dsimp [s]; omega))
  have hdegree : (n + m) * n ≤ 2 ^ s := calc
    _ ≤ (2 ^ p + 2 ^ p) * 2 ^ p := Nat.mul_le_mul (Nat.add_le_add hn hm) hn
    _ = _ := by dsimp [s]; rw [two_mul p, pow_add, pow_add]; ring
  have hterms (u : Fin (n + 1)) (z : Fin ((n + m) * n + 1)) :
      determinantQueryVisits n u.val z.val ≤ 2 ^ c :=
    determinantQueryVisits_le_exp n _ _ s hdim ((Nat.lt_succ_iff.mp u.isLt).trans hdim)
      ((Nat.lt_succ_iff.mp z.isLt).trans hdegree)
  have hsucc (k t : ℕ) (h : k ≤ 2 ^ t) : k + 1 ≤ 2 ^ (t + 1) := by
    rw [pow_succ]
    have ht : 1 ≤ 2 ^ t := Nat.one_le_pow _ _ (by decide)
    omega
  change _ ≤ 2 ^ (p + 1 + (s + 1) + c)
  calc
    rankQueryVisits n m ≤ ∑ _u : Fin (n + 1), ∑ _z : Fin ((n + m) * n + 1), 2 ^ c :=
      Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun z _ => hterms u z
    _ = (n + 1) * (((n + m) * n + 1) * 2 ^ c) := by simp
    _ ≤ 2 ^ (p + 1) * (2 ^ (s + 1) * 2 ^ c) :=
      Nat.mul_le_mul (hsucc _ _ hn) (Nat.mul_le_mul_right _ (hsucc _ _ hdegree))
    _ = _ := by simp only [pow_add, mul_assoc]

end RankQuery

end VPVNP
end Computability
end OAI
