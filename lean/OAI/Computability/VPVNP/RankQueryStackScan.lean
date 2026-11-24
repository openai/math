import OAI.Computability.VPVNP.RankQueryStackBounds

/-!
# Clocked stack computation of rectangular matrix rank

The evaluator halts when it reaches a returned scalar at empty stack. The rank
scan uses this evaluator for every bidegree, with no access to polynomial
matrices or their determinants.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack

namespace Program

variable {Q R : Type*} [Semiring R] (p : Program Q R)

/-- Tail-recursive execution with a timeout. An empty-stack return is a
successful result, including exactly at the clock boundary. -/
def drive : ℕ → Config Q R → Option R
  | _, (.returned r, []) => some r
  | 0, _ => none
  | t+1, c => drive t (p.step c)

theorem drive_next (t : ℕ) (c : Config Q R) : p.drive (t+1) c = p.drive t (p.step c) := by
  rcases c with ⟨control, s⟩
  cases control with
  | enter | scan => rfl
  | returned r => cases s <;> cases t <;> rfl

theorem Runs.drive {cap t : ℕ} {a b : Config Q R} (h : p.Runs cap t a b) (rem : ℕ) :
    p.drive (t+rem) a = p.drive rem b := by
  induction h with
  | done => simp
  | next _ _ ih => rw [Nat.succ_add, drive_next, ih]

end Program

namespace SchurKey

variable {n : ℕ} {R : Type*} [CommRing R]

/-- Bound on abstract stack transitions for a Schur query with matrix order `n` and degree
limits `U` and `Z`. -/
def clock (n U Z : ℕ) :=
  (5 + 6 * arityBound n U Z) ^ (Nat.clog 2 U + 4 + Nat.clog 2 n + 1)

/-- Run the determinant coefficient query at bidegree `(u,z)` with its proved transition bound,
defaulting to zero on timeout. -/
def compute (entry : Entry n R) (u z : ℕ) : R :=
  ((program entry).drive (clock n u z) (.enter (root (Fin.last u) (Fin.last z)), [])).getD 0

theorem compute_correct (M : Matrix (Fin n) (Fin n) (Polynomial R)) (entry : Entry n R)
    (he : ∀ i j z, entry i j z = (M i j).coeff z) (u z : ℕ) :
    compute entry u z = (M.charpolyRev.coeff u).coeff z := by
  obtain ⟨t,ht,hrun⟩ := run M entry he (Fin.last u) (Fin.last z)
  change t ≤ clock n u z at ht
  have hr := hrun.drive (program entry) (clock n u z - t)
  rw [Nat.add_sub_of_le ht] at hr
  unfold compute
  rw [hr]
  cases clock n u z - t <;> rfl

/-- Rectangular matrix rank from the stack program and scalar input accesses. -/
def computeRank {F : Type*} [CommRing F] [DecidableEq F] {m : ℕ}
    (M : Matrix (Fin n) (Fin m) F) : ℕ :=
  scanRank n m (compute (weightedGramEntryCoeff M))

theorem computeRank_eq {F : Type*} [Field F] [DecidableEq F] {m : ℕ}
    (M : Matrix (Fin n) (Fin m) F) : computeRank M = M.rank :=
  scanRank_correct M _ (compute_correct (weightedGram M) _ (weightedGramEntryCoeff_eq M))

theorem arityBound_le_exp (n U Z s : ℕ) (hn : n ≤ 2^s) (hu : U ≤ 2^s) (hz : Z ≤ 2^s) :
    arityBound n U Z ≤ 2 ^ (2*s + 4) := by
  let A := 2^s
  have hA : 1 ≤ A := Nat.one_le_pow _ _ (by decide)
  change n ≤ A at hn
  change U ≤ A at hu
  change Z ≤ A at hz
  have hZ : Z + 1 ≤ 2*A := by omega
  have hU : U + 1 ≤ 2*A := by omega
  have hn2 := Nat.mul_le_mul hn hn
  have hnZ := Nat.mul_le_mul hn hZ
  have huZ := Nat.mul_le_mul hU hZ
  have ha2 := Nat.mul_le_mul_left A hA
  have hr : 2 ^ (2*s + 4) = 16*(A*A) := by dsimp [A]; rw [two_mul, pow_add, pow_add]; ring
  rw [hr, arityBound]
  nlinarith

/-- The clock bound is singly exponential in the common bit bound. -/
theorem clock_le_exp (n u z s : ℕ) (hn : n ≤ 2^s) (hu : u ≤ 2^s) (hz : z ≤ 2^s) :
    clock n u z ≤ 2 ^ ((2*s+8)*(2*s+5)) := by
  have ha := arityBound_le_exp n u z s hn hu hz
  have hA := Nat.one_le_pow (2*s+4) 2 (by decide)
  have hb : 5+6*arityBound n u z ≤ 2^(2*s+8) := by
    rw [show 2*s+8 = (2*s+4)+4 by omega, pow_add]
    norm_num
    omega
  have hd : Nat.clog 2 u+4+Nat.clog 2 n+1 ≤ 2*s+5 := by
    have := Nat.clog_le_of_le_pow hn
    have := Nat.clog_le_of_le_pow hu
    omega
  calc
    clock n u z ≤ (2^(2*s+8)) ^ (Nat.clog 2 u+4+Nat.clog 2 n+1) := Nat.pow_le_pow_left hb _
    _ ≤ (2^(2*s+8)) ^ (2*s+5) := Nat.pow_le_pow_right (by positivity) hd
    _ = _ := (pow_mul ..).symm

/-- Total scalar-stack clock over the rectangular scan, including queries
for zero rows or zero columns. -/
theorem rankClock_le_exp (n m p : ℕ) (hn : n ≤ 2^p) (hm : m ≤ 2^p) :
    let s := 2*p+1
    ∑ u : Fin (n+1), ∑ z : Fin ((n+m)*n+1), clock n u z ≤
      2^(p+1 + (s+1) + (2*s+8)*(2*s+5)) := by
  let s := 2*p+1
  let c := (2*s+8)*(2*s+5)
  have hN : n ≤ 2^s := hn.trans (Nat.pow_le_pow_right (by decide) (by dsimp [s]; omega))
  have hZ : (n+m)*n ≤ 2^s := calc
    _ ≤ (2^p+2^p)*2^p := Nat.mul_le_mul (Nat.add_le_add hn hm) hn
    _ = _ := by dsimp [s]; rw [two_mul p, pow_add, pow_add]; ring
  have hsucc (a k : ℕ) (h : a ≤ 2^k) : a+1 ≤ 2^(k+1) := by
    rw [pow_succ]
    have := Nat.one_le_pow k 2 (by decide)
    omega
  change _ ≤ 2^(p+1 + (s+1) + c)
  calc
    _ ≤ ∑ _u : Fin (n+1), ∑ _z : Fin ((n+m)*n+1), 2^c :=
      Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun z _ =>
        clock_le_exp n u z s hN ((Nat.lt_succ_iff.mp u.isLt).trans hN) ((Nat.lt_succ_iff.mp z.isLt).trans hZ)
    _ = (n+1)*(((n+m)*n+1)*2^c) := by simp
    _ ≤ (2^(p+1)) * ((2^(s+1)) * 2^c) :=
      Nat.mul_le_mul (hsucc n p hn) (Nat.mul_le_mul_right _ (hsucc _ s hZ))
    _ = _ := by simp only [pow_add, mul_assoc]

end SchurKey

end RankQuery.Stack

end VPVNP
end Computability
end OAI
