import OAI.Optimization.LinearProgramming.Recovery.Matrix
import OAI.Optimization.LinearProgramming.Recovery.Slack
import OAI.Optimization.LinearProgramming.Farkas.Sparse

/-! The oracle reduction in §2. The output is a vector computed by the algorithm. On the
dual side, sparsity is proved for this very vector, using uniqueness on the recovered line. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery

open Matrix Presentation
open scoped Matrix

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {m d : ℕ}

def primalPresentation (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) := fromColumns (slackColumns A b)

def dualPresentation (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) := fromKernel (slackColumns A b)ᵀ

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem mem_dualPresentation (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) (w : Fin (m+1) → K) :
    w ∈ (dualPresentation A b).denote ↔ Aᵀ *ᵥ Fin.tail w = 0 ∧ b ⬝ᵥ Fin.tail w = -w 0 := by
  rw [dualPresentation,transpose_kernel,denote_columns,slackColumns_range]
  simpa using Farkas.slack_orthogonal_iff A b (w 0) (Fin.tail w)

theorem decodePrimal (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) (w : Fin (m+1) → K)
    (hw : w ∈ (primalPresentation A b).denote) (hn : 0 ≤ w) (hi : w 0 = 1) :
    ∃ x, Elimination.solve A (b - Fin.tail w) = some x ∧ A *ᵥ x ≤ b := by
  rw [primalPresentation,denote_columns,slackColumns_range] at hw
  obtain ⟨⟨β,u⟩,hu⟩ := hw
  have hβ : β = 1 := (congrFun hu 0).trans hi
  have hAu : A *ᵥ u = b - Fin.tail w := by
    funext j
    have he := congrFun hu j.succ
    change β * b j - (A *ᵥ u) j = w j.succ at he
    change (A *ᵥ u) j = b j - w j.succ
    rw [hβ, one_mul] at he
    linarith only [he]
  obtain ⟨x,hx⟩ := Elimination.solve_complete _ _ ⟨u,hAu⟩
  refine ⟨x,hx,?_⟩
  rw [Elimination.solve_sound _ _ _ hx]
  exact fun j => sub_le_self _ (hn j.succ)

/-- Every normalized multiplier supported inside the returned one represents the same point
of the restricted line. This gives sparsity and minimality for the vector actually returned. -/
theorem sameNormalizedMultiplier (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) (w : Fin (m+1) → K)
    (S : Finset (Fin (m+1))) (hw : w ∈ (dualPresentation A b).denote) (hi : w 0 = 1)
    (hz : ∀ j, j ∉ S → w j = 0)
    (hrank : Module.finrank K ((dualPresentation A b).restrict S).denote = 1)
    (z : Fin m → K) (hAz : Aᵀ *ᵥ z = 0) (hbz : b ⬝ᵥ z = -1)
    (hs : Function.support z ⊆ Function.support (Fin.tail w)) : Fin.tail w = z := by
  let z' : Fin (m+1) → K := Fin.cons 1 z
  have hwS := (restrict_spec (dualPresentation A b) S w).mpr ⟨hw,hz⟩
  have hz'S : z' ∈ ((dualPresentation A b).restrict S).denote := by
    apply (restrict_spec _ _ _).mpr
    constructor
    · exact (mem_dualPresentation A b z').mpr (by simpa [z'] using And.intro hAz hbz)
    · intro j
      refine Fin.cases ?_ (fun k hk => ?_) j
      · intro h0
        exact False.elim (one_ne_zero (α := K) (hi.symm.trans (hz 0 h0)))
      · change z k = 0
        by_contra hnon
        exact hs hnon (hz k.succ hk)
  have him : w = z' := marked_line_unique _ 0 hrank hwS hz'S hi rfl
  rw [him]
  funext j
  rfl

theorem decodeDual (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) (w : Fin (m+1) → K)
    (S : Finset (Fin (m+1))) (hw : w ∈ (dualPresentation A b).denote) (hn : 0 ≤ w) (hi : w 0 = 1)
    (hz : ∀ j, j ∉ S → w j = 0)
    (hrank : Module.finrank K ((dualPresentation A b).restrict S).denote = 1) :
    0 ≤ Fin.tail w ∧ Aᵀ *ᵥ Fin.tail w = 0 ∧ b ⬝ᵥ Fin.tail w = -1 ∧
      (Finset.univ.filter fun j => Fin.tail w j ≠ 0).card ≤ A.rank + 1 := by
  obtain ⟨hA,hb⟩ := (mem_dualPresentation A b w).mp hw
  rw [hi] at hb
  have hy : 0 ≤ Fin.tail w := fun j => hn j.succ
  refine ⟨hy,hA,hb,?_⟩
  obtain ⟨z,_,hAz,hbz,hcard,hs⟩ := Farkas.sparse_certificate_supported A b (Fin.tail w) hy hA
    (hb.trans_lt neg_one_lt_zero)
  have ht := sameNormalizedMultiplier A b w S hw hi hz hrank z hAz hbz hs
  simpa [ht] using hcard

structure LPResult (K : Type*) (m d : ℕ) where
  value : Option (Sum (Fin d → K) (Fin m → K))
  queries : List (Presentation K (m+1))

/-- Solve the input inequalities by feasibility decisions on homogeneous marked subspaces.
A single elimination recovers the original variables on a primal witness. -/
def solveLP (decide : Presentation K (m+1) → Bool) (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) :
    LPResult K m d :=
  let r := recoverColumns decide (slackColumns A b) 0
  let value := if r.primal then (Elimination.solve A (b - Fin.tail r.point)).map Sum.inl
    else some (.inr (Fin.tail r.point))
  ⟨value,r.queries⟩

/-- Both solver outputs, including the support bound, concern the vectors actually returned.
The number of marked-subspace decisions on an `m`-inequality input is exactly `m + 1`. -/
theorem solveLP_spec (decide : Presentation K (m+1) → Bool) (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K)
    (oracle : ∀ u, decide u = true ↔ ∃ x ∈ u.denote, 0 ≤ x ∧ 0 < x 0) :
    let r := solveLP decide A b
    r.queries.length = m + 1 ∧
    ((∃ x, r.value = some (.inl x) ∧ A *ᵥ x ≤ b) ∨
      ∃ y, r.value = some (.inr y) ∧ 0 ≤ y ∧ Aᵀ *ᵥ y = 0 ∧ b ⬝ᵥ y = -1 ∧
        (Finset.univ.filter fun j => y j ≠ 0).card ≤ A.rank + 1) := by
  let r := recoverColumns decide (slackColumns A b) 0
  obtain ⟨hlen,_,hdim,hm,hn,hi,hz⟩ := recoverColumns_spec decide (slackColumns A b) 0 oracle
  change r.point ∈ (if r.primal then primalPresentation A b else dualPresentation A b).denote at hm
  change Module.finrank K ((if r.primal then primalPresentation A b else dualPresentation A b).restrict r.allowed).denote = 1 at hdim
  have hvalue : (solveLP decide A b).value = if r.primal then
      (Elimination.solve A (b - Fin.tail r.point)).map Sum.inl else some (Sum.inr (Fin.tail r.point)) := rfl
  refine ⟨hlen,?_⟩
  cases hp : r.primal with
  | true =>
    left
    have hw : r.point ∈ (primalPresentation A b).denote := by simpa only [hp,ite_true] using hm
    obtain ⟨x,hx,ok⟩ := decodePrimal A b r.point hw hn hi
    exact ⟨x,by rw [hvalue]; simp [hp,hx],ok⟩
  | false =>
    right
    have hw : r.point ∈ (dualPresentation A b).denote := by simpa only [hp,Bool.false_eq_true,ite_false] using hm
    have hd : Module.finrank K ((dualPresentation A b).restrict r.allowed).denote = 1 := by
      have sideEq : (if r.primal then primalPresentation A b else dualPresentation A b) = dualPresentation A b := by simp [hp]
      exact (congrArg (fun side : Presentation K (m+1) => Module.finrank K (side.restrict r.allowed).denote) sideEq).symm.trans hdim
    exact ⟨Fin.tail r.point,by rw [hvalue]; simp [hp],decodeDual A b r.point r.allowed hw hn hi hz hd⟩

/-- Substituting the per-query bound of `restart_recovery` into the actual LP trace.
For `m` inequalities the slack-space dimension is `m+1`, independently of the number of variables. -/
theorem solveLP_service_bound (decide : Presentation K (m+1) → Bool) (A : Matrix (Fin m) (Fin d) K)
    (b : Fin m → K) (oracle : ∀ u, decide u = true ↔ ∃ x ∈ u.denote, 0 ≤ x ∧ 0 < x 0)
    (calls : Presentation K (m+1) → ℕ) (restarts h : ℕ)
    (bounded : ∀ u ∈ (solveLP decide A b).queries, calls u ≤ (restarts+1)*h) :
    ((solveLP decide A b).queries.map calls).sum ≤ (m+1) * ((restarts+1)*h) := by
  have hs := serviceCalls_le calls (solveLP decide A b).queries restarts h bounded
  simpa only [(solveLP_spec decide A b oracle).1] using hs

end Recovery
end LinearProgramming
end Optimization
end OAI
