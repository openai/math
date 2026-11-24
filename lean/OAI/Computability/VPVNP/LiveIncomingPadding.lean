import OAI.Computability.VPVNP.LiveGroupContraction
import OAI.Computability.VPVNP.LiveHeaderPhysical

/-!
# Canonical incoming cuts in the live group count

Section 14.1 checks the padding of both incident cuts. The recurrence for
exponent vectors already checks a pair's outgoing padding, and a tail step
checks its outgoing configuration. Here those outgoing conditions imply
every incoming format check whenever the product of all groups is nonzero.
The incoming midpoint is a pair-format cut, even at the first tail group.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ChainAssignments

open CutSchedule ExponentTrace LiveChain LiveHeaderDescriptors
open scoped Classical

variable {h Δ t Z M w : ℕ} {Nom : Type*} [Fintype Nom]
variable {Path : Exterior h Δ → Fin (2^h) → Nom → Type*} [∀ ξ i μ, Fintype (Path ξ i μ)]

/-- The trailing padding on an outgoing pair-format cut, at its physical sites. -/
def pairPadding (t Z : ℕ) (bits : LiveBits h Δ) (i : Fin (2^h)) : Prop :=
  Physical.ZeroSlice (bits i) (span .pair (width (h+1) Δ (i.val+1)) Δ (t*Z) 0 .padding)

/-- The physical check on the input side of a group. The initial cut has
no condition. Up to the midpoint the incoming padding is checked. Later
incoming cuts must decode to canonical evaluator configurations. -/
def incomingChecks (t Z : ℕ) {E : UniversalMachine.Program}
    (layout : LiveEvaluatorTail.Layout E.extra M w Δ) (cuts : AllCuts h Δ) (j : Fin (2^(h+1))) : Prop :=
  (∀ i, j.castSucc = firstCut i → pairPadding t Z (liveCutEquiv h Δ cuts).1 i) ∧
  ∀ k, j.castSucc = laterCut k → (LiveEvaluatorTail.readCut layout k (cuts (laterCut k))).isSome = true

private theorem first_ne_later (i : Fin (2^h)) (k : Fin (2^h-1)) : firstCut i ≠ laterCut k := by
  intro he
  have hh := congrArg Fin.val he
  have hi := i.isLt
  dsimp [firstCut,laterCut] at hh
  omega

private theorem first_inj {i j : Fin (2^h)} (he : firstCut i = firstCut j) : i = j := by
  apply Fin.ext
  have := congrArg Fin.val he
  simpa [firstCut] using this

private theorem later_inj {i j : Fin (2^h-1)} (he : laterCut i = laterCut j) : i = j := by
  apply Fin.ext
  have := congrArg Fin.val he
  simpa [laterCut] using this

theorem incomingChecks_initial (t Z : ℕ) {E : UniversalMachine.Program}
    (layout : LiveEvaluatorTail.Layout E.extra M w Δ) (cuts : AllCuts h Δ) {j : Fin (2^(h+1))}
    (first : j.val = 0) : incomingChecks t Z layout cuts j := by
  constructor <;> intro i he <;> have := congrArg Fin.val he <;>
    simp [firstCut,laterCut,first] at this

/-- This includes the input of the first tail group, whose cut carries
exponents rather than a serialized evaluator state. -/
theorem incomingChecks_pair (t Z : ℕ) {E : UniversalMachine.Program}
    (layout : LiveEvaluatorTail.Layout E.extra M w Δ) (cuts : AllCuts h Δ) {j : Fin (2^(h+1))}
    (i : Fin (2^h)) (hin : j.castSucc = firstCut i) :
    incomingChecks t Z layout cuts j ↔ pairPadding t Z (liveCutEquiv h Δ cuts).1 i := by
  constructor
  · exact fun hc => hc.1 i hin
  · intro hc
    constructor
    · intro i' he
      obtain rfl := first_inj (hin.symm.trans he)
      exact hc
    · intro k he
      exact (first_ne_later i k (hin.symm.trans he)).elim

/-- A tail-format input passes exactly when its literal cut equals one of
the canonical mode/configuration/padding strings. -/
theorem incomingChecks_tail (t Z : ℕ) {E : UniversalMachine.Program}
    (layout : LiveEvaluatorTail.Layout E.extra M w Δ) (cuts : AllCuts h Δ) {j : Fin (2^(h+1))}
    (k : Fin (2^h-1)) (hin : j.castSucc = laterCut k) :
    incomingChecks t Z layout cuts j ↔ ∃ s, cuts (laterCut k) = LiveEvaluatorTail.writeCut layout k s := by
  constructor
  · intro hc
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (hc.2 k hin)
    exact ⟨s, (LiveEvaluatorTail.readCut_iff layout k _ s).mp hs⟩
  · rintro ⟨s, hs⟩
    constructor
    · intro i he
      exact (first_ne_later i k (he.symm.trans hin)).elim
    · intro k' he
      obtain rfl := later_inj (hin.symm.trans he)
      rw [(LiveEvaluatorTail.readCut_iff layout k _ s).mpr hs]
      rfl

/-- The first tail group receives the last cumulative exponent vector.
It validates the midpoint's remaining bits using the first-half layout. -/
theorem incomingChecks_midpoint (t Z : ℕ) {E : UniversalMachine.Program}
    (layout : LiveEvaluatorTail.Layout E.extra M w Δ) (cuts : AllCuts h Δ) {j : Fin (2^(h+1))}
    (mid : j.val = 2^h) :
    incomingChecks t Z layout cuts j ↔ pairPadding t Z (liveCutEquiv h Δ cuts).1
      ⟨2^h-1,by have := Nat.two_pow_pos h; omega⟩ := by
  apply incomingChecks_pair
  apply Fin.ext
  dsimp [firstCut]
  have := Nat.two_pow_pos h
  omega

/-- Every nonzero pair factor enforces the physical zero-padding interval
of its output cut. -/
theorem pairCount_padding (fit : 1+t*Z ≤ Δ) (inc : ∀ ξ i μ, Path ξ i μ → Fin t → ℕ)
    (bits : LiveBits h Δ) (i : Fin (2^h)) (ok : pairCount fit inc bits i ≠ 0) :
    pairPadding t Z bits i := by
  apply (Physical.pair_padding_zero (Nat.succ_pos _) i.isLt fit (bits i)).mpr
  by_contra bad
  apply ok
  unfold pairCount
  apply Finset.sum_eq_zero
  intro μ _
  apply Finset.sum_eq_zero
  intro q _
  exact ite_eq_right (fun hv => bad (congrArg (fun a => a.2.2.2) hv.1))

/-- Every nonzero tail factor with an outgoing interior cut has produced a
decodable canonical configuration. -/
theorem tailCount_decoded {E : UniversalMachine.Program} (layout : LiveEvaluatorTail.Layout E.extra M w Δ)
    (init : LiveEvaluatorEncoding.Code E.extra M) (lst : TailBits h Δ) (k : Fin (2^h-1))
    (ok : tailCount E layout init lst ⟨k.val,by have := k.isLt; omega⟩ ≠ 0) :
    (LiveEvaluatorTail.readCut layout k (lst k)).isSome = true := by
  let i : Fin (2^h) := ⟨k.val,by have := k.isLt; omega⟩
  have hj : k.val+1 ≠ 2^h := by have := k.isLt; omega
  have hbd : LiveEvaluatorTail.boundary layout init lst i.succ = LiveEvaluatorTail.readCut layout k (lst k) := by
    simp [LiveEvaluatorTail.boundary, i, hj]
  cases he : LiveEvaluatorTail.readCut layout k (lst k) with
  | some _ => rfl
  | none =>
    apply False.elim (ok ?_)
    unfold tailCount
    apply Finset.sum_eq_zero
    intro bit _
    apply ite_eq_right
    rintro ⟨s,u,_,hout,_,_⟩
    change LiveEvaluatorTail.boundary layout init lst i.succ = some u at hout
    rw [hbd, he] at hout
    contradiction

end ChainAssignments

end VPVNP
end Computability
end OAI
