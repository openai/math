import OAI.Computability.BorderVNP.CellGadgetSteps
import OAI.Computability.BorderVNP.CellPrefixLexical

/-! # Lexical index bounds for repeated one-copy factors -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

private theorem row_lexical {α : Type} (off : NatExpr) (ws : List ℕ) (p : α → Bool)
    (rs : List α) : (rowTest (tableWires off ws) p rs).lexical ≤ off.lexical := by
  apply Term.any_lexical_le
  intro t ht
  obtain ⟨z,_,hz⟩ := List.mem_filterMap.mp ht
  split at hz <;> simp_all only [Option.some.injEq, reduceCtorEq]
  subst t
  apply wordIs_lexical_le
  intro a ha
  obtain ⟨w,_,rfl⟩ := List.mem_map.mp ha
  simp [NatExpr.lexical]

/-- A gadget selector references only counters in its supplied offset. -/
theorem factorSelect_lexical_le (off : NatExpr) (id : ℕ) (f : Factor) :
    (factorSelect off id f).lexical ≤ off.lexical := by
  cases f with
  | gadget ws rs => exact row_lexical off ws (fun x => decide (x = id)) rs
  | _ => exact Nat.zero_le _

private theorem pass_lexical (off copy : NatExpr) (f : Factor) :
    (factorPass off copy f).lexical ≤ max off.lexical copy.lexical := by
  cases f with
  | truth w r => exact (row_lexical off w id r).trans (le_max_left ..)
  | sign w r | gadget w r => exact (row_lexical off w (fun _ => true) r).trans (le_max_left ..)
  | unary w p => simp [factorPass, Term.lexical, NatExpr.lexical]

private theorem sign_lexical (off : NatExpr) (f : Factor) : (factorSign off f).lexical ≤ off.lexical := by
  cases f with
  | sign w r => exact row_lexical off w id r
  | _ => exact Nat.zero_le _

private theorem range_lexical (off : NatExpr) (limit : ℕ) (f : Factor) : (rangeTerm limit off f).lexical ≤ off.lexical := by
  cases f with
  | gadget w r => exact row_lexical off w (fun x => decide (limit ≤ x)) r
  | _ => exact Nat.zero_le _

private theorem fragment_lexical (b : BoxBlock) (start : ℕ) (body : FactorBody) {K : ℕ}
    (h : ∀ f j off i, j.lexical = 0 → off.lexical = 0 → i.lexical = 0 → (body f j off i).lexical ≤ K) :
    (b.fragment start body).lexical ≤ K := by
  refine max_le (Nat.zero_le _) (sequence_lexical_le _ ?_)
  intro s hs
  obtain ⟨fj,_,rfl⟩ := List.mem_map.mp hs
  exact h _ _ _ _ rfl rfl rfl

/-- Each sparse box introduces only the innermost copy counter. All three
arguments passed to the body have lexical index zero, irrespective of its copy stride. -/
theorem sweep_lexical_le (body : FactorBody) (bs : List BoxBlock) (start : ℕ) {K : ℕ}
    (h : ∀ f j off i, j.lexical = 0 → off.lexical = 0 → i.lexical = 0 → (body f j off i).lexical ≤ K) :
    (sweep body bs start).lexical ≤ K := by
  induction bs generalizing start with
  | nil => exact Nat.zero_le _
  | cons b bs ih => exact max_le (fragment_lexical b start body h) (ih _)

/-- The complete factor scan fits the directory interpreter's lexical-index bound. -/
theorem factorSweep_lexical_le (D : Directory) (aux : ℕ) :
    (sweep (factorBody aux) D.blocks 0).lexical ≤ 2 := by
  apply sweep_lexical_le
  intro f _ off i _ hoff hi
  let a := NatExpr.add (.lit aux) off
  have ha : a.lexical = 0 := by simp [a,NatExpr.lexical,hoff]
  have hp := pass_lexical a i (f.shift aux)
  have hs := sign_lexical a (f.shift aux)
  change max (factorPass a i (f.shift aux)).guard.lexical (factorSign a (f.shift aux)).sign.lexical ≤ 2
  simp only [Term.guard_lexical, Term.sign_lexical, max_le_iff]
  omega

/-- All range checks fit the same lexical-index bound. -/
theorem Directory.rangeGuard_lexical_le (D : Directory) : D.rangeGuard.lexical ≤ 2 := by
  apply sweep_lexical_le
  intro f j off i _ hoff _
  rw [Term.guard_lexical]
  exact (range_lexical off _ f).trans (by omega)

/-- The prefix count steps add only the candidate counter under the box-copy counter. -/
theorem Gadget.steps_lexical_le (D : Directory) (cap aux id : ℕ) :
    (sweep (stepBody cap aux id) D.blocks 0).lexical ≤ 2 := by
  apply sweep_lexical_le
  intro f j off _ hj hoff _
  let a := NatExpr.add (.lit aux) off
  have ha : a.lexical = 0 := by simp [a, NatExpr.lexical, hoff]
  have hs := factorSelect_lexical_le a id (f.shift aux)
  exact (Prefix.stepGen_lexical_le 0 cap j (factorSelect a id (f.shift aux))).trans (by omega)

end CellSparse

end BorderVNP
end Computability
end OAI
