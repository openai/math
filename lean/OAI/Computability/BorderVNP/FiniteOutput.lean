import OAI.Computability.BorderVNP.SignedPaths
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Field.Defs

/-!
# The finite-field universal path tensor of §2.2

Fix a numbering of a finite field. Its output code marks exactly one of the first
`card F` work-tape cells at and to the right of the halting head. A binary one marks
a cell. Blanks and binary zeros leave it unmarked. Invalid codes contribute zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FPath

open VPVNP.UniversalMachine

variable (F : Type*) [Field F] [Fintype F]

/-- The fixed field code places a one in the numbered position of the element. -/
noncomputable def code (a : F) (i : Fin (Fintype.card F)) : Bool :=
  decide (i = Fintype.equivFin F a)

omit [Field F] in
/-- Distinct field elements receive distinct output words. -/
theorem code_injective : Function.Injective (code F) := by
  intro a b h
  have he := congrFun h (Fintype.equivFin F a)
  simpa [code] using he

/-- Decode a valid field output, assigning zero to every malformed word. -/
noncomputable def decodeWord (bits : Fin (Fintype.card F) → Bool) : F := by
  classical
  exact if h : ∃ a, code F a = bits then h.choose else 0

/-- Every field element is available as a path output. -/
theorem decodeWord_code (a : F) : decodeWord F (code F a) = a := by
  classical
  unfold decodeWord
  split
  next h => exact code_injective F h.choose_spec
  next h => exact (h ⟨a, rfl⟩).elim

/-- Read the field output only on an accepting halt. -/
noncomputable def output {e : ℕ} (c : Config e) : F :=
  if c.state.val = 1 then
    decodeWord F fun i => decide ((c.secondTape.right₀.nth i.val).val = 2)
  else 0

/-- Run a decoded literal program with exactly one padding bit per clock tick. -/
noncomputable def witness {n : ℕ} (x : Fin n → Bool) (w : Fin (n ^ 100) → Bool) : F :=
  match decode (List.ofFn x) with
  | none => 0
  | some p => output F ((List.ofFn w).foldl (choiceStep p) (initial p (List.ofFn x)))

/-- The universal field-valued tensor, with addition in the output field. -/
noncomputable def U {n : ℕ} (x : Fin n → Bool) : F :=
  ∑ w, witness F x w

/-- The number of padded words of weight `v`, before reduction in the field. -/
noncomputable def count {n : ℕ} (x : Fin n → Bool) (v : F) : ℕ := by
  classical
  exact (Finset.univ.filter (fun w => witness F x w = v)).card

/-- Grouping paths by their field output recovers the universal tensor value. -/
theorem U_eq_count_smul {n : ℕ} (x : Fin n → Bool) :
    U F x = ∑ v : F, count F x v • v := by
  classical
  unfold U count
  rw [← Finset.sum_fiberwise_of_maps_to
    (show ∀ w ∈ Finset.univ, witness F x w ∈ (Finset.univ : Finset F)
      from fun _ _ => Finset.mem_univ _) (fun w => witness F x w)]
  apply Finset.sum_congr rfl
  intro v _
  rw [← Finset.sum_const]
  exact Finset.sum_congr rfl fun w hw => (Finset.mem_filter.mp hw).2

/-- Recursive field sum over the leaves of the actual bounded binary path tree. -/
noncomputable def paths (p : Program) : ℕ → Config p.extra → F
  | 0, c => output F c
  | t + 1, c =>
    if c.state.val = 1 then output F c else if c.state.val = 0 then 0 else
      match branches p c with
      | .stop => 0
      | .one a => paths p t (advance c a)
      | .two a b => paths p t (advance c a) + paths p t (advance c b)

private theorem paths_halt (p : Program) (t : ℕ) (c : Config p.extra) (h : c.state.val = 1) :
    paths F p t c = output F c := by cases t <;> simp [paths, h]

private theorem paths_reject (p : Program) (t : ℕ) (c : Config p.extra) (h : c.state.val = 0) :
    paths F p t c = 0 := by cases t <;> simp [paths, output, h]

private theorem paths_step (p : Program) (t : ℕ) (c : Config p.extra) :
    paths F p (t + 1) c = paths F p t (choiceStep p c false) + paths F p t (choiceStep p c true) := by
  have hbad := paths_reject F p t (reject c) rfl
  by_cases ha : c.state.val = 1
  · simp [paths, choiceStep, ha, hbad, paths_halt F p t c ha]
  by_cases hr : c.state.val = 0
  · simp [paths, choiceStep, hr, paths_reject F p t c hr]
  cases h : branches p c <;> simp [paths, choiceStep, ha, hr, h, hbad]

/-- Early halts contribute exactly once to the field sum, with unused choice bits zero. -/
theorem paths_eq_sum (p : Program) (t : ℕ) (c : Config p.extra) :
    paths F p t c = ∑ w : Fin t → Bool, output F ((List.ofFn w).foldl (choiceStep p) c) := by
  induction t generalizing c with
  | zero => simp [paths]
  | succ t ih =>
    rw [paths_step, ih, ih, ← (Fin.consEquiv (fun _ : Fin (t + 1) => Bool)).sum_comp,
      Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
    simp [Fin.consEquiv]

/-- The witness definition is the finite-field sum over the decoded machine's paths. -/
theorem U_eq_paths {n : ℕ} (x : Fin n → Bool) :
    U F x = (decode (List.ofFn x)).elim 0 (fun p => paths F p (n ^ 100) (initial p (List.ofFn x))) := by
  cases h : decode (List.ofFn x) <;> simp [U, witness, h, paths_eq_sum]

end FPath

end BorderVNP
end Computability
end OAI
