import OAI.Hierarchy.TraceShrinkWordConstants
import OAI.ThreeFlat.Diagonal.PhysicalRefreshAdmission
import OAI.ThreeFlat.Diagonal.PhysicalProgramRecords

namespace OAI
/-! # Fixed table and alphabet bounds for arbitrary repetition counts

The public program template contains the finitely many shrinking tables and the
one refresh grid of a block. Its repeated program selects only from those constants.
-/

noncomputable section

namespace ThreeFlat.Diagonal.NavigationPass
open PhysicalStage
variable {F : Type} [Field F]

/-- The fixed, age-independent width threshold of any row in a finite physical program. -/
def traceWordConstants : {s : ℕ} → Program F s → List ℕ
  | _,.done _=>[]
  | _,.shrink s t T _ tail=>Hierarchy.TraceShrinkRetained.fixedWords T s (2^t)::traceWordConstants tail
  | _,.refresh _ _ _ _ _ _ _ T _ _ _ _ _ _ _ tail=>refreshFixedWords T::traceWordConstants tail

end ThreeFlat.Diagonal.NavigationPass

namespace Hierarchy.TraceStageConstants
open ThreeFlat Diagonal Diagonal.PhysicalStage Diagonal.NavigationPass
open Filter
open scoped BigOperators Classical

variable {F : Type} [Field F] (B : PhysicalStage.Block F)

private def words : StaticMotif F → ℕ
  | .shrink s D T => TraceShrinkRetained.fixedWords T s D
  | .refresh _ _ _ _ _ T => refreshFixedWords T

def bound : ℕ :=
  (∑ i : Fin B.levels,TraceShrinkRetained.fixedWords B.shrink (B.exponent i.val)
    (2^B.exponent (i.val+1)))+refreshFixedWords B.refresh

private theorem words_le {m : StaticMotif F} (ok : B.publicTemplate m) : words m≤bound B := by
  rcases ok with ⟨i,rfl⟩ | rfl
  · apply le_trans _ (Nat.le_add_right ..)
    exact Finset.single_le_sum (fun j _=>Nat.zero_le (TraceShrinkRetained.fixedWords B.shrink
      (B.exponent j.val) (2^B.exponent (j.val+1)))) (Finset.mem_univ i)
  · exact Nat.le_add_left ..

private theorem supported {s : ℕ} (P : Program F s) (ok : P.SupportedBy B.publicTemplate) :
    ∀ x∈traceWordConstants P, x≤bound B := by
  induction P with
  | done => intro x h; simp [traceWordConstants] at h
  | shrink s t T small tail ih =>
    intro x present
    rcases List.mem_cons.mp present with eq | past
    · rw [eq]
      exact words_le B ok.1
    · exact ih ok.2 x past
  | refresh s t h pad g γ C T hm hh sym rows zero conn deg tail ih =>
    intro x present
    rcases List.mem_cons.mp present with eq | past
    · rw [eq]
      exact words_le B ok.1
    · exact ih ok.2 x past

theorem repeated (n x : ℕ) (occurs : x∈traceWordConstants (B.repeat n)) : x≤bound B :=
  supported B (B.repeat n) (B.repeat_supported n) x occurs

theorem eventual : ∀ᶠ w : ℕ in atTop,
    B.alphabetCap≤2^w ∧ ∀ n x, x∈traceWordConstants (B.repeat n) → x≤2^w := by
  filter_upwards [eventually_ge_atTop (B.alphabetCap+bound B)] with w large
  have floor : w≤2^w := Nat.lt_two_pow_self.le
  refine ⟨by omega,?_⟩
  intro n x occurs
  exact (repeated B n x occurs).trans (by omega)


end Hierarchy.TraceStageConstants

end
end OAI
