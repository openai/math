import OAI.Computability.NearSquareRoot.ScheduleGeneratorArity

/-! # Simultaneous effective tests for the paper's two call-count bounds -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator
open Filter

noncomputable def midExponent (j : ℕ) : ℝ := 1/2 + 1/(2*((j:ℝ)+2))
noncomputable def targetExponent (j : ℕ) : ℝ := 1/2 + 1/((j:ℝ)+2)

private theorem mid_eq (j : ℕ) : (((j+3:ℕ) : ℝ) / (2*(j+2):ℕ)) = midExponent j := by
  unfold midExponent
  push_cast
  field_simp
  ring

private theorem target_eq (j : ℕ) : (((j+4:ℕ) : ℝ) / (2*(j+2):ℕ)) = targetExponent j := by
  unfold targetExponent
  push_cast
  field_simp
  ring

/-- Given the generated template's computable main call count, batch width
and reserve size, one physical-search-compatible choice of stage arity satisfies
both the upper bound on main calls and the strict recurrence contraction. -/
theorem choose_stage (cost width reserve : ℕ → ℕ → ℕ)
    (hc : Computable₂ cost) (hw : Computable₂ width) (ha : Computable₂ reserve)
    (calls : ∀ j, ∀ᶠ m : ℕ in atTop, 0 < width j m ∧
      (cost j m : ℝ)/(width j m) ≤ (m:ℝ)^(midExponent j))
    (reserves : ∀ j, ∃ β D : ℝ, β ≤ midExponent j ∧ 0 ≤ D ∧
      ∀ᶠ m : ℕ in atTop, (reserve j m : ℝ) ≤ D*(m:ℝ)^β) :
    ∃ m : ℕ → ℕ, Computable m ∧ ∀ j, 2 ≤ m j ∧ 0 < width j (m j) ∧
      (cost j (m j) : ℝ)/(width j (m j)) ≤ (m j:ℝ)^(midExponent j) ∧
      2*(m j:ℝ)^(midExponent j) + 2*reserve j (m j) < (m j:ℝ)^(targetExponent j) := by
  let den (j : ℕ) := 2*(j+2)
  let num (j : ℕ) := j+3
  let outer (j : ℕ) := j+4
  have hd : Computable den := Primrec.nat_mul.to_comp.comp (Computable.const 2)
    (Primrec.nat_add.to_comp.comp Computable.id (Computable.const 2))
  have hg : Computable num := Primrec.nat_add.to_comp.comp Computable.id (Computable.const 3)
  have hp : Computable outer := Primrec.nat_add.to_comp.comp Computable.id (Computable.const 4)
  have dpos (j) : 0 < den j := by dsimp [den]; omega
  let accept (j m : ℕ) := decide (0 < width j m) && volumeTest (cost j m) (width j m) m (num j) (den j)
  have eff : Computable₂ accept := Primrec.and.to_comp.comp
    (Primrec.nat_lt.decide.to_comp.comp (Computable.const 0) hw)
    (computable_volumeTest hc hw Computable.snd (hg.comp Computable.fst) (hd.comp Computable.fst))
  have valid (j m : ℕ) : accept j m = true ↔ 0 < width j m ∧
      (cost j m : ℝ)/(width j m) ≤ (m:ℝ)^(midExponent j) := by
    simp only [accept,Bool.and_eq_true,decide_eq_true_eq]
    by_cases pos : 0 < width j m
    · rw [volumeTest_correct _ _ _ _ _ pos (dpos j),show ((num j : ℝ)/den j) = _ from mid_eq j]
    · simp [pos]
  obtain ⟨m,effm,both⟩ := choose_arity accept eff (fun j => (calls j).mono fun m hm => (valid j m).2 hm)
    reserve ha den num outer hd hg hp dpos (by intro j; dsimp [num,outer]; omega)
    (fun j => by simpa only [num,den,mid_eq] using reserves j)
  refine ⟨m,effm,fun j => ?_⟩
  obtain ⟨pass,large,gap⟩ := both j
  obtain ⟨positive,mainCost⟩ := (valid j _).1 pass
  exact ⟨large,positive,mainCost,by simpa only [num,outer,den,mid_eq,target_eq] using gap⟩

end Generator

end NearSquareRoot
end Computability
end OAI
