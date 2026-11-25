import OAI.Hierarchy.DescentColonyScoreCore

namespace OAI
/-! # The forward binary multiplier search gives the inverse load permutation -/
namespace Hierarchy.DescentColonies
open DescentGL DescentBinaryField
open scoped BigOperators
variable {k : ℕ}

theorem preimageWord_correct (a μ : Bits k) (L : Layout k) (acts : ∀ b,multiply a μ b=L b)
    (dest : Block k) : preimageWord a μ dest=some (L.symm ((address k).symm dest)) := by
  let test := fun b => decide (blockAddress (multiply a μ b)=dest)
  let old := L.symm ((address k).symm dest)
  have hit (b : Bits k) : test b=true ↔ b=old := by
    simp only [test,decide_eq_true_eq,blockAddress_eq,acts]
    constructor
    · intro h
      have t := congrArg (address k).symm h
      have z := congrArg L.symm (show L b=(address k).symm dest by simpa using t)
      simpa only [LinearEquiv.symm_apply_apply] using z
    · rintro rfl
      simp [old]
  have present : (preimageWord a μ dest).isSome :=
    List.find?_isSome.mpr ⟨old,mem_words _,(hit _).mpr rfl⟩
  cases found : preimageWord a μ dest with
  | none => simp [found] at present
  | some b => exact congrArg some ((hit b).mp (List.find?_some found))

theorem multiplierLoad_pullback {V : Type*} (weight : V→Block k→ℕ) (a μ : Bits k) (L : Layout k)
    (acts : ∀b,multiply a μ b=L b) (v : V) (x : Block k) :
    multiplierLoad weight a μ v x=weight v ((rearrange L).symm x) := by
  rw [multiplierLoad,preimageWord_correct a μ L acts]
  change weight v (blockAddress (L.symm ((address k).symm x))) = _
  exact congrArg (weight v) (blockAddress_eq _)

end Hierarchy.DescentColonies

end OAI
