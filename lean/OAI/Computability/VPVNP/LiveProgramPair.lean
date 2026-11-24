import OAI.Computability.VPVNP.LiveProgramPairStages

/-!
# The four ordinary handoffs before the first-half exponent check

Histograms and accepted compressor choices remain separate indices. The
initializer and copy have one path each. Joining the four stages preserves
the entire report sequence that enters the final exponent check.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairStages
open BurstRAM LiveStageLink
open scoped Classical

namespace Group

variable {G : Group} {m : Memory G.w} {Nom : Type*} {Path : Nom → Type*}

/-- Local path classifications of the four stages preceding the terminal
digit test. Each classification concerns only its native component. -/
structure Chronology (G : Group) (m : Memory G.w) (Nom : Type*) (Path : Nom → Type*) where
  /-- Nomination-stage histories starting in the group’s initial memory and indexed by the
  chosen histogram. -/
  nominations : Indexed G Stage.nominations m Nom
  /-- The unique auxiliary initialization following each nomination in the memory left by that
  nomination. -/
  init (μ : Nom) : Indexed G Stage.auxiliaryInit (nominations.memory μ) Unit
  /-- The unique auxiliary copy following initialization for the chosen nomination. -/
  copy (μ : Nom) : Indexed G Stage.auxiliaryCopy ((init μ).memory ()) Unit
  /-- Pair-stage histories starting in the copy’s actual final memory and indexed by a path for
  that nomination. -/
  pair (μ : Nom) : Indexed G Stage.pair ((copy μ).memory ()) (Path μ)

private def single {β : Unit → Type*} : β () ≃ Σ u : Unit, β u where
  toFun x := ⟨.unit,x⟩
  invFun x := by rcases x with ⟨u,x⟩; cases u; exact x
  left_inv _ := rfl
  right_inv x := by rcases x with ⟨u,x⟩; cases u; rfl

namespace Chronology
variable (A : Chronology G m Nom Path)

/-- Linked reports from nomination, initialization, sparse copy, and the selected pair path
concatenated in execution order. -/
noncomputable def prefixLogs (μ : Nom) (q : Path μ) :=
  A.nominations.logs μ ++ ((A.init μ).logs .unit ++ ((A.copy μ).logs .unit ++ (A.pair μ).logs q))

/-- Every accepting run through this branch has one and only one nomination,
one compressed pair path, and one accepting terminal check. The final check's
cap includes the reports of all four preceding stages. -/
noncomputable def paths (cap : List (Report G.w) → Prop) :
    (Σ μ : Nom, Σ q : Path μ, ActualPaths G.P G.clock 0 ((A.pair μ).memory q)
      (fun tail => cap (A.prefixLogs μ q ++ tail))) ≃ ActualPaths G.P G.clock 0 m cap := by
  apply Equiv.trans _ (A.nominations.continuationEquiv (s' := Stage.auxiliaryInit) rfl cap)
  apply Equiv.sigmaCongrRight
  intro μ
  let check₁ := fun rest => cap (A.nominations.logs μ ++ rest)
  let check₂ := fun rest => check₁ ((A.init μ).logs .unit ++ rest)
  let check₃ := fun rest => check₂ ((A.copy μ).logs .unit ++ rest)
  apply Equiv.trans _ ((A.init μ).continuationEquiv (s' := Stage.auxiliaryCopy) rfl check₁)
  apply Equiv.trans _ single
  apply Equiv.trans _ ((A.copy μ).continuationEquiv (s' := Stage.pair) rfl check₂)
  apply Equiv.trans _ single
  apply Equiv.trans _ ((A.pair μ).continuationEquiv (s' := Stage.exponents) rfl check₃)
  apply Equiv.sigmaCongrRight
  intro q
  simp only [check₁,check₂,check₃,prefixLogs,List.append_assoc]
  exact Equiv.refl _

end Chronology
end Group
end LiveProgram.PairStages

end VPVNP
end Computability
end OAI
