import OAI.Computability.BorderVNP.FiniteProcessorWeight

/-! # Neutral loader, track sweeps and cleanup in the field processor

The accumulated field element is carried by the same elementary transitions of
the existing private compiler. Only an accepting ready row will change it.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldProcessor

open VPVNP.RAMTape TeamSite TeamPrivateTape TeamPrivateFragment
open private ambient install_eq from OAI.Computability.BorderVNP.TeamPrivateValue
variable {Q Γ : Type} {m g : ℕ} {F : Type*} [Field F] [Fintype F]

/-- Field instrumentation of the exact private compiler before its installation. -/
noncomputable def privateCode (M : Macro Q Γ m g) (w : FieldSelect.Return Q Γ F m) :=
  FieldStack.productCode (TeamPrivateCompiler.code M.alphabet M.digit M.inputTape M.table M.start) (privateFactor M w)

omit [Field F] in
private theorem rename_acc {K L Q R : Type} (op : StackOp K Q) (ports : K → L) (labels : Q → R) (acc : F) :
    (op.rename ports labels).rename id (fun q => (q,Fintype.equivFin F acc)) =
      op.rename ports (fun z => (labels z,Fintype.equivFin F acc)) := by cases op <;> rfl

/-- The synchronized tracks update and move at the signed compiler's original cost.
No control internal to this sweep updates the field value. -/
theorem sweep (M : Macro Q Γ m g) (w : FieldSelect.Return Q Γ F m) (c : Command Q (m*g))
    (t : Fin (m*g) → Track) (acc : F) :
    StackRuns (privateCode M w) (2*(m*g)+1)
      (.run (.inl (.sweep c 0 (heads t))),Fintype.equivFin F acc) (ambient t)
      (.run (.inl (.ready c.next (heads (c.apply t)))),Fintype.equivFin F acc) (ambient (c.apply t)) := by
  let T := trackTable M.alphabet M.table
  let dummy : Table Q (m*g) := fun _ _ => .halt false false
  let label := fun q : State Q (m*g) => (TeamPrivateCompiler.Control.run (.inl q),Fintype.equivFin F acc)
  have r := (sweep_run dummy c t).lift Sum.inr Sum.inr_injective label (ambient t) (target := privateCode M w) (by
    intro q hc
    have neutral : privateFactor M w (.run (.inl q)) = 1 := by
      cases q <;> first | rfl | simp [dummy,TeamPrivateTape.code] at hc
    have same : TeamPrivateTape.code T q = TeamPrivateTape.code dummy q := by
      cases q <;> first | rfl | simp [dummy,TeamPrivateTape.code] at hc
    simp only [privateCode,FieldStack.productCode,label,Equiv.symm_apply_apply,neutral,mul_one,
      TeamPrivateCompiler.code,TeamPrivateFragment.rows]
    dsimp only [T] at same
    rw [same]
    cases op : TeamPrivateTape.code dummy q <;> first
      | exact rename_acc _ _ _ _
      | simp [op,StackOp.returns] at hc)
  simpa only [install_eq,label] using r

/-- All private cleanup ports are cleared with the accumulator preserved. -/
theorem cleanup (M : Macro Q Γ m g) (w : FieldSelect.Return Q Γ F m) (out : Option Bool)
    (t : Fin (m*g) → Track) (acc : F) :
    StackRuns (privateCode M w) (TeamPrivateCleanup.steps (bank t))
      (.run (.inr (out,(TeamPrivateCleanup.all (Port (m*g))).body.entry)),Fintype.equivFin F acc) (ambient t)
      (.result out,Fintype.equivFin F acc) (fun _ => []) := by
  let label : (TeamPrivateCleanup.all (Port (m*g))).State → FieldStack.ProductState (TeamPrivateCompiler.Control Q m g) F := fun z =>
    (TeamPrivateCompiler.Control.run (.inr (out,z)),Fintype.equivFin F acc)
  have r := TeamPrivateCleanup.all_linked (privateCode M w) Sum.inr Sum.inr_injective label
    (.result out,Fintype.equivFin F acc) (ambient t) (by
    intro q
    simp only [privateCode,FieldStack.productCode,label,privateFactor,Equiv.symm_apply_apply,mul_one,
      TeamPrivateCompiler.code,TeamPrivateFragment.rows,rename_acc]
    congr 1
    funext v
    cases v <;> rfl)
  have he : installStacks Sum.inr (ambient t) (fun _ => []) = fun _ => [] := by
    funext k; cases k with
    | inl b => rw [installStacks_outside (hl := fun _ => Sum.inr_ne_inl)]; rfl
    | inr p => rw [installStacks_at Sum.inr_injective]
  rwa [he] at r

/-- The physical loader accepts any binary word, preserving the current field element. -/
theorem load (M : Macro Q Γ m g) (w : FieldSelect.Return Q Γ F m) (bits : List Bool) (acc : F) :
    let t := tracks M.alphabet (input M.alphabet.blank M.digit M.inputTape bits)
    StackRuns (privateCode M w) (TeamPrivateInput.steps g bits)
      (.load .start,Fintype.equivFin F acc) (TeamPrivateInput.initial bits)
      (.run (.inl (.ready M.start (heads t))),Fintype.equivFin F acc) (ambient t) := by
  let lab : TeamPrivateInput.State g → FieldStack.ProductState (TeamPrivateCompiler.Control Q m g) F := fun z => (TeamPrivateCompiler.Control.load z,Fintype.equivFin F acc)
  let enter : (Fin (m*g) → Bool) → FieldStack.ProductState (TeamPrivateCompiler.Control Q m g) F := fun bs => (TeamPrivateCompiler.Control.run (.inl (.ready M.start bs)),Fintype.equivFin F acc)
  apply TeamPrivateInput.native_runs M.alphabet M.digit M.inputTape bits (privateCode M w) lab enter
  intro q hc
  have eq (v : TeamPrivateInput.State g) :
      TeamPrivateInput.withHead M.alphabet M.digit M.inputTape lab enter v =
      (TeamPrivateInput.withHead M.alphabet M.digit M.inputTape TeamPrivateCompiler.Control.load
        (fun bs => .run (.inl (.ready M.start bs))) v,Fintype.equivFin F acc) := by cases v <;> rfl
  have hload : TeamPrivateInput.withHead M.alphabet M.digit M.inputTape lab enter q = lab q := by
    cases q <;> first | rfl | simp [TeamPrivateInput.code] at hc
  rw [hload]
  simp only [privateCode,FieldStack.productCode,lab,privateFactor,Equiv.symm_apply_apply,mul_one,
    TeamPrivateCompiler.code,rename_acc]
  congr 1
  funext v
  exact (eq v).symm

end FieldProcessor

end BorderVNP
end Computability
end OAI
