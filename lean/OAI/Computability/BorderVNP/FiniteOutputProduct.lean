import OAI.Computability.BorderVNP.FiniteOutputClock

/-! # Local field multipliers in the finite-field processors

A fixed finite field is held in the finite control. Each local table lookup
can multiply the accumulator by the element attached to its selected control
label. Compiling the accumulator preserves the instruction count, and the
literal one-hot field machine realizes the resulting path products.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldStack

open VPVNP.RAMTape VPVNP.UniversalMachine StackCompiler Filter

variable {K Q : Type} [DecidableEq K] {F : Type*} [Field F] [Fintype F]

/-- Sum of the products of local field weights on the accepting paths. -/
def productPaths (c : StackCode K Q) (factor terminal : Q → F) : ℕ → Q → Stacks K → F
  | 0, _, _ => 0
  | t+1, q, s => factor q * (match c q with
    | .push k b r => productPaths c factor terminal t r (Function.update s k (b :: s k))
    | .pop k f => productPaths c factor terminal t (f (s k).head?) (Function.update s k (s k).tail)
    | .goto r => productPaths c factor terminal t r s
    | .choose l r => productPaths c factor terminal t l s + productPaths c factor terminal t r s
    | .halt b => if b then terminal q else 0)

/-- The field accumulator uses one of finitely many control states. Its numbering
works for fields in any type universe. -/
abbrev ProductState (Q : Type) (F : Type*) [Fintype F] := Q × Fin (Fintype.card F)

/-- Each transition carries its running product into the following control label. -/
noncomputable def productCode (c : StackCode K Q) (factor : Q → F) : StackCode K (ProductState Q F) :=
  fun x => (c x.1).rename id
    (fun q => (q, Fintype.equivFin F ((Fintype.equivFin F).symm x.2 * factor x.1)))

/-- The last instruction's factor and terminal output are included at an accepting halt. -/
noncomputable def productOutput (factor terminal : Q → F) (x : ProductState Q F) : F :=
  (Fintype.equivFin F).symm x.2 * factor x.1 * terminal x.1

/-- One elementary instruction suffices for each source instruction with field weight.
Branch multiplicities and the initial accumulator are retained exactly. -/
theorem productCode_value (c : StackCode K Q) (factor terminal : Q → F) (t : ℕ) (q : Q)
    (s : Stacks K) (acc : F) :
    paths (productCode c factor) (productOutput factor terminal) t (q,Fintype.equivFin F acc) s =
      acc * productPaths c factor terminal t q s := by
  induction t generalizing q s acc with
  | zero => simp [paths, productPaths]
  | succ t ih =>
    rw [paths, productPaths]
    cases h : c q <;> simp only [productCode, Equiv.symm_apply_apply, h, StackOp.rename,
      id_eq, Function.comp_apply, ih, productOutput]
    all_goals simp [mul_assoc, mul_add, mul_ite]

variable [Fintype K] [Fintype Q]

/-- A single fixed literal field program realizes the weighted local validator at
every sufficiently large processor length, including arbitrary link and advice bits. -/
theorem eventually_product_program (input : K) (u : ℕ) (hu : 1 ≤ u) (hexp : 2*(u+2)+1 ≤ 100)
    (src : StackCode K Q) (factor terminal : Q → F) (start : Q) :
    ∃ P : Program, ∀ᶠ n : ℕ in atTop, ∀ payload : Word,
      let raw := programPrefix P ++ payload
      raw.length = n → FPath.U F raw.get =
        productPaths src factor terminal (n^u) start (labeledInput input raw) := by
  let q := (start,Fintype.equivFin F 1)
  refine ⟨clockedMachine input u (productCode src factor) (productOutput factor terminal) q, ?_⟩
  filter_upwards [eventually_prefix_value input u hu hexp (productCode src factor)
    (productOutput factor terminal) q] with n compiled
  intro payload raw hlen
  simpa only [q, productCode_value, one_mul] using compiled payload hlen

end FieldStack

end BorderVNP
end Computability
end OAI
