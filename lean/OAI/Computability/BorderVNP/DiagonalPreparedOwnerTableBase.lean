import OAI.Computability.BorderVNP.DiagonalPreparedOwnedJoin

/-! # The owned report table at the common address of the actual prepared prefix -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.PreparedOwned

open TeamContraction TeamContraction.ProcessorSlots CellDispatch CellMacro.Generator BorderVNP.Cube
open scoped Classical

variable {R n w axes b h K s : ℕ} {id : TableEntry axes b h K s → ℕ} {gen : Fragment IO}
    {X Raw Hist Claim : Type} {Route : Hist → Type}
    {Report : (i : Raw) → (q : Hist) → Route q → Type}
    (S : X → Fin (R+1) → PositiveTeam id gen n w)
    (prep : JointBeforeCells S ≃ PreparedFields Raw Hist Claim Route Report)
    (cells : Hist → ℕ) (owner : (q : Hist) → Route q → Fin (cells q) → Fin (R+1))

local notation "Fields" => PreparedFields Raw Hist Claim Route Report

/-- Every field and team sees the routed owner table at its actual
post-call memory, beginning at the given physical directory address. -/
def OwnerTablesAt (base : Fields → Fin (R+1) → ℕ) : Prop :=
  ∀ (f : Fields) u, let z := prep.symm f
    OwnerTable (S z.1 u).pub ((S z.1 u).postMemory (z.2 u))
      ⟨u.val,base f u,cells f.2.1⟩ (PositiveTeam.ownerWord (owner f.2.1 f.2.2.1))

/-- Package the common allocated address with the rows already read at
that address. Its proof is the table argument of the prepared column. -/
def certifiedTableBase (address : ℕ) (observed : OwnerTablesAt S prep cells owner (fun _ _ => address)) :
    {base : Fields → Fin (R+1) → ℕ // OwnerTablesAt S prep cells owner base} :=
  ⟨fun _ _ => address, observed⟩

/-- All actual fields and teams use exactly the supplied directory address. -/
theorem certifiedTableBase_address (address : ℕ)
    (observed : OwnerTablesAt S prep cells owner (fun _ _ => address)) (f : Fields) (u : Fin (R+1)) :
    (certifiedTableBase S prep cells owner address observed).val f u = address := rfl

end RoutingISA.Evaluator.PreparedOwned

end BorderVNP
end Computability
end OAI
