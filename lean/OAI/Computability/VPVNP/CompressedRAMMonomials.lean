import OAI.Computability.VPVNP.IteratedCompression
import OAI.Computability.VPVNP.ShrinkProcedureWitness
import OAI.Computability.VPVNP.RefreshProcedureWitness
import OAI.Computability.VPVNP.CursorStateCount

/-!
# Monomial paths in the iterated compression of the RAM network

Equation (12.2) sums the parameter monomials of the actual compression
procedure on the padded cursor graph. The two fixed templates determine
all the local witnesses. The chosen term may change both the next state and
its kernel, at every step and in every block.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.BlockSchedule.Templates

open NetworkKernel

variable {k : Type*} [Field k] {S : BlockSchedule k}
variable (B : S.Templates) {A : Type*} [CommRing A] (κ : B.Entry → A) (hκ : B.IsSolution κ)

/-- Every map entry of the scheduled block has finite monomial witnesses in
the common alphabet of the two templates. -/
noncomputable def procedureWitnesses : (B.procedure κ hκ).MapWitnesses κ :=
  S.assembleBlockWitnesses _ _ (B.shrinkProcedureWitnesses κ hκ) (B.refreshProcedureWitnesses κ hκ)

/-- Local witnesses for the complete history in Theorem 7.1. -/
noncomputable def executeWitnesses {n : ℕ} (T : ℕ) (h : T * S.laneBits ≤ n)
    (X : State (S.degreeExponent 0) n) :
    (B.execute κ hκ T h X).history.KernelWitnesses κ :=
  (B.execute κ hκ T h X).historyWitnesses
    (Procedure.repeatWitnesses (B.procedureWitnesses κ hκ) _ T n (Nat.add_sub_of_le h).symm X)

end Compression.BlockSchedule.Templates

namespace CursorNetwork

open CursorRouting Compression NetworkKernel BurstRAM BurstRAM.PrivateRAM

variable {k : Type*} [Field k] {S : BlockSchedule k} {D e w p r k' base lanes : ℕ} [NeZero D]

/-- The sum over the expanded paths of the concrete compression is the
integer machine path count specialized to the coefficient ring. A choice
retains the term sequence, final edge values, and all local witnesses. -/
noncomputable def compressedRAMCount (B : S.Templates) {A : Type*} [CommRing A]
    (κ : B.Entry → A) (hκ : B.IsSolution κ) (M : Machine w p r k') (fuel : ℕ)
    (initial : Word w) (header : ℕ → Word w) (hw : 2 ≤ w) (hc : 2 ^ D * 2 ^ e < 2 ^ w)
    (labels : Fin D ≃ Fin base ⊕ Fin lanes) (hD : 1 < D) (T : ℕ) (hT : T * S.laneBits ≤ lanes) :
    MonomialWitness κ (Nat.card (ActualPaths M.program fuel initial
      (RAMMemory.initialMemory (2 ^ D) header) (withinCaps (2 ^ D) (2 ^ e))) : A) :=
  let pad := S.baseDegree - 2
  have hpad : 2 + pad = 2 ^ S.degreeExponent 0 := Nat.add_sub_of_le S.degree_bounds.1
  let X := cursorState labels hD hpad (ramFieldBits (2 ^ e) w : RAMSystem D → ℕ)
  expandedRAMStateCount M fuel initial header hw hc labels hD hpad
    (B.execute κ hκ T hT X).history (B.executeWitnesses κ hκ T hT X)

end CursorNetwork

end VPVNP
end Computability
end OAI
