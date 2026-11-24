import OAI.Computability.VPVNP.CompressionLocalDegree
import OAI.Computability.VPVNP.CompressedRAMMonomials

/-!
# Degree coverage for the fixed iterated compressor

The shrinking and refresh records use the two parts of the common template
alphabet. At every site and on every branch of the actual repeated block,
the degrees in these records bound the degree of its chosen kernel monomial.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.BlockSchedule.Templates

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates)
variable {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)

theorem shrinkProcedure_degreeCovered (i : Fin S.steps) :
    Procedure.DegreeCovered (B.shrinkProcedureWitnesses f hf i) (B.shrinkProcedureRecords f hf i) :=
  Procedure.DegreeCovered.ofPass _ _ _ _ _ _ _ _ _
    (fun g X => B.shrinkPass_degreeCovered f hf i (packingLaneBits_add _ g) X)

theorem refreshProcedure_degreeCovered :
    Procedure.DegreeCovered (B.refreshProcedureWitnesses f hf)
      (B.refreshProcedureRecords f hf) := by
  intro g n h X
  subst n
  exact ⟨B.refreshPass_degreeCovered f hf g X, fun _ => trivial⟩

theorem procedure_degreeCovered :
    Procedure.DegreeCovered (B.procedureWitnesses f hf) (B.recordBounds f hf) :=
  S.assemble_degreeCovered _ _ _ _ _ _ (B.shrinkProcedure_degreeCovered f hf)
    (B.refreshProcedure_degreeCovered f hf)

/-- The actual repeated witnesses in the kernel history obey the degree
bound given by the corresponding repeated records. -/
theorem execute_degreeCovered {n : ℕ} (T : ℕ) (h : T * S.laneBits ≤ n)
    (X : State (S.degreeExponent 0) n) :
    (B.execute f hf T h X).DegreeCovered
      (Procedure.repeatWitnesses (B.procedureWitnesses f hf) _ T n (Nat.add_sub_of_le h).symm X)
      (B.records f hf T h X) :=
  Procedure.repeat_degreeCovered (B.procedure_degreeCovered f hf) _ T n (Nat.add_sub_of_le h).symm X

end Compression.BlockSchedule.Templates

end VPVNP
end Computability
end OAI
