import OAI.Hierarchy.DescentOriginalPublicOperandBoard

namespace OAI
/-! # Reading the original header, chronological donor and fallback packet after reindexing -/
namespace Hierarchy.DescentResetPublicOperandBook.Config
open DescentFallbackPeriod
noncomputable section
variable {n₀ n₁ : ℕ} {A B : Config} {C : DescentFallbackOperandBranch.Config}

theorem relay_relabel (shape : A=B) (dim : n₀=n₁) (adjusted : C=B.oldConfig) (raw : A.Data n₀) :
    let row : C.Data n₁ := adjusted.symm ▸ B.basic (relabel shape dim raw)
    (∀j,(C.header row j).val=(A.oldConfig.header (A.basic raw) j).val) ∧
    (∀(i : Fin C.count) (j : Fin A.oldConfig.count),i.val=j.val→∀f,
      (C.digit row i f).val=(A.oldConfig.digit (A.basic raw) j f).val) ∧
    ∀(i : Input C.oldDegree C.donors C.oldCap n₁ C.residual)
      (j : Input A.oldConfig.oldDegree A.oldConfig.donors A.oldConfig.oldCap n₀ A.oldConfig.residual),
      (number i).val=(number j).val→(C.packet row i).val=(A.oldConfig.packet (A.basic raw) j).val :=by
  subst B
  subst n₁
  subst C
  refine ⟨fun _=>rfl,?_,?_⟩
  · intro i j same f
    exact congrArg (fun z=>(A.oldConfig.digit (A.basic raw) z f).val) (Fin.ext same)
  · intro i j same
    exact congrArg (fun z=>(A.oldConfig.packet (A.basic raw) z).val) (number.injective (Fin.ext same))

end
end Hierarchy.DescentResetPublicOperandBook.Config

end OAI
