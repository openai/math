import OAI.Hierarchy.DescentOriginalPublicOperandBoard

namespace OAI
namespace Hierarchy.DescentResetPublicOperandBook.Config
open DescentSIMDLookup DescentPackedZip DescentRotorWindowArchive
noncomputable section
variable {n m : ℕ} {A B : Config} (shape : A=B) (dim : n=m) (raw : A.Data n)

/-- Renaming the public menu and board leaves each scalar and the chronological
matrix read at the same numerical address in the original packet. -/
theorem good_native_row :
    (∀j,(B.oldConfig.header (B.basic (relabel shape dim raw)) j).val=(A.oldConfig.header (A.basic raw) j).val) ∧
    (∀j,(B.reg (relabel shape dim raw) j).val=(A.reg raw j).val) ∧
    (∀(j : Fin B.oldConfig.count) (k : Fin A.oldConfig.count),j.val=k.val→∀f,
      (B.oldConfig.digit (B.basic (relabel shape dim raw)) j f).val=(A.oldConfig.digit (A.basic raw) k f).val) ∧
    ∀(j : Input B.oldDegree B.donors B.oldCap) (k : Input A.oldDegree A.donors A.oldCap),
      (ix j).val=(ix k).val→(B.oldData (relabel shape dim raw) j).val=(A.oldData raw k).val :=by
  subst B
  subst m
  refine ⟨fun _=>rfl,fun _=>rfl,?_,?_⟩
  · intro j k same f
    cases Fin.ext same
    rfl
  · intro j k same
    cases ix.injective (Fin.ext same)
    rfl

end
end Hierarchy.DescentResetPublicOperandBook.Config

end OAI
