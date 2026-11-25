import OAI.Hierarchy.DescentLivePrivateWords

namespace OAI
/-! # Restricting the private names preserves their used cardinality -/
namespace Hierarchy.DescentTerminalVertexFields
open DescentKernelHistory
open scoped Classical
noncomputable section

theorem restricted_words {T B : Type} (s : Recipe T B) : Fintype.card s.restricted.UsedWord=Fintype.card s.UsedWord := by
  let allUsed (u : s.UsedWord) : s.restricted.Used u := by
    obtain ⟨i,j,has⟩:=u.property
    refine ⟨i,j,?_⟩
    change s.activePort i j=.inr u
    have read:=(s.activePort_read i j).trans has
    cases h:s.activePort i j with
    | inl b=>simp [h] at read
    | inr v=>exact congrArg Sum.inr (Subtype.ext (by simpa [h] using read))
  exact Fintype.card_congr (⟨fun h=>h.val,fun u=>⟨u,allUsed u⟩,fun _=>rfl,fun _=>rfl⟩:s.restricted.UsedWord≃s.UsedWord)

end
end Hierarchy.DescentTerminalVertexFields

end OAI
