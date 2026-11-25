import OAI.Hierarchy.DescentTerminalEpochChart

namespace OAI
/-! # Low-level observation prefixes and the size of a fixed selector directory -/
namespace Hierarchy.DescentTerminalEpochDecoder
open DescentTerminalEpochChart
def Uniform {A : Type} (C : ℕ) (ts : List (Source A)) : Prop := ∀a∈ts,a.C=C
def seatBill {A : Type} (ls : List (Source A)) := (ls.map Source.seats).sum
end Hierarchy.DescentTerminalEpochDecoder

namespace Hierarchy.DescentTerminalEpochHeader
open DescentTerminalEpochChart
private theorem observation_ext {a b : Observation} (image : a.image=b.image) (count : a.count=b.count) : a=b := by
  rcases a with ⟨C₁,d₁,n₁,v₁⟩
  rcases b with ⟨C₂,d₂,n₂,v₂⟩
  cases count
  change (⟨C₁,n₁,v₁⟩ : RawImage)=⟨C₂,n₂,v₂⟩ at image
  cases image
  rfl

theorem prefix_fields {as bs : List Observation}
    (images : List.IsPrefix (as.map Observation.image) (bs.map Observation.image))
    (counts : List.IsPrefix (as.map Observation.count) (bs.map Observation.count)) :
    List.IsPrefix as bs := by
  induction as generalizing bs with
  | nil=>simp
  | cons a as ih=>
    cases bs with
    | nil=>simp at images
    | cons b bs=>
      simp only [List.map_cons,List.cons_prefix_cons] at images counts ⊢
      exact ⟨observation_ext images.1 counts.1,ih images.2 counts.2⟩

end Hierarchy.DescentTerminalEpochHeader

end OAI
