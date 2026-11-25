import OAI.Computability.NearSquareRoot.InterchangeAtlasVerifier
import OAI.Computability.NearSquareRoot.InterchangeFlatAtlasCheck
import OAI.Computability.NearSquareRoot.InterchangeFlatAtlasMask
import OAI.Computability.NearSquareRoot.InterchangeFlatAtlasPacking

/-! # Equivalence between numerical tests and the finite chart conditions -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FlatAtlas

open Interchange Interchange.StageLedger Interchange.RectangleAtlas Opcode

private theorem allN_iff {k : ℕ} {p : ℕ → Bool} : allN k p = true ↔ ∀ j : Fin k, p j = true := by
  simp only [allN, List.all_eq_true, List.mem_range]
  exact ⟨fun h j => h j j.isLt, fun h j hj => h ⟨j,hj⟩⟩

private theorem sides_iff {p : Bool → Bool} : sides p = true ↔ ∀ s, p s = true := by
  simp only [sides, Bool.and_eq_true, Bool.forall_bool]

private theorem guard_iff {p q : Bool} : (!p || q) = true ↔ (p = true → q = true) := by
  cases p <;> simp

variable {L T b a m : ℕ} {bits : List Bool} {r : Fin T → Rectangle (Fin L)}

/-- Every active native chart receives its price and legality checks. Every occupied
endpoint is tested in both coordinate diagrams and every label receives its pivot test. -/
theorem valid_iff_on (H : Represents bits r) (A : List Word) :
    valid b a m L T bits A = true ↔
      (∀ c : Chart r m, shape b a m A (AddressROM.affordable a c) (chartIndex c) = true) ∧
      (∀ s (j : Fin m) (u : Endpoint r s), edge a m L T A s j u.1 u.2.val = true) ∧
      ∀ (j : Fin m) (v : Fin L), diag a m L A j v = true := by
  simp only [valid, Bool.and_eq_true, sides_iff, allN_iff, guard_iff]
  constructor
  · rintro ⟨⟨⟨⟨labels,common⟩,prep⟩,localRows⟩,diagonal⟩
    refine ⟨?_,?_,diagonal⟩
    · rintro (⟨s,j,v⟩ | ⟨j,t⟩ | ⟨s,v,t,h⟩ | ⟨j,s,v,t,h⟩)
      · exact labels s j v
      · exact common j t
      · exact prep s v t ((H s t v).mpr h)
      · exact (localRows s j v t ((H s t v).mpr h)).1
    · rintro s j ⟨v,t,h⟩
      exact (localRows s j v t ((H s t v).mpr h)).2
  · rintro ⟨forms,edges,diagonal⟩
    refine ⟨⟨⟨⟨fun s j v => forms (Chart.label s j v), fun j t => forms (Chart.common j t)⟩,?_⟩,?_⟩,diagonal⟩
    · intro s v t h
      exact forms (Chart.prepare (s:=s) ⟨v,t,(H s t v).mp h⟩)
    · intro s j v t h
      let u : Endpoint r s := ⟨v,t,(H s t v).mp h⟩
      exact ⟨forms (Chart.localMap j u), edges s j u⟩

end FlatAtlas

end NearSquareRoot
end Computability
end OAI
