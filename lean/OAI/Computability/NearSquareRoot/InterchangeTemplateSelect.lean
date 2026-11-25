import OAI.Computability.NearSquareRoot.InterchangeTemplateSearch
import OAI.Computability.NearSquareRoot.InterchangeTemplateExists

/-! # Effective, uniform selection of all recursive interchange instructions -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.Template.Data

private theorem hasCode (j t : ℕ) : ∃ n, Valid j t (enumerate n) := by
  obtain ⟨x,h⟩ := exists_valid j t
  exact ⟨Encodable.encode x, by simpa only [enumerate_encode] using h⟩

/-- The code of the first passing finite ROM. The termination proof uses
the Hamming construction; each iteration only tests the supplied numeral. -/
def first (j threshold : ℕ) := Nat.find (hasCode j threshold)

def select (j threshold : ℕ) := enumerate (first j threshold)

theorem selected_valid (j threshold : ℕ) : Valid j threshold (select j threshold) :=
  Nat.find_spec (hasCode j threshold)

theorem computable_first : Computable₂ first := by
  let test (s n : ℕ) := decide (Valid (Nat.unpair s).1 (Nat.unpair s).2 (enumerate n))
  have htest : Primrec₂ test := (primrec_valid
    ((Primrec.fst.comp Primrec.unpair).comp Primrec.fst)
    ((Primrec.snd.comp Primrec.unpair).comp Primrec.fst)
    (primrec_enumerate.comp Primrec.snd)).decide.to₂
  have hex (s : ℕ) : ∃ n, test s n = true := by
    obtain ⟨n,h⟩ := hasCode (Nat.unpair s).1 (Nat.unpair s).2
    exact ⟨n,decide_eq_true h⟩
  obtain ⟨pick,hpick,h⟩ := NearSquareRoot.Generator.first_certificate test htest.to_comp hex
  apply (hpick.comp₂ Primrec₂.natPair.to_comp).of_eq
  rintro ⟨j,t⟩
  obtain ⟨hit,minimal⟩ := h (Nat.pair j t)
  have good : Valid j t (enumerate (pick (Nat.pair j t))) := by simpa [test] using hit
  apply Nat.le_antisymm _ (Nat.find_min' (hasCode j t) good)
  by_contra! above
  have before := minimal _ above
  have hbad : ¬ Valid j t (enumerate (first j t)) := by simpa [test, first] using before
  exact hbad (selected_valid j t)

theorem computable_select : Computable₂ select := primrec_enumerate.to_comp.comp₂ computable_first

theorem select_contraction (j t : ℕ) :
    let x := select j t
    ((x.calls * BatchRows.groups x.b x.width : ℕ) : ℝ) / x.b + (2*x.a : ℕ) <
      (x.m : ℝ)^Generator.targetExponent j := valid_contraction (selected_valid j t)

end Interchange.Template.Data

end NearSquareRoot
end Computability
end OAI
