import OAI.Hierarchy.DescentResetOriginalDonors

namespace OAI
/-! Legal reads of all three emitted donor arrays after the public compact-host remap. -/
namespace Hierarchy.DescentResetOriginalDonors
open ProtocolRAM DescentSIMDLookup
noncomputable section

private theorem bank_later {w a b : ℕ} {B : Bank} (f : B.Fits w a) (h : a≤b) : B.Fits w b :=
  ⟨f.1,f.2.1,f.2.2.trans h⟩

theorem Panel.bank_fits (P : Panel) (base : ℕ) (j : Fin P.fields) (x : Fin P.blocks) {w : ℕ}
    (roof : P.endAddress base<2^w) : (P.bank base j x).Fits w (P.endAddress base) :=
  DescentResetStemProject.page_fits j x roof

namespace Layout
variable (L : Layout) (base : ℕ) (R : DescentResetDenseOperand.Layout) (cnt inv : Bank) {w : ℕ}
    (access : R.Fits cnt inv w (L.endAddress base)) (roof : L.endAddress base<2^w)

include access roof

theorem label_fits (x : Fin L.blocks) (s : Bool) (j : Fin L.slots) :
    (L.label base R cnt inv x s j).Fits w (L.endAddress base) := by
  have two := (L.cuts base).2.1.trans (L.cuts base).2.2
  exact R.fits access _ ⟨bank_later (L.labels.bank_fits base (L.wing s j) x (two.trans_lt roof)) two,trivial⟩

theorem cargo_fits (x : Fin L.blocks) (s : Bool) (t : Fin 2) (j : Fin L.slots) :
    (L.cargo base R cnt inv x s t j).Fits w (L.endAddress base) := by
  unfold cargo
  apply R.fits access
  split
  · have three:=(L.cuts base).2.2
    exact ⟨bank_later (L.tickets.bank_fits (L.ticketBase base) (L.wing s j) x (three.trans_lt roof)) three,trivial⟩
  · exact ⟨L.halos.bank_fits (L.haloBase base) j x roof,trivial⟩

end Layout
end
end Hierarchy.DescentResetOriginalDonors

end OAI
