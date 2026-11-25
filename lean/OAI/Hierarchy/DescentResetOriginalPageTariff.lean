import OAI.Hierarchy.DescentResetOriginalDate

namespace OAI
/-! # Cost of publishing the public or private original-number pages -/
namespace Hierarchy.DescentResetMixedWordRAM.OriginalDate.Date
open DescentStaticWordColumn
noncomputable section
variable {X J K w : ℕ} (L : Date X J K)

/-- Includes the shared twelve-page lookup table and every selected shelf write. -/
def pagePrice (T : ℕ) := 2048*(X*J+1)*(T+1)*(1+L.rows+2^L.width)

private theorem page_cost (n T rows page : ℕ) :
    4+10*(12*page)+(4+n*(4+rows*(2*(4*T+33)+4)))+
      7*(15*(12*page+1)+(15+n*(11+4*(4*T+33)))) ≤
    2048*(n+1)*(T+1)*(1+rows+page) := by
  ring_nf
  omega

theorem priced (T : ℕ) (room : L.Room w)
    («meta» : ∀ p, (L.fields.meta p).work ≤ T) (zero : ∀ p, (L.fields.zero p).work ≤ T)
    (halo : ∀ p, (L.fields.halo p).work ≤ T) (arg : ∀ p, (L.fields.arg p).work ≤ T) :
    L.ticks+7*names (L.code w) ≤ L.pagePrice T := by
  have all (p : Fin (X*J)) : (L.fields.meta p).work+(L.fields.zero p).work+
      (L.fields.halo p).work+(L.fields.arg p).work+33 ≤ 4*T+33 := by
    have a := «meta» p
    have b := zero p
    have c := halo p
    have d := arg p
    omega
  have inv := L.invoice room (4*T+33) all
  exact (Nat.add_le_add inv.1 (Nat.mul_le_mul_left 7 inv.2)).trans (page_cost ..)

end
end Hierarchy.DescentResetMixedWordRAM.OriginalDate.Date

end OAI
