import OAI.Hierarchy.DescentTerminalCandidateType
import OAI.Hierarchy.DescentTerminalAppendixNumbers
import OAI.Hierarchy.DescentExteriorPinTypes
import OAI.Hierarchy.DescentExteriorShelfNumbers

namespace OAI
/-! # Number of inputs on the original exterior, chip and paid-row candidate -/
namespace Hierarchy.DescentTerminalFullPins
open DescentExterior DescentExteriorShelf DescentTerminalChipPins DescentTerminalPorts
open scoped Classical BigOperators
noncomputable section

variable (A : Type) [Fintype A] (E j rest s K W q piece rows : ℕ)
local notation "full" => Candidate (A⊕Hidden E j rest s) K W q piece rows
local notation "copies" => 2^(j+(j+rest))*s
local notation "modeBits" => q*(W*piece)

/-- A chip has two candidate planes.  Each paid raw row contributes its live
payload bits, including when the row count or a chip dimension vanishes. -/
theorem candidate_card :
    Fintype.card full = Fintype.card A+2*E*copies+(2*(K*W)+rows)*modeBits :=by
  change Fintype.card (((A⊕Hidden E j rest s)⊕Inputs K W q piece)⊕RowBit rows modeBits)=_
  simp only [Fintype.card_sum,(header_price E j rest s).2,Inputs,Bit,DescentTerminalBinReaddress.Slot,
    RowBit,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin]
  ring

/-- The first two physical chip columns provide one full row per chip site
for each independent Boolean plane.  The separately declared raw bank provides
a further row for each explicitly paid row. -/
theorem candidate_rows_in_public (codes pub : ℕ) :
    2*(K*W)+rows ≤ DescentTerminalPublicIdentity.total K W q piece codes rows pub :=by
  let bits:=DescentTerminalChipBootWords.bits K W q piece codes
  have columns : 2^(bits 0)+2^(bits 1)≤DescentTerminalChipBootWords.total K W q piece codes:=by
    unfold DescentTerminalChipBootWords.total
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
    change 2^(bits 0)+2^(bits 1)≤2^(bits 0)+(2^(bits 1)+_)
    omega
  have first : K*W≤2^(bits 0):=Nat.le_pow_clog (by decide : 1<2) (K*W)
  have second : K*W≤2^(bits 1):=Nat.le_pow_clog (by decide : 1<2) (K*W)
  have raw:=DescentTerminalPrimitiveArena.covered rows
  unfold DescentTerminalPublicIdentity.total DescentTerminalPaidBoot.total DescentTerminalBoot.total
  omega

/-- The exterior uses exactly two candidate bits for every copy and exterior
gate.  The two chip planes and the paid raw rows fit the issued public bits. -/
theorem candidate_card_paid (codes pub bw : ℕ) (mode : modeBits≤bw) :
    Fintype.card full≤Fintype.card A+2*E*copies+DescentTerminalPublicIdentity.total K W q piece codes rows pub*bw :=by
  rw [candidate_card]
  exact Nat.add_le_add_left (Nat.mul_le_mul (candidate_rows_in_public K W q piece rows codes pub) mode) _

/-- The same count in wide words uses each of the two exterior planes at its
packed pitch, which may vary independently of the number of exterior gates. -/
theorem candidate_card_wide (codes pub bw : ℕ) (exterior : 2^j*s≤bw) (mode : modeBits≤bw) :
    Fintype.card full≤Fintype.card A+(2*span j rest s E+DescentTerminalPublicIdentity.total K W q piece codes rows pub)*bw :=by
  have h₀:=row_room j rest s E
  change E*2^(j+rest)≤ span j rest s E at h₀
  have exteriorBits : 2*E*copies≤2*span j rest s E*bw:=by
    calc
      _ = (2*(E*2^(j+rest)))*(2^j*s):=by rw [pow_add (2:ℕ) j (j+rest)];ring
      _ ≤ _:=Nat.mul_le_mul (Nat.mul_le_mul_left _ h₀) exterior
  have bound:=candidate_card_paid A E j rest s K W q piece rows codes pub bw mode
  rw [Nat.add_mul]
  omega

end
end Hierarchy.DescentTerminalFullPins

end OAI
