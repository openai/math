import OAI.Hierarchy.DescentContactSenderScale
import OAI.Hierarchy.DescentContactDonorFrontPrice

namespace OAI
/-! # Previous-host donor reconstruction charged at the physical receiver pitch -/
namespace Hierarchy.DescentContactDonorFront.Shape
open DescentSIMDLookup DescentContactCostUnit DescentResetSignedHaloMatrix
open DescentContactSenderDate.Layout
variable (A : Shape)
local notation "D" => A.degree
local notation "N" => A.boardFields
local notation "F" => A.laneFields
local notation "S" => A.returnFields
local notation "M" => A.batch
local notation "jobs" => (A.lows*(2*A.cap))*2
private def haloFactor (d : ℕ) := 2*(2*(d+1)+1)
private def routeFactor (d : ℕ) := 1+((d+1)+(1+(1+1)))

def clockFactor (U : ℕ) := scanClock N F S jobs D U+(4+10*4)+
    (4+10*haloFactor D+(4+(D+1)*(2*termWork D+4))+(4+10*2)+(4+10*routeFactor D))
def nameFactor (U : ℕ) := scanNames N F S jobs D U+15*(4+1)+
    (15*(haloFactor D+1)+(11+4*termWork D)+15*(2+1)+15*(routeFactor D+1))

theorem donor_scale (base U h T : ℕ) (host : A.hosts≤T)
    (rows : A.hosts*chunks A.groups M≤T) (lut : 2^(h/2)≤T) (positive : 0<M)
    (board : (A.fieldBits*N+A.fieldBits)*M≤h/2)
    (split : ((A.fieldBits*F)*2+A.fieldBits*F)*M≤h/2)
    (returns : (A.fieldBits*S+A.fieldBits)*M≤h/2)
    (field : A.fieldBits*M≤h/2) (pick : (A.queryBits+A.cargoBits)*M≤h/2)
    (join : (A.cargoBits+A.cargoBits)*M≤h/2) :
    A.fee base U+7*A.size base U≤(A.clockFactor U+7*A.nameFactor U)*T := by
  have pos : 0<T:=(Nat.two_pow_pos _).trans_le lut
  have table {u : ℕ} (key : u≤h/2) : 2^u≤1*T:=by
    simpa using (Nat.pow_le_pow_right (by decide : 0<2) key).trans lut
  have rx : A.hosts*chunks A.groups M≤1*T:=by simpa using rows
  have hx : A.hosts≤1*T:=by simpa using host
  have idx : A.idCells≤4*T:=by
    simpa [idCells] using sum (fixed 1 pos) (DescentContactCostUnit.span hx pos)
  have owners : A.hosts*(D+1)≤(D+1)*T:=by
    simpa using right (D+1) hx
  have halo : cells A.hosts D≤haloFactor D*T:=
    left 2 (DescentContactCostUnit.span owners pos)
  have q₁ : A.queryBits*M≤h/2:=(Nat.mul_le_mul_right M (Nat.le_add_right ..)).trans pick
  have q₂ : A.queryBits*M+A.cargoBits≤h/2:=by
    have h' := Nat.le_mul_of_pos_right A.cargoBits positive
    rw [Nat.add_mul] at pick;omega
  have q₃ : A.cargoBits*M≤h/2:=(Nat.mul_le_mul_right M (Nat.le_add_right ..)).trans join
  have book : DescentPackedChildNeighbor.SIMD.ROM.cells (D+1) A.queryBits A.cargoBits M A.hosts A.groups
      ≤routeFactor D*T:=by
    simpa [routeFactor, DescentPackedChildNeighbor.SIMD.ROM.cells] using sum (table q₁) (sum (left (D+1) (table q₂))
      (sum (table q₃) (sum (table join) rx)))
  have dec : 2*2^(A.fieldBits*M)≤2*T:=by simpa using left 2 (table field)
  obtain ⟨speed,text⟩:=(A.sender base).scan_scale U h T rows lut board split returns
  have clocked : A.fee base U≤A.clockFactor U*T:=by
    exact sum (sum speed (sum (fixed 4 pos) (left 10 idx)))
      (sum (sum (sum (sum (fixed 4 pos) (left 10 halo))
        (sum (fixed 4 pos) (right (2*termWork D+4) owners))) (sum (fixed 4 pos) (left 10 dec)))
        (sum (fixed 4 pos) (left 10 book)))
  have named : A.size base U≤A.nameFactor U*T:=by
    exact sum (sum text (left 15 (sum idx (fixed 1 pos))))
      (sum (sum (sum (left 15 (sum halo (fixed 1 pos))) (fixed (11+4*termWork D) pos))
        (left 15 (sum dec (fixed 1 pos)))) (left 15 (sum book (fixed 1 pos))))
  exact sum clocked (left 7 named)

end Hierarchy.DescentContactDonorFront.Shape

end OAI
