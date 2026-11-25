import OAI.Hierarchy.DescentSeedTokenSourceLayout
import OAI.Hierarchy.DescentWideSeedRoleCode

namespace OAI
/-! # Scheduled primitive-role source code and its physical tariff -/
namespace Hierarchy.DescentPackedSeed.Primitive.Source
open DescentSeedRoot DescentSIMDLookup Catalyst
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {k p : ℕ} (X : Approximation F k p) (R s payload bw : ℕ)
local notation "O" => Fintype.card (Old X)
local notation "A" => pieces payload s
local notation "n" => jobs X R s payload
local notation "dst" => raw X R s payload

def program (base : ℕ) :=wideProgram (s:=s) (R:=R) X payload bw base (dst base)
def image (base : ℕ) (m : Memory bw) :=wideImage (s:=s) (R:=R) X payload bw base (dst base) m
def clock (base : ℕ) :=wideTime (s:=s) (R:=R) X payload base

theorem price (base : ℕ) :
    clock X R s payload base+7*DescentStaticWordColumn.names (program X R s payload bw base) ≤
      1000+115*Fintype.card Plan*2^(payload/2)+300*n :=by
  have fit := lanes_fit payload (8*digitsNeeded s)
  have size : 2^(digitsNeeded s*8*A) ≤ 2^(payload/2):=Nat.pow_le_pow_right (by decide)
    (by simpa only [pieces,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using fit)
  have tab : cols s A ≤ Fintype.card Plan*2^(payload/2) :=
    Nat.mul_le_mul_left (Fintype.card Plan) size
  have allocated : endAddr base O R A s-base=cols s A+2*n :=by
    change base+cols s A+2*n-base=cols s A+2*n
    omega
  rw [program,wide_names,clock,wideTime,allocated,Nat.mul_assoc 115 (Fintype.card Plan)]
  change (4+10*(cols s A+2*n)+(4+60*n))+7*(15*(cols s A+2*n+1)+(11+4*28)) ≤
    1000+115*(Fintype.card Plan*2^(payload/2))+300*n
  omega

end
end Hierarchy.DescentPackedSeed.Primitive.Source

end OAI
