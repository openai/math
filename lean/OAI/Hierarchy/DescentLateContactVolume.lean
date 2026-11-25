import OAI.Hierarchy.DescentContactOutputPrice
import OAI.Hierarchy.DescentContactOutputWork
import OAI.Hierarchy.DescentResetReceivedVolume
import OAI.Hierarchy.DescentResetQuantityFunded

namespace OAI
/-! # The complete measured contact publication before the signed candidate scan -/
namespace Hierarchy.DescentContactOutputShape.Shape
open DescentSIMDLookup DescentDatedAddressBook DescentDatedAddressBook.CandidateFront ProtocolRAM
noncomputable section
variable (A : Shape)
local notation "D" => A.donor
local notation "H" => A.donor.hosts
local notation "M" => A.donor.batch
local notation "f" => A.donor.fieldBits
local notation "v" => A.donor.cargoBits
local notation "Q" => A.sockets
local notation "I" => DescentContactMaskShape.donors (D)+1

def massCharge (rows span size dir q lim : ℕ) :=
  ((4+10*(q*span))+(4+10*size+(4+q*(4+rows*(2*lim+4)+(4+44*rows))))+(4+10*dir))+
    7*((15*(q*span+1)+(15*(size+1)+(15+q*(102+4*lim))))+15*(dir+1))
def massFactor (q inputs : ℕ) :=massCharge 1 3 ((inputs*2+2)*4) 2 q (1+inputs*18)
def catalogFactor (q : ℕ) :=2000*(q+2)

private theorem mass_scaled (q i R span size dir E : ℕ) (one : 1≤E) (rows : R≤E)
    (source : span≤3*E) (sizeFit : size≤((i*2+2)*4)*E) (direction : dir≤2*E) :
    massCharge R span size dir q (1+i*18)≤ massFactor q i*E:=by
  let op:=1+i*18
  calc massCharge R span size dir q op≤ massCharge E (3*E) (((i*2+2)*4)*E) (2*E) q op:=by
         unfold massCharge
         gcongr
       _≤ massFactor q i*E:=by
         change massCharge E (3*E) (((i*2+2)*4)*E) (2*E) q op≤ massCharge 1 3 ((i*2+2)*4) 2 q op*E
         have a:=Nat.mul_le_mul_left q one
         have b:=Nat.mul_le_mul_left (q*op) one
         unfold massCharge
         nlinarith only [one,a,b]

structure KeyRoom (h : ℕ) : Prop where
  mass : (f*I+f)*M≤h/2
  marker : A.markerBits*M≤h/2
  field : f*M≤h/2
  cargo : v*M≤h/2
  choice : A.choiceBits≤h/2
  projection : (A.metaBits*A.blocks)*A.batch≤h/2
  input : A.metaBits*M≤h/2

private theorem original_mass (h E donorStart first : ℕ) (key : KeyRoom A h)
    (one : 1≤E) (dict : 2^(h/2)≤E) (rows : H*chunks (D).groups M≤E) :
    let S₀:=(D).sender donorStart
    let dir:=DescentContactMaskShape.directionSize (D)
    DescentContactSenderMass.Date.clockBound S₀ first+(4+10*dir)+
      7*(DescentContactSenderMass.Date.nameBound S₀ first+15*(dir+1))≤ massFactor Q I*E:=by
  let R:=H*chunks (D).groups M
  let span:=2^Nat.clog 2 R
  let pack:=2^((f*I+f)*M)
  have powers : pack≤E:=(Nat.pow_le_pow_right (by decide) key.mass).trans dict
  have pad : span≤3*E:=(DescentVenueQuantityPlanes.padded_length R).trans (by dsimp only [R];omega)
  have sz : (I*2+2)*2^max ((f*I+f)*M) (Nat.clog 2 R)≤((I*2+2)*4)*E:=by
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    rcases le_total ((f*I+f)*M) (Nat.clog 2 R) with a|a
    · rw [max_eq_right a];change span≤_;omega
    · rw [max_eq_left a];change pack≤_;omega
  have direction:=Nat.mul_le_mul_left 2 ((Nat.pow_le_pow_right (by decide) key.field).trans dict)
  exact mass_scaled Q I R span _ _ E one rows pad sz direction

private theorem catalog_funded (h E : ℕ) (key : KeyRoom A h) (one : 1≤E) (dict : 2^(h/2)≤E) :
    A.catalogClock+7*A.catalogNames≤catalogFactor Q*E:=by
  have m:=(Nat.pow_le_pow_right (by decide : 0<2) key.marker).trans dict
  have a:=(Nat.pow_le_pow_right (by decide : 0<2) key.field).trans dict
  have b:=(Nat.pow_le_pow_right (by decide : 0<2) key.cargo).trans dict
  have c:=(Nat.pow_le_pow_right (by decide : 0<2) key.choice).trans dict
  have label : DescentResetDonorBook.words Q f A.metaBits M≤((Q+1)*2)*E:=Nat.mul_le_mul_left _ c
  unfold catalogClock catalogNames DescentContactMarkerShape.ticks DescentContactWidthPage.clock
    DescentContactWidthPage.words DescentContactWidthPage.size catalogFactor
  simp only [DescentContactWidthPage.words]
  nlinarith only [m,a,b,label,one,Nat.zero_le (Q*E)]

def fieldFactor (q inputs shapes blocks work : ℕ) :=
  massFactor q inputs+catalogFactor q+
    4096*volumeFactor (q*4) blocks*(5*shapes)+
    (4+(q*4)*(4+shapes*(2*work+4)))+7*(15+(q*4)*(11+4*work))

/-- All sensor reads and the shared choice and projection tables occur in this
one price. The enlarged sparse host count is multiplied solely by the local shape count. -/
theorem cost_volume (h donorStart first work : ℕ) (key : KeyRoom A h)
    (grid : A.groups*A.blocks=(D).groups) (same : A.batch=M) (live : 0<M)
    (block : 0<A.blocks) (pitch : M≤h) :
    A.cost donorStart first work≤fieldFactor Q I (A.shapes+1) A.blocks work*
      ResetOutput.receiptArea h H (chunks (D).groups M):=by
  let E:=ResetOutput.receiptArea h H (chunks (D).groups M)
  let Q₀:=A.shapes+1
  have one : 1≤E:=Nat.succ_le_of_lt (by dsimp only [E,ResetOutput.receiptArea];positivity)
  have hosts : H≤E:=by dsimp only [E,ResetOutput.receiptArea];omega
  have rows : H*chunks (D).groups M≤E:=by dsimp only [E,ResetOutput.receiptArea];omega
  have dict : 2^(h/2)≤E:=by
    have up:=Nat.le_mul_of_pos_left (2^(h/2)) (by positivity : 0<(h+1)^3)
    dsimp only [E,ResetOutput.receiptArea]
    omega
  have mass:=original_mass A h E donorStart first key one dict rows
  have menus:=catalog_funded A h E key one dict
  have smaller : A.groups≤(D).groups:=(Nat.le_mul_of_pos_right _ block).trans_eq grid
  have parts : chunks A.groups M≤chunks (D).groups M:=Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right smaller _) _)
  have nextRows: H*chunks A.groups M≤E:=(Nat.mul_le_mul_left _ parts).trans rows
  have inflate : stemEnvelope h A.sparseHosts A.sparseHosts A.groups A.blocks M A.batch≤5*Q₀*E:=by
    have rawCount:=Nat.mul_le_mul_left A.shapes hosts
    have rawIn:=Nat.mul_le_mul_left A.shapes rows
    have rawOut:=Nat.mul_le_mul_left A.shapes nextRows
    have shared : (h+1)^3*2^(h/2)≤E:=by dsimp only [E,ResetOutput.receiptArea];omega
    unfold stemEnvelope sparseHosts
    rw [grid,same]
    dsimp only [Q₀]
    nlinarith only [rawCount,rawIn,rawOut,shared,one]
  have volume:=volume_paid h A.fields A.sparseHosts A.sparseHosts A.groups A.blocks A.metaBits M A.batch block
    (by simpa only [same] using live) pitch (by simpa only [same] using pitch) key.input key.projection
  have stuff:=volume.trans (Nat.mul_le_mul_left _ inflate)
  have sensors : A.sparseHosts*chunks (A.groups*A.blocks) M≤Q₀*E:=by
    rw [grid]
    have a:=Nat.mul_le_mul_left A.shapes rows
    dsimp only [sparseHosts,Q₀]
    nlinarith only [a,Nat.zero_le E]
  have scaled:=Nat.mul_le_mul_right (2*work+4) sensors
  let F:=A.fields
  have z:=Nat.mul_le_mul_left (F*(11+4*work)) one
  have y:=Nat.mul_le_mul_left F one
  have x:=Nat.mul_le_mul_left F scaled
  unfold cost
  unfold fieldFactor
  change _≤(massFactor Q I+catalogFactor Q+4096*volumeFactor F A.blocks*(5*Q₀)+
    (4+F*(4+Q₀*(2*work+4)))+7*(15+F*(11+4*work)))*E
  nlinarith only [mass,menus,stuff,x,y,z,one]

end
end Hierarchy.DescentContactOutputShape.Shape

end OAI
