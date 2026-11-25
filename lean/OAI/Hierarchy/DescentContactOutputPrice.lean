import OAI.Hierarchy.DescentContactOutputDate

namespace OAI
/-! # Account for mounted source expressions and the actual four-field contact publication -/
namespace Hierarchy.DescentContactOutputShape.Shape
open DescentSIMDLookup DescentStaticWordColumn DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable (A : Shape) (donorStart first : ℕ) {w : ℕ}
local notation "D" => A.donor
variable (u : DescentContactSenderDate.Prior A.donor.degree A.donor.lows A.donor.cap A.donor.n A.donor.residual)
local notation "E" => A.projected first
local notation "H" => A.sparseHosts
local notation "M" => A.donor.batch
local notation "dir" => DescentContactMaskShape.directionSize (D)
local notation "S₀" => A.donor.sender donorStart
local notation "terms" => A.four (A.fieldsAt donorStart first u)

def cost (T : ℕ):=
  (DescentContactSenderMass.Date.clockBound (S₀) first+(4+10*dir)+
    7*(DescentContactSenderMass.Date.nameBound (S₀) first+15*(dir+1)))+
  (A.catalogClock+7*A.catalogNames)+
  (4096*DescentResetStemProject.volume A.fields H A.groups A.blocks A.metaBits M A.batch+
    (4+A.fields*(4+H*chunks (A.groups*A.blocks) M*(2*T+4)))+7*(15+A.fields*(11+4*T)))

theorem actual_cost (T : ℕ) (work : ∀q f,(A.fieldsAt donorStart first u q f).work≤T)
    (old : 0<M) (block : 0<A.blocks) (batch : 0<A.batch) :
    A.issuedTicks donorStart first u+7*names (A.issuedProgram donorStart first u w)≤A.cost donorStart first T:=by
  have pre:=DescentContactMaskShape.period_priced (w:=w) (D) donorStart first u
  have end_:=DescentResetStemProjectExpr.tariff E H A.groups A.blocks A.metaBits M A.batch w terms T
    (fun i=>work _ _) old block batch
  change (DescentContactMaskShape.clock (D) donorStart first u+A.catalogClock)+
    DescentResetStemProjectExpr.ticks E H A.groups A.blocks A.metaBits M A.batch terms+7*names
    (((DescentContactMaskShape.period (D) donorStart first u w).seq (A.catalog first w)).seq
      (DescentResetStemProjectExpr.program E H A.groups A.blocks A.metaBits M A.batch terms w))≤_
  rw [names_seq,names_seq,A.catalog_names]
  unfold cost
  omega

end
end Hierarchy.DescentContactOutputShape.Shape

end OAI
