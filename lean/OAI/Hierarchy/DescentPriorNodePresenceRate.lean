import OAI.Hierarchy.DescentPriorNodePresenceShape
import OAI.Hierarchy.DescentOrdinaryRoleRetileRate

namespace OAI
/-! Native text and word costs for the all-node reset input. -/
namespace Hierarchy.DescentPriorNodePresence.Chart
open DescentSIMDLookup DescentDatedAddressBook DescentStaticWordColumn DescentSixParty.Chronology ProtocolRAM Filter
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable (C : Chart)
def volume:=2^(C.tokenBits*C.nodes*C.roleLanes)+2^(C.nodes*C.operandLanes)+C.convert.lookupBill+C.convert.rowBill+
  (C.blocks+1)*(C.mask.rows+1)+(2*C.blocks+1)*(C.rows+1)
theorem tariff (base : ℕ) (role arity : Fin C.blocks→Bank) (w : ℕ) (old : 0<C.roleLanes) (nxt : 0<C.operandLanes) :
    (C.phase base role arity w).ticks+7*names (C.phase base role arity w).program≤8192*C.volume:=by
  have low:=C.mask.tariff C.presence base role (fun _=>true) w
  have mid:=C.convert.shared_fee (C.maskEnd base) (C.mask.bank base) w old nxt
  have later:=C.pages.tariff C.expand (C.tileEnd base) (C.input base arity) C.test w
  simp only [phase,NativePhase.seq,names_seq] at *
  unfold volume
  change _≤1024*(2^(C.tokenBits*C.nodes*C.roleLanes)+(C.blocks+1)*(C.mask.rows+1)) at low
  change _≤1024*(2^((1*C.nodes)*C.operandLanes)+(2*C.blocks+1)*(C.rows+1)) at later
  rw [Nat.one_mul] at later
  omega

variable {ι : ℕ→Type*} (D : ∀h,ι h→Chart)
def Linear (a : ∀h,ι h→ℕ) : Prop:=∃k:ℕ,∀ᶠ h:ℕ in atTop,∀i,a h i≤k*h
structure ScalarRoom : Prop where
  hosts : Bounded (fun h i=>(D h i).hosts)
  groups : Bounded (fun h i=>(D h i).groups)
  blocks : Bounded (fun h i=>(D h i).blocks)
  roles : Bounded (fun h i=>(D h i).roleLanes)
  operands : Bounded (fun h i=>(D h i).operandLanes)
  tokens : Linear (fun h i=>(D h i).tokenBits*(D h i).nodes*(D h i).roleLanes)
  packedMask : Linear (fun h i=>(D h i).nodes*(D h i).roleLanes)
  expanded : Linear (fun h i=>(D h i).nodes*(D h i).operandLanes)

private theorem phase_rate (Q : ∀h,ι h→DescentPackedUnaryPages.Shape) (base : ∀h,ι h→ℕ)
    (addr : Bounded base) (hh : Bounded (fun h i=>(Q h i).hosts)) (gg : Bounded (fun h i=>(Q h i).groups))
    (ll : Bounded (fun h i=>(Q h i).lanes)) (nn : Bounded (fun h i=>(Q h i).pages))
    (width : Linear (fun h i=>(Q h i).width)) : Bounded (fun h i=>(Q h i).finish (base h i)):=by
  have chunks_ : Bounded (fun h i=>chunks (Q h i).groups (Q h i).lanes):=
    (gg.add ll).of_le (fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..))
  have rows : Bounded (fun h i=>(Q h i).rows):=hh.mul chunks_
  obtain ⟨k,fits⟩:=width
  have lit:=Bounded.pow_of_linear fits
  exact ((addr.add ((Bounded.const 2).mul lit)).add (nn.mul rows)).add ((rows.add (Bounded.const 1)).padded)

theorem rate (R : ScalarRoom D) (base : ∀h,ι h→ℕ) (addr : Bounded base) :
    Bounded (fun h i=>(D h i).endAddress (base h i)):=by
  have low:=phase_rate (fun h i=>(D h i).mask) base addr R.hosts R.groups R.roles R.blocks R.tokens
  have mid:=DescentOrdinaryRoleRetile.Layout.address_bound (fun h i=>(D h i).convert)
    (fun h i=>(D h i).maskEnd (base h i)) R.hosts R.groups R.roles R.operands R.blocks low (by
      simpa only [Linear, convert, Nat.one_mul] using R.packedMask)
  exact phase_rate (fun h i=>(D h i).pages) (fun h i=>(D h i).tileEnd (base h i))
    mid R.hosts R.groups R.operands ((Bounded.const 2).mul R.blocks) (by
      simpa only [Linear, pages, DescentPackedUnaryPages.Shape.width, Nat.one_mul] using R.expanded)

end
end Hierarchy.DescentPriorNodePresence.Chart

end OAI
