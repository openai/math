import OAI.Hierarchy.DescentOrdinaryHeadRetile
import OAI.Hierarchy.DescentOrdinaryRoleRetileRate
import OAI.Hierarchy.DescentTerminalPrimitiveSpace

namespace OAI
/-! The real earlier source expressions are gathered at their archived pitch before the
same overlap table changes the SIMD width. The row bill counts both actual populations. -/
namespace Hierarchy.DescentOrdinaryHeadRetile
open DescentSIMDLookup DescentStaticWordColumn DescentPackedFlowBatch ProtocolRAM
open DescentDatedAddressBook Filter
noncomputable section

def headerFee (N rows work : ℕ) :=109+N*((4+rows*(2*work+4))+7*(11+4*work))

private theorem batch_fee (base rows n w work : ℕ) (read : ℕ→Expr)
    (small : ∀j < n,(read j).work ≤ work) :
    clock (passes base rows rows read 0 n)+7*names (program w (passes base rows rows read 0 n))
      ≤ headerFee n rows work :=by
  have ticks:=DescentPackedFlowBatch.tariff base rows rows n read work small
  have hardware:=DescentOperandVectorArena.names_passes base rows rows w work read 0 n
    (fun j _ hj=>small j (by simpa using hj))
  calc
    _ ≤ (4+n*(4+rows*(2*work+4)))+7*(15+n*(11+4*work)) :=
      Nat.add_le_add ticks (Nat.mul_le_mul_left 7 hardware)
    _ = _ :=by unfold headerFee;ring

namespace Shape
variable (S : Shape) (base : ℕ) (src : Fin S.n→Expr) (w work : ℕ)
set_option quotPrecheck false
local notation "headₕ" => S.head base src w
local notation "retileₕ" => S.role.phase (S.roleStart base) (S.staged base) w
local notation "phaseₕ" => S.phase base src w

theorem head_fee (limit : ∀i,(src i).work ≤ work) :
    (headₕ).ticks+7*names (headₕ).program ≤ headerFee S.n S.oldRows work :=by
  apply batch_fee
  intro j hj
  simpa only [column,dite_eq_left hj] using limit ⟨j,hj⟩

theorem fee (limit : ∀i,(src i).work ≤ work) :
    (phaseₕ).ticks+7*names (phaseₕ).program ≤ headerFee S.n S.oldRows work+
      ((retileₕ).ticks+7*names (retileₕ).program) :=by
  change (headₕ).ticks+(retileₕ).ticks+7*names ((headₕ).program.seq (retileₕ).program) ≤ _
  rw [names_seq]
  have upper:=S.head_fee base src w work limit
  omega

theorem shared_fee (limit : ∀i,(src i).work ≤ work) (old : 0 < S.before) (fresh : 0 < S.after) :
    (phaseₕ).ticks+7*names (phaseₕ).program ≤
      headerFee S.n S.oldRows work+4096*(S.role.lookupBill+S.role.rowBill) :=
  (S.fee base src w work limit).trans (Nat.add_le_add_left
    (S.role.shared_fee (S.roleStart base) (S.staged base) w old fresh) _)

theorem extent : S.endAddress base ≤ base+(S.n+2)*(S.oldRows+1)+1+S.role.roof 0 :=by
  change S.role.roof (S.roleStart base) ≤ _
  rw [S.role.translated]
  apply Nat.add_le_add_right
  have cap : 2^Nat.clog 2 (S.oldRows+1) ≤ 2*(S.oldRows+1)+1:=DescentTerminalPrimitiveArena.pad_le _
  unfold roleStart
  nlinarith only [cap,Nat.zero_le S.n]

theorem address_bound {ι : ℕ→Type*} (S : ∀h,ι h→Shape) (base : ∀h,ι h→ℕ)
    (hosts : Bounded (fun h i=>(S h i).hosts)) (groups : Bounded (fun h i=>(S h i).groups))
    (old : Bounded (fun h i=>(S h i).before)) (next : Bounded (fun h i=>(S h i).after))
    (count : Bounded (fun h i=>(S h i).n)) (origin : Bounded base)
    (width : ∃k : ℕ,∀ᶠ h : ℕ in atTop,∀i,(S h i).bits*(S h i).before ≤ k*h) :
    Bounded (fun h i=>(S h i).endAddress (base h i)) :=by
  have live : Bounded (fun h i=>(S h i).oldRows):=
    hosts.mul ((groups.add old).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..))
  have done_:=DescentOrdinaryRoleRetile.Layout.address_bound (fun h i=>(S h i).role)
    (fun _ _=>0) hosts groups old next count (Bounded.const 0) width
  exact (((origin.add ((count.add (Bounded.const 2)).mul (live.add (Bounded.const 1)))).add
    (Bounded.const 1)).add done_).of_le (fun h i=>(S h i).extent (base h i))

theorem cofinal_fee (factor saving : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀(S : Shape)(base w work J original : ℕ)(src : Fin S.n→Expr),
    J ≤ Nat.log 2 h → 2^h ≤ original → 0 < S.before → 0 < S.after → S.before ≤ h → S.after ≤ h →
    S.bits*S.before ≤ h/2 → w+1 ≤ factor*h → (∀i,(src i).work ≤ work) →
    let p:=S.phase base src w
    (p.ticks+7*names p.program)*(w+1) ≤ original/(2^J)^saving+
      (4096*S.role.rowBill+headerFee S.n S.oldRows work)*(factor*h) :=by
  filter_upwards [DescentOrdinaryRoleRetile.Layout.cofinal_fee factor saving] with h originalBill
  intro S base w work J original src hj huge old next lo hi half bus bound p
  have retile:=originalBill S.role (S.roleStart base) w J original (S.staged base) hj huge old next lo hi half bus
  have native:=Nat.mul_le_mul_right (w+1) (S.fee base src w work bound)
  rw [Nat.add_mul (headerFee S.n S.oldRows work)] at native
  have header:=Nat.mul_le_mul_left (headerFee S.n S.oldRows work) bus
  apply native.trans
  calc
    _ ≤ headerFee S.n S.oldRows work*(factor*h)+(original/(2^J)^saving+4096*S.role.rowBill*(factor*h)) :=
      Nat.add_le_add header retile
    _ = _:=by ring

end Shape

end
end Hierarchy.DescentOrdinaryHeadRetile

end OAI
