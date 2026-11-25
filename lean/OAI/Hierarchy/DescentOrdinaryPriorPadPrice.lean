import OAI.Hierarchy.DescentOrdinaryPriorPad
import OAI.Hierarchy.DescentOrdinaryPriorRetileRate
import OAI.Hierarchy.DescentOrdinaryHostPadPrice

namespace OAI
/-! The incoming seven-field bank changes its lane pitch at the old host population.
The extra scan copies just the live intersection and clears every padded destination. -/
namespace Hierarchy.DescentOrdinaryPriorPad
open DescentSIMDLookup DescentDatedPriorOperand DescentSixParty.Chronology
open DescentStaticWordColumn ProtocolRAM DescentDatedAddressBook Filter
noncomputable section
variable (l : Layout) (currentH lanes base prior w : ℕ)
set_option quotPrecheck false
local notation "Nₚ" => DescentOrdinaryPriorRetile.pages l
local notation "Rₚ" => rows l currentH lanes
local notation "Kₚ" => kept l currentH lanes
local notation "padₚ" => extension l currentH lanes base w
local notation "beforeₚ" => DescentOrdinaryPriorRetile.phase l lanes base prior w
local notation "allₚ" => phase l currentH lanes base prior w

theorem extension_fee :
    (padₚ).ticks+7*names (padₚ).program ≤ 512*(Nₚ+1)*(Rₚ+1) :=
  (rect l currentH lanes).fee (start l lanes base) (inputs l lanes base) w

theorem fee :
    (allₚ).ticks+7*names (allₚ).program ≤
      (beforeₚ).ticks+7*names (beforeₚ).program+512*(Nₚ+1)*(Rₚ+1) :=by
  change (beforeₚ).ticks+(padₚ).ticks+7*names ((beforeₚ).program.seq (padₚ).program) ≤ _
  rw [names_seq]
  have cap:=extension_fee l currentH lanes base w
  omega

theorem shared_fee (old : 0 < l.lanes) (new : 0 < lanes) :
    (allₚ).ticks+7*names (allₚ).program ≤
      4096*(DescentOrdinaryPriorRetile.lookupBill l lanes+DescentOrdinaryPriorRetile.rowBill l lanes)+
        512*(Nₚ+1)*(Rₚ+1) :=
  (fee l currentH lanes base prior w).trans
    (Nat.add_le_add_right (DescentOrdinaryPriorRetile.shared_fee l lanes base prior w old new) _)

/-- All newly reserved addresses are linear in the current host count, even when no prior
host survives or the current population is smaller than the previous allocation. -/
theorem extent : roof l currentH lanes base ≤
    DescentOrdinaryPriorRetile.roof l lanes base+(Nₚ+3)*(Rₚ+1)+1 :=
  (rect l currentH lanes).extent (start l lanes base)

theorem address_bound {ι : ℕ→Type*} (l : ∀h,ι h→Layout) (fresh lanes base : ∀h,ι h→ℕ)
    (hosts : Bounded (fun h i=>(l h i).hosts)) (current : Bounded fresh)
    (groups : Bounded (fun h i=>(l h i).groups)) (old : Bounded (fun h i=>(l h i).lanes))
    (nxt : Bounded lanes) (count : Bounded (fun h i=>pages (l h i))) (origin : Bounded base)
    (packed : ∃k : ℕ,∀ᶠ h : ℕ in atTop,∀i,DescentOrdinaryPriorRetile.digits (l h i)*(l h i).lanes ≤ k*h) :
    Bounded (fun h i=>roof (l h i) (fresh h i) (lanes h i) (base h i)) :=by
  have before:=DescentOrdinaryPriorRetile.address_bound l lanes base hosts groups old nxt count origin packed
  have tiles : Bounded (fun h i=>chunks (l h i).groups (lanes h i)):=
    (groups.add nxt).of_le (fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..))
  exact ((before.add ((count.add (Bounded.const 3)).mul ((current.mul tiles).add (Bounded.const 1)))).add
    (Bounded.const 1)).of_le (fun h i=>extent (l h i) (fresh h i) (lanes h i) (base h i))

theorem cofinal_fee (factor saving : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀(l : Layout)(currentH lanes base prior w J original : ℕ),
    J ≤ Nat.log 2 h → 2^h ≤ original → 0 < l.lanes → 0 < lanes → l.lanes ≤ h → lanes ≤ h →
    DescentOrdinaryPriorRetile.digits l*l.lanes ≤ h/2 → w+1 ≤ factor*h →
    let p:=phase l currentH lanes base prior w
    (p.ticks+7*names p.program)*(w+1) ≤ original/(2^J)^saving+
      (4096*DescentOrdinaryPriorRetile.rowBill l lanes+512*(DescentOrdinaryPriorRetile.pages l+1)*
        (currentH*chunks l.groups lanes+1))*(factor*h) :=by
  filter_upwards [DescentOrdinaryPriorRetile.cofinal_fee factor saving] with h admitted
  intro l currentH lanes base prior w J original height major old new priorPitch nextPitch packed machine p
  have part:=admitted l lanes base prior w J original height major old new priorPitch nextPitch packed machine
  have native:=Nat.mul_le_mul_right (w+1) (fee l currentH lanes base prior w)
  have copyBound:=Nat.mul_le_mul_left (512*(DescentOrdinaryPriorRetile.pages l+1)*(rows l currentH lanes+1)) machine
  apply native.trans
  change _ ≤ original/(2^J)^saving+
    (4096*DescentOrdinaryPriorRetile.rowBill l lanes+512*(DescentOrdinaryPriorRetile.pages l+1)*
       (rows l currentH lanes+1))*(factor*h)
  simpa only [Nat.add_mul,Nat.add_assoc] using Nat.add_le_add part copyBound

end
end Hierarchy.DescentOrdinaryPriorPad

end OAI
