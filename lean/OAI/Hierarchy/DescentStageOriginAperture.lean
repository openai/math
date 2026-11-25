import OAI.Hierarchy.DescentFundedOriginChoice
import OAI.Hierarchy.DescentNamedFundedScale
import OAI.Hierarchy.DescentResetRetainedCalendarWidths

namespace OAI
/-! # The extra dated W origin book fits on the true epoch and cap calendars -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale Chronology DescentOrdinaryOriginBounds Filter

variable {F P : Type} [Field F] (G : PoweredGadget F)

def originRate (t f g reset D : ℕ) :=
  8+(D+1)+(8+((capPeriod G.b t g).map (·+1)).prod)+
    (1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g)+
    (stageNumbers G t 0 f g reset 0 0).localTokenExponent

theorem stage_origin_aperture (t f g reset D B : ℕ) (positive : 0<B) (cut : 20*originRate G t f g reset D≤B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
    ∀M tail age, let S:=stageNumbers G t J f g reset M tail
    let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
    ∀(v : PhysicalOrdinary F P) (prior : ℕ),
    v.area.D≤D → v.area.k=k → v.reference.oldNodes≤S.retainedNodes → v.resolver.nodes≤S.retainedNodes →
    v.reference.capacity≤((capCalendar G.b t g J).take age).prod*256 → v.payload=h →
    4*v.fundedMaxUnit prior*(2^k)≤h → 4*v.fundedMaxUnit (v.originExtra prior)*(2^k)≤h :=by
  filter_upwards [PhysicalOrdinary.future_enlarged_room (F:=F) (P:=P)
    (originRate G t f g reset D) B positive cut] with h assembled
  intro J M tail age S k v prior degree radix oldNodes newNodes slots paid before
  let a:=originRate G t f g reset D
  have exp {j : ℕ} (low : j≤a) : scale J j≤ scale J a :=
    Nat.pow_le_pow_right (n:=2) (by decide) (Nat.mul_le_mul_right (J+1) low)
  have plain : a≤ scale J a:=calc
    a≤a*(J+1):=Nat.le_mul_of_pos_right a (Nat.succ_pos J)
    _≤2^(a*(J+1)):=Nat.lt_two_pow_self.le
  have enough : 8≤ scale J a:=(show 8≤a by dsimp [a,originRate];omega).trans plain
  have Dbound : v.area.D+1≤ scale J a:=((Nat.succ_le_succ degree).trans
    (show D+1≤a by dsimp [a,originRate];omega)).trans plain
  have kt : k≤(1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g)*(J+1):=groupBits_linear ..
  have radixBound : 2^k≤ scale J a :=
    (Nat.pow_le_pow_right (n:=2) (by decide) kt).trans (exp (by dsimp [a,originRate];omega))
  have nodeRate : S.localTokenExponent=(stageNumbers G t 0 f g reset 0 0).localTokenExponent:=rfl
  have nodeBound : S.retainedNodes≤ scale J a := (S.capacities_scale G).1.trans (exp (by
    rw [nodeRate];dsimp [a,originRate];omega))
  have capBound:= (DescentNamedFundedChart.capPrefix G.b t g J age).trans (exp (by
    dsimp [a,originRate];omega))
  rw [←radix] at before radixBound ⊢
  exact assembled v prior enough Dbound radixBound (oldNodes.trans nodeBound) (slots.trans capBound)
    (newNodes.trans nodeBound) paid before

end Hierarchy.DescentSixParty

end OAI
