import OAI.Hierarchy.DescentOriginalPrimitiveLimits
import OAI.Hierarchy.DescentResetLookupTraffic
import OAI.Hierarchy.DescentDatedRetainedPitches

namespace OAI
/-! # Size of the nine actual lookup domains on every selected reset date -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty Filter
noncomputable section
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (board : NonlinearExpanders.Graph n d)
variable (op : RotorSpec) (t f g reset D : ℕ)
local notation "η" => hostRate t reset
local notation "κ" => 1+(η+capRate G t g)*(t+1)+8+cutRate t f g
local notation "Ht" => GroupStage.depthBound D n f g
local notation "shapePrice" => 2*(2*((2^n+1)+((2*d+4)*2^n+(2^n+1)*2^(Ht+1))))
local notation "rate" => localExponent G board op t f g reset D



local notation "primitive" => primitiveLocalExponent G board op t f g reset D
local notation "menuSize" => (2^n+2^Ht+DescentResetCableSlots.cableCap board Ht+D+64)
local notation "e₀" => primitive+menuSize
def lookupLocalExponent:=8*e₀+17

private theorem generous (J e : ℕ) : 512*(scale J e+1)^8≤ scale J (8*e+17):=by
  let L:=scale J e
  have pos:1≤L:=Nat.two_pow_pos _
  have bound:L+1≤2*L:=by omega
  calc
    _≤512*(2*L)^8:=Nat.mul_le_mul_left _ (Nat.pow_le_pow_left bound _)
    _=2^(8*e*(J+1)+17):=by
      rw [pow_add]
      rw [show 8*e*(J+1)=(e*(J+1))*8 by ring,pow_mul]
      change 512*(2*L)^8=L^8*2^17
      ring
    _≤_:=by
      change 2^(8*e*(J+1)+17)≤2^((8*e+17)*(J+1))
      apply Nat.pow_le_pow_right (by decide)
      rw [Nat.add_mul];omega

theorem original_lookup_limits (τ drift B : ℕ) (positive : 0<B) (branch : G.b≤2^(capRate G t g)) (bound : ℕ) :
    ∀ᶠ h : ℕ in atTop,let J:=Nat.log 2 h/(2*B);
    ∀sites age p degree e previous lanes nextM base old,p≤h→degree≤bound→
      let z:=originalSample G op t f g reset τ D drift J sites age p degree h e previous lanes nextM base old
      let v:=z.output G board D f g op.C op.w
      LookupLimits v (37+28*(v.front.signedQueries/2)) (scale J (lookupLocalExponent G board op t f g reset D)):=by
  filter_upwards [original_fields G board op t f g reset τ D drift B positive branch bound,
    original_primitive_limits G board op t f g reset D τ drift B positive branch bound] with h area primitiveRoom
  let J:=Nat.log 2 h/(2*B)
  dsimp only
  intro sites age p degree e previous lanes nextM base old hp hd
  let z:=originalSample G op t f g reset τ D drift J sites age p degree h e previous lanes nextM base old
  let v:=z.output G board D f g op.C op.w
  let L:=scale J e₀
  let cap:=((capCalendar G.b z.sched.rounds g z.sched.height).take age).prod*256
  let X:=2^z.k
  have dims:=area sites age p degree e previous lanes nextM base old hp hd
  have m:=primitiveRoom sites age p degree e previous lanes nextM base old hp hd
  have weak {a u : ℕ} (ok:a≤ scale J u) (flat:u≤e₀) : a≤L:=ok.trans
    (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ flat))
  have fixed (a : ℕ) (little:a≤ menuSize) : a≤L:=
    (little.trans (Nat.lt_two_pow_self (n:=menuSize)).le).trans
      (Nat.pow_le_pow_right (by decide) ((Nat.le_add_left menuSize primitive).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))))
  have le₀:primitive≤e₀:=Nat.le_add_right ..
  have oldC:cap≤L:=weak dims.cap (((Nat.le_add_right rate κ).trans (Nat.le_add_right _ _)).trans le₀)
  have smallX:X≤L:=weak m.blocks le₀
  have smallK:z.k≤L:=weak m.residual le₀
  have smallN:z.sched.retainedNodes≤L:=weak m.nodes le₀
  have smallA:z.sched.retainedArgumentsAt G z.drift≤L:=weak m.args le₀
  have dy:2^n≤L:=fixed _ ((((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ 64))
  have ht:2^Ht≤L:=fixed _ ((((Nat.le_add_left _ _).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ 64))
  have cable:DescentResetCableSlots.cableCap board Ht≤L:=fixed _ (((Nat.le_add_left _ _).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ 64))
  have deg:D≤L:=fixed _ ((Nat.le_add_left _ _).trans (Nat.le_add_right _ 64))
  have lp:1≤L:=Nat.two_pow_pos _
  have roots:DescentResetLocalRoster.rootSlots z.k (2^n)≤(2*L)+(2*L)*(L+1):=by
    unfold DescentResetLocalRoster.rootSlots
    rw [pow_succ,Nat.mul_comm _ 2]
    gcongr
  have book:DescentSharedBookScan.width z.k (2^n) D≤((L+1)*L*(L+1))*((L+1)*((L+1)*L*(L+1))):=by
    unfold DescentSharedBookScan.width DescentFallbackShapeTable.rows
    gcongr
  let Q:=512*(L+1)^8
  have fit:Q≤ scale J (lookupLocalExponent G board op t f g reset D):=generous J e₀
  have geom:v.setup.retained.CalendarPitch (z.sched.groupWidth z.k z.tail z.age) z.k h v.retainedUnit:=
    ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  have donors:v.setup.retained.donors=X:=(DescentResetRetainedSetup.Layout.CalendarPitch.geometry _ geom).2.1
  have channels:((7*z.sched.retainedArgumentsAt G z.drift)*X)*z.sched.retainedNodes≤Q:=by
    calc _≤((7*L)*L)*L:=by gcongr
         _≤_:=by dsimp [Q];ring_nf;omega
  have small (u : ℕ) (a:u≤L) : u≤Q:=by apply a.trans;dsimp [Q];ring_nf;omega
  refine ⟨?_,?_,?_,(small _ smallN).trans fit,?_,channels.trans fit,?_,(small _ smallX).trans fit,?_⟩
  · apply le_trans _ fit
    change 6+2*(v.setup.retained.donors*(2*cap))≤Q
    rw [donors]
    calc _≤6+2*(L*(2*L)):=by gcongr
         _≤_:=by dsimp [Q];ring_nf;omega
  · apply le_trans _ fit
    calc _≤L*L:=Nat.mul_le_mul smallA smallN
         _≤_:=by dsimp [Q];ring_nf;omega
  · apply le_trans _ fit
    change 8+12*(X*(2*cap))+(X+D*X+(X*(2*cap)+DescentSharedBookScan.width z.k (2^n) D))+
      (X*X+D*(D*6))≤Q
    calc _≤8+12*(L*(2*L))+(L+L*L+(L*(2*L)+((L+1)*L*(L+1))*((L+1)*((L+1)*L*(L+1)))))+(L*L+L*(L*6)):=by gcongr
         _≤_:=by dsimp [Q];ring_nf;omega
  · apply le_trans _ fit
    calc _≤(7*L)*L:=Nat.mul_le_mul (Nat.mul_le_mul_left 7 smallA) smallX
         _≤_:=by dsimp [Q];ring_nf;omega
  · apply le_trans _ fit
    change 2*(X*(2*cap))+(1+(2*(DescentResetLocalRoster.rootSlots z.k (2^n)*(2^n+2^Ht))+
      2*(DescentResetLocalRoster.rootSlots z.k (2^n)*DescentResetCableSlots.cableCap board Ht)))≤Q
    calc _≤2*(L*(2*L))+(1+(2*((2*L+2*L*(L+1))*(L+L))+2*((2*L+2*L*(L+1))*L))) :=by gcongr
         _≤_:=by dsimp [Q];ring_nf;omega
  · apply le_trans _ fit
    change 37+28*(2*(X*(2*cap))/2)≤Q
    simp only [Nat.mul_div_cancel_left _ (by decide : 0<2)]
    calc _≤37+28*(L*(2*L)):=by gcongr
         _≤_:=by dsimp [Q];ring_nf;omega

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
