import OAI.Hierarchy.DescentNormalizedCalendarPurchase

namespace OAI
/-! The original head grain is positive and its native width is representable
at the same word ratio and cutoffs as the complete calendar invoice. -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler TerminalScale Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ}
  (board : NonlinearExpanders.Graph n d) (op : RotorSpec) (t f g resetCost cut drift bound : ℕ)
local notation "κ" => 1+(hostRate t resetCost+capRate G t g)*(t+1)+8+cutRate t f g

def GrainRoom (ratio τ B h : ℕ) : Prop :=
  ∀copies,let J:=Nat.log 2 h/(2*B)
    let S:=stageNumbers G t J f g resetCost copies (tail τ J)
    let k:=groupBits t J (hostRate t resetCost) (capRate G t g) (cutRate t f g)
    let p:=headGrain G S k h
    0 < p ∧ S.firstWidth G.b p < 2^(ratio*h)

theorem grain_room {ratio τ B : ℕ} (cpu : 0 < ratio) (large : 20 ≤ B)
    (reserve : 2*localSocketRate G t g ≤ τ)
    (budget : 2*(localSocketRate G t g+(τ+κ+4))+Nat.clog 2 G.b*(t+1) ≤ B) :
    ∀ᶠ h:ℕ in atTop,GrainRoom G t f g resetCost ratio τ B h :=by
  filter_upwards [early_native_packing G t f g resetCost τ B large reserve budget] with h fit
  intro copies J S k p
  have packed:=fit copies
  let s:=S.firstWidth G.b p
  let j:=headChunk G S
  have first : 2^J ≤ s:=packed.2.2.1
  have short : 16*(2^j*s) ≤ h:=packed.2.2.2.1
  have fits : s ≤ h:=((Nat.le_mul_of_pos_left s (Nat.two_pow_pos j)).trans
    (Nat.le_mul_of_pos_left (2^j*s) (by decide : 0 < 16))).trans short
  constructor
  · by_contra! dead
    have zero : p=0:=by omega
    have absent:s=0:=by simp [s,AtomSchedule.firstWidth,AtomSchedule.grainAt,zero]
    have printed:=Nat.two_pow_pos J
    omega
  · exact (fits.trans (Nat.le_mul_of_pos_left h cpu)).trans_lt Nat.lt_two_pow_self

theorem normalized_calendar_live_at_ratio (saving : ℕ) (branch : G.b ≤ 2^(capRate G t g)) :
    ∃purchaseLeast head : ℕ,∀ratio ≥ purchaseLeast,
      ∃minTail : ℕ,∀τ ≥ minTail,∃minBus : ℕ,∀B ≥ minBus,∀ᶠ h:ℕ in atTop,
        GrainRoom G t f g resetCost ratio τ B h ∧
        NormalizedRuns G board op t f g resetCost cut drift bound branch head ratio τ B h :=by
  obtain ⟨A,head,receipt⟩:=normalized_calendar_at_ratio G board op t f g resetCost cut drift bound saving branch
  refine ⟨max 1 A,head,?_⟩
  intro ratio word
  obtain ⟨T,work⟩:=receipt ratio ((le_max_right ..).trans word)
  refine ⟨max T (2*localSocketRate G t g),?_⟩
  intro τ paid
  obtain ⟨Q,issued⟩:=work τ ((le_max_left ..).trans paid)
  let packing:=2*(localSocketRate G t g+(τ+κ+4))+Nat.clog 2 G.b*(t+1)
  refine ⟨max Q (max 20 packing),?_⟩
  intro B funded
  have limits:= (le_max_right Q (max 20 packing)).trans funded
  exact (grain_room G t f g resetCost ((le_max_left ..).trans word) ((le_max_left ..).trans limits)
    ((le_max_right ..).trans paid) ((le_max_right ..).trans limits)).and (issued B ((le_max_left ..).trans funded))

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
