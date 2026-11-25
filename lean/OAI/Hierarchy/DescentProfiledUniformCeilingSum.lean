import OAI.Hierarchy.DescentProfiledUniformPreliminary
import OAI.Hierarchy.DescentProfiledOrdinaryUniformRaster
import OAI.Hierarchy.DescentProfiledUniformSignedGuard
import OAI.Hierarchy.DescentRegisteredSignedBeforeFull

namespace OAI
/-! One address exponent controls both the advancing floor and the actual
signed tests once the native component extents have uniform exponents. -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open Chronology Chronology.RegisterTimeline DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook
open DescentSIMDLookup DescentPacking.PackedMatch DescentPacking.PackedMatch.Local.Stage Filter
noncomputable section
set_option Elab.async false
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (op : RotorSpec) (t f g reset drift bound : ℕ)
local notation "offer" τ:arg B:arg h:arg => ProfiledOrdinaryOffer G f g board op t reset τ drift bound B h
local notation "V" => ∀τ B h,offer τ B h → ℕ

def UniformRoof (value : V) : Prop :=
  ∃C:ℕ,∀τ B,0 < B → SignedStage.unitRate G t f g reset < B → τ ≤ B →
    ∀ᶠ h:ℕ in atTop,∀x:offer τ B h,value τ B h x ≤ 2^(C*h)

namespace UniformRoof
variable {G board op t f g reset drift bound}
variable {a b : (τ B h : ℕ) → ProfiledOrdinaryOffer G f g board op t reset τ drift bound B h → ℕ}
local notation "budget" => UniformRoof G board op t f g reset drift bound

theorem add (fa : budget a) (fb : budget b) : budget (fun τ B h x=>a τ B h x+b τ B h x):=by
  change (∃ C : ℕ, _) at fa fb ⊢
  rcases fa with ⟨A,af⟩
  rcases fb with ⟨C,cf⟩
  refine ⟨max A C+1,?_⟩
  intro τ B den small short
  filter_upwards [af τ B den small short,cf τ B den small short,eventually_ge_atTop 1] with h ar cr pos
  intro x
  have ma:=((ar x).trans (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.mul_le_mul_right h (le_max_left A C))))
  have mc:=((cr x).trans (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.mul_le_mul_right h (le_max_right A C))))
  have bump : max A C*h+1 ≤ (max A C+1)*h := by
    rw [Nat.add_mul,Nat.one_mul]
    exact Nat.add_le_add_left pos _
  have twice:=Nat.pow_le_pow_right (by decide : 0 < 2) bump
  exact (Nat.add_le_add ma mc).trans (by simpa only [Nat.pow_succ,Nat.mul_two] using twice)

theorem of_le (fa : budget a) (cover : ∀ (τ B h : ℕ) (x : offer τ B h),b τ B h x ≤ a τ B h x) : budget b:=by
  change (∃ C : ℕ, _) at fa ⊢
  rcases fa with ⟨C,bills⟩
  exact ⟨C,fun τ B d s b=>(bills τ B d s b).mono fun h lim x=>(cover τ B h x).trans (lim x)⟩

end UniformRoof
local notation "budget" => UniformRoof G board op t f g reset drift bound
local notation "v" x:arg => (x).model

theorem uniform_span_sum
    (parts : budget (fun _ _ _ x=>(v x).vector.endAddress 0+(v x).resolver.endAddress 0+
      (v x).metadata.ordinaryEnd 0+(v x).operandBook.endAddress 0))
    (retained : budget (fun _ _ _ x=>(v x).survivorWords))
    (reference : budget (fun _ _ _ x=>(v x).referenceWords))
    (venue : budget (fun _ _ _ x=>(v x).venue.endAddress 0))
    (primitive : budget (fun _ _ _ x=>(v x).primitiveRoof 0)) :
    budget (fun _ _ _ x=>max x.endAt (x.model.signedGuard x.stageFloor)-x.slot.position.floor) :=by
  obtain ⟨P,front⟩:=uniform_preliminary G board op t f g reset drift bound
  obtain ⟨R,scan⟩:=uniform_raster G board op t f g reset drift bound
  obtain ⟨S,guard⟩:=uniform_signed_guard_excess G board op t f g reset drift bound
  have pre : budget (fun τ B h x=>preliminary G board op t f g reset τ drift bound B h x):=
    ⟨P,fun τ B d _ _=>front τ B d⟩
  have raster : budget (fun _ _ _ x=>StageVenueTail.OrdinaryRaster.roof x.model.area x.model.venue x.model.rasterLanes 0):=
    ⟨R,fun τ B d _ _=>(scan τ B d).mono fun h caps x=>by simpa only [←pow_mul,Nat.mul_comm h R] using caps x⟩
  have extra : budget (fun _ _ _ x=>(v x).signedGuard x.stageFloor-(v x).signedEnd x.stageFloor):=
    ⟨S,fun τ B _ _ _=>guard τ B⟩
  have one : budget (fun _ _ _ _=>1):=⟨0,fun _ _ _ _ _=>Eventually.of_forall fun _ _=>by simp⟩
  have cap : budget (fun _ _ _ x=>x.model.fullCeiling):=by
    have roots := UniformRoof.add pre parts
    have saved := UniformRoof.add roots retained
    have refs := UniformRoof.add saved reference
    have stage := UniformRoof.add refs venue
    have rest := UniformRoof.add stage primitive
    have pass := UniformRoof.add rest raster
    apply UniformRoof.of_le (UniformRoof.add pass one)
    intro τ B h x
    simp only [PhysicalOrdinary.fullCeiling,PhysicalOrdinary.returnedCeiling,PhysicalOrdinary.ceiling,
      PhysicalOrdinary.argumentExtra,Dated.Ordinary.ordinaryWords,preliminary]
    omega
  apply UniformRoof.of_le (UniformRoof.add cap extra)
  intro τ B h x
  have test:=x.model.signed_guard_span x.slot.position.floor
  rw [x.model_floor] at test
  have last:=x.span_le
  omega

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
