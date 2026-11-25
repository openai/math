import OAI.Hierarchy.DescentRegisteredResetSum
import OAI.Hierarchy.DescentRegisteredActorTariff
import OAI.Hierarchy.DescentRegisteredDirectoryTariff
import OAI.Hierarchy.DescentRegisteredContactTariff
import OAI.Hierarchy.DescentRegisteredMasksTariff
import OAI.Hierarchy.DescentRegisteredNumberTariff
import OAI.Hierarchy.DescentRegisteredFundingTariff
import OAI.Hierarchy.DescentRegisteredVenueTariff
import OAI.Hierarchy.DescentRegisteredRootTariff

namespace OAI
/-! Uniform original component prices at a single chronological input position. -/
namespace Hierarchy.DescentSixParty.RegisteredReset
open DescentCompiler TerminalScale DescentDatedAddressBook PhysicalReset NativePitch Chronology Chronology.RegisterTimeline Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
  (op : RotorSpec) (K : Parameters) (saving : ℕ)
local notation "first" a:arg J:arg τ:arg => (stageNumbers G K.t J K.f K.g K.reset (Sample.copies a) (tail τ J)).firstWidth G.b (Sample.p a)
local notation "grain" a:arg J:arg τ:arg => (stageNumbers G K.t J K.f K.g K.reset (Sample.copies a) (tail τ J)).grainAt G.b (Sample.p a) 0
local notation "cell" J:arg => groupBits K.t J (hostRate K.t K.reset) (capRate G K.t K.g) (cutRate K.t K.f K.g)

theorem actor : Region G board op K 2 saving := by
  obtain ⟨C,E,price⟩:=registered_actor_tariff G board op K.t K.f K.g K.reset K.degree K.rate K.ratio K.receiver saving
  refine ⟨C,E,1,0,?_⟩
  intro τ B _ den _ _
  filter_upwards [price τ B den] with h current
  intro a g _ J
  rcases a with ⟨copies,age,p,w,deg,pos,ordinary,rates,same,space,cap⟩
  subst board
  let a : Sample G rates.board op K τ B h := ⟨copies,age,p,w,deg,pos,ordinary,rates,rfl,space,cap⟩
  have quoted:=current a.copies a.age a.p a.w K.drift a.degreeLimit (first a J τ) (grain a J τ) a.rates
  have paid:=quoted a.ordinary (a.position.ports.afterPad (cell J) a.position.floor)
    (a.position.ports.priorStart (cell J) a.position.floor) a.space rfl g.degreeAt g.live g.input g.ambient g.bus g.walsh g.root g.width
  have charge (z : EnteredCharges) (start : ℕ) : z.paddedAmount start 2 = z.actor := rfl
  rw [charge, one_mul]
  exact paid

theorem received : Region G board op K 3 saving := by
  obtain ⟨C,E,C₁,E₁,price⟩:=registered_directory_tariff G board op K.t K.f K.g K.reset K.degree K.rate K.ratio K.receiver saving
  refine ⟨C,E,1,0,?_⟩
  intro τ B _ den _ _
  filter_upwards [price τ B den] with h current
  intro a g _ J
  rcases a with ⟨copies,age,p,w,deg,pos,ordinary,rates,same,space,cap⟩
  subst board
  let a : Sample G rates.board op K τ B h := ⟨copies,age,p,w,deg,pos,ordinary,rates,rfl,space,cap⟩
  have quoted:=current a.copies a.age a.p a.w K.drift a.degreeLimit (first a J τ) (grain a J τ) a.rates
  have paid:=quoted a.ordinary (a.position.ports.afterPad (cell J) a.position.floor)
    (a.position.ports.priorStart (cell J) a.position.floor) a.space rfl g.degreeAt g.live g.input g.ambient g.bus g.walsh g.root g.width
  have charge (z : EnteredCharges) (start : ℕ) : z.paddedAmount start 3 = z.received := rfl
  rw [charge, one_mul]
  exact paid.1

theorem compact : Region G board op K 4 saving := by
  obtain ⟨C₀,E₀,C,E,price⟩:=registered_directory_tariff G board op K.t K.f K.g K.reset K.degree K.rate K.ratio K.receiver saving
  refine ⟨C,E,1,0,?_⟩
  intro τ B _ den _ _
  filter_upwards [price τ B den] with h current
  intro a g _ J
  rcases a with ⟨copies,age,p,w,deg,pos,ordinary,rates,same,space,cap⟩
  subst board
  let a : Sample G rates.board op K τ B h := ⟨copies,age,p,w,deg,pos,ordinary,rates,rfl,space,cap⟩
  have quoted:=current a.copies a.age a.p a.w K.drift a.degreeLimit (first a J τ) (grain a J τ) a.rates
  have paid:=quoted a.ordinary (a.position.ports.afterPad (cell J) a.position.floor)
    (a.position.ports.priorStart (cell J) a.position.floor) a.space rfl g.degreeAt g.live g.input g.ambient g.bus g.walsh g.root g.width
  have charge (z : EnteredCharges) (start : ℕ) : z.paddedAmount start 4 = z.compact := rfl
  rw [charge, one_mul]
  exact paid.2

theorem contact : Region G board op K 5 saving := by
  obtain ⟨C,E,price⟩:=registered_contact_tariff G board op K.t K.f K.g K.reset K.degree K.rate K.ratio K.receiver saving
  refine ⟨C,E,1,0,?_⟩
  intro τ B _ den _ _
  filter_upwards [price τ B den] with h current
  intro a g _ J
  rcases a with ⟨copies,age,p,w,deg,pos,ordinary,rates,same,space,cap⟩
  subst board
  let a : Sample G rates.board op K τ B h := ⟨copies,age,p,w,deg,pos,ordinary,rates,rfl,space,cap⟩
  have quoted:=current a.copies a.age a.p a.w K.drift a.degreeLimit (first a J τ) (grain a J τ) a.rates
  have paid:=quoted a.ordinary (a.position.ports.afterPad (cell J) a.position.floor)
    (a.position.ports.priorStart (cell J) a.position.floor) a.space rfl g.degreeAt g.live g.input g.ambient g.bus g.walsh g.root g.width
  have charge (z : EnteredCharges) (start : ℕ) : z.paddedAmount start 5 = z.contact := rfl
  rw [charge, one_mul]
  exact paid.1

theorem masks : Region G board op K 6 saving := by
  obtain ⟨C,E,price⟩:=registered_masks_tariff G board op K.t K.f K.g K.reset K.degree K.rate K.ratio K.receiver saving
  refine ⟨C,E,3,0,?_⟩
  intro τ B _ den _ _
  filter_upwards [price τ B den] with h current
  intro a g _ J
  rcases a with ⟨copies,age,p,w,deg,pos,ordinary,rates,same,space,cap⟩
  subst board
  let a : Sample G rates.board op K τ B h := ⟨copies,age,p,w,deg,pos,ordinary,rates,rfl,space,cap⟩
  have quoted:=current a.copies a.age a.p a.w K.drift a.degreeLimit (first a J τ) (grain a J τ) a.rates
  have paid:=quoted a.ordinary (a.position.ports.afterPad (cell J) a.position.floor)
    (a.position.ports.priorStart (cell J) a.position.floor) a.space rfl g.degreeAt g.live g.input g.ambient g.bus g.walsh g.root g.width
  have charge (z : EnteredCharges) (start : ℕ) : z.paddedAmount start 6 = z.masks := rfl
  rw [charge]
  exact paid

theorem classes : Region G board op K 12 saving := by
  obtain ⟨C,E,price⟩:=registered_contact_tariff G board op K.t K.f K.g K.reset K.degree K.rate K.ratio K.receiver saving
  refine ⟨C,E,1,0,?_⟩
  intro τ B _ den _ _
  filter_upwards [price τ B den] with h current
  intro a g _ J
  rcases a with ⟨copies,age,p,w,deg,pos,ordinary,rates,same,space,cap⟩
  subst board
  let a : Sample G rates.board op K τ B h := ⟨copies,age,p,w,deg,pos,ordinary,rates,rfl,space,cap⟩
  have quoted:=current a.copies a.age a.p a.w K.drift a.degreeLimit (first a J τ) (grain a J τ) a.rates
  have paid:=quoted a.ordinary (a.position.ports.afterPad (cell J) a.position.floor)
    (a.position.ports.priorStart (cell J) a.position.floor) a.space rfl g.degreeAt g.live g.input g.ambient g.bus g.walsh g.root g.width
  have charge (z : EnteredCharges) (start : ℕ) : z.paddedAmount start 12 = z.classes := rfl
  rw [charge, one_mul]
  exact paid.2

theorem funding : Region G board op K 9 saving := by
  obtain ⟨C,E,price⟩:=registered_funding_tariff G board op K.t K.f K.g K.reset K.degree K.rate K.ratio K.receiver saving
  refine ⟨C,E,1,0,?_⟩
  intro τ B _ den _ _
  filter_upwards [price τ B den] with h current
  intro a g _ J
  rcases a with ⟨copies,age,p,w,deg,pos,ordinary,rates,same,space,cap⟩
  subst board
  let a : Sample G rates.board op K τ B h := ⟨copies,age,p,w,deg,pos,ordinary,rates,rfl,space,cap⟩
  have quoted:=current a.copies a.age a.p a.w K.drift a.degreeLimit (first a J τ) (grain a J τ) a.rates
  have paid:=quoted a.ordinary (a.position.ports.afterPad (cell J) a.position.floor)
    (a.position.ports.priorStart (cell J) a.position.floor) a.space rfl g.degreeAt g.live g.boundary g.input g.ambient g.bus g.hosts g.groups g.blocks g.precision g.pitch a.cap g.walsh g.root g.width
  have charge (z : EnteredCharges) (start : ℕ) : z.paddedAmount start 9 = z.funding := rfl
  rw [charge, one_mul]
  exact paid

theorem numbered : Region G board op K 7 saving := by
  obtain ⟨C,E,price⟩:=registered_number_tariff G board op K.t K.f K.g K.reset K.degree K.ratio K.receiver saving
  refine ⟨C,E,1,0,?_⟩
  intro τ B _ den _ _
  filter_upwards [price τ B den] with h current
  intro a g _ J
  rcases a with ⟨copies,age,p,w,deg,pos,ordinary,rates,same,space,cap⟩
  subst board
  let a : Sample G rates.board op K τ B h := ⟨copies,age,p,w,deg,pos,ordinary,rates,rfl,space,cap⟩
  have paid:=current a.copies a.age a.p a.w K.drift a.degreeLimit (first a J τ) (grain a J τ)
    a.ordinary (a.position.ports.afterPad (cell J) a.position.floor)
    (a.position.ports.priorStart (cell J) a.position.floor) a.space g.degreeAt g.live g.input g.ambient g.bus
    g.walsh g.root g.width g.roof
  have charge (z : EnteredCharges) (start : ℕ) : z.paddedAmount start 7 = z.numbered := rfl
  rw [charge, one_mul]
  exact paid

theorem venue : Region G board op K 10 saving := by
  obtain ⟨next,C,E,price⟩:=registered_venue_tariff G board K.t K.f K.g K.reset K.degree K.receiver K.ratio saving
  let extra:=groupRate G K.t K.f K.g K.reset+(6*(terminalDegree G K.t K.f K.g K.reset+1)+19)
  refine ⟨C,E,1,next+2+2*extra,?_⟩
  intro τ B _ den limit branch
  filter_upwards [price op K.drift τ B (by omega) branch (by dsimp only [extra] at limit;omega)] with h current
  intro a g _ J
  have paid:=current a.copies a.age a.p a.w a.degreeLimit (first a J τ) (grain a J τ)
    a.ordinary (a.position.ports.afterPad (cell J) a.position.floor)
    (a.position.ports.priorStart (cell J) a.position.floor) a.space g.live g.input g.ambient g.bus g.ordinaryAt
    g.hosts g.blocks g.degreeAt g.walsh g.root g.width
  have charge (z : EnteredCharges) (start : ℕ) : z.paddedAmount start 10 = z.venue := rfl
  rw [charge, one_mul]
  exact paid

theorem roots : Region G board op K 1 saving := by
  let lanes:=2*(1+(hostRate K.t K.reset+capRate G K.t K.g)*(K.t+1)+8+cutRate K.t K.f K.g)
  let tables:=2*(3*stencilRate G K.t K.f K.g K.reset+1)
  obtain ⟨E,price⟩:=registered_root_tariff_all G op K.t K.f K.g K.reset K.degree n d K.rate K.ratio K.receiver saving
  refine ⟨1,E,6,lanes+tables,?_⟩
  intro τ B time den limit _
  filter_upwards [price τ B time den (by change lanes ≤ B;omega) (by change tables ≤ B;omega)] with h current
  intro a g w J
  rcases a with ⟨copies,age,p,bus,deg,pos,ordinary,rates,same,space,cap⟩
  subst board
  let a : Sample G rates.board op K τ B h := ⟨copies,age,p,bus,deg,pos,ordinary,rates,rfl,space,cap⟩
  have quoted:=current w.parties w.degree w.bits w.world w.q w.ε a.copies a.age a.p a.w w.state w.wire w.hist
    K.drift a.degreeLimit (first a J τ) (grain a J τ) w.reached a.rates
  have paid:=quoted a.ordinary (a.position.ports.afterPad (cell J) a.position.floor)
    (a.position.ports.priorStart (cell J) a.position.floor) a.space g.live g.boundary g.input g.ambient g.bus
    g.degreeAt g.precision g.pitch w.capacity g.atomWork g.walsh g.root g.width g.prime
  have charge (z : EnteredCharges) (start : ℕ) : z.paddedAmount start 1 = z.roots := rfl
  rw [charge]
  simp only [one_mul]
  exact paid

end
end Hierarchy.DescentSixParty.RegisteredReset

end OAI
