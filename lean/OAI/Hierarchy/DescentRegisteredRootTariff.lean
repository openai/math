import OAI.Hierarchy.DescentRegisteredResetCharges
import OAI.Hierarchy.DescentResetSelectedRootBill

namespace OAI
/-! The wrapped processor's roots charge at its actual predecessor register. -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler TerminalScale DescentDatedAddressBook PhysicalReset DescentPackedWalsh
open DescentCompiler DescentSixParty.Chronology DescentPacking.PackedMatch.Local.Stage DescentPrimitivePalette
open ProtocolRAM DescentStaticWordColumn Filter
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (G : PoweredGadget F) {deg : ℕ} {bs : P→ℕ} (W : MarkedWorld F deg P bs) (q ε : ℝ)

theorem registered_root_tariff_all (op : RotorSpec) (t f g reset D n d z ratio receiver saving : ℕ) :
    ∃exponent : ℕ,∀τ B,0 < τ → 0 < B →
      2*(1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g) ≤ B →
      2*(3*stencilRate G t f g reset+1) ≤ B →
      ∀ᶠ h:ℕ in atTop,∀ (P₀ : Type) (d₀ : ℕ) (bs₀ : P₀→ℕ) (world : MarkedWorld F d₀ P₀ bs₀) (q₀ ε₀ : ℝ),∀ copies i p w state wire hist drift degree s Z : ℕ,
        let J:=Nat.log 2 h/(2*B)
        let tb:=tail τ J
        let S:=stageNumbers G t J f g reset copies tb
        let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
        ∀(r : Reached world G q₀ ε₀ S k i state D wire hist) (rates : ResetRates G S k D n d op.C f g z tb)
          (ordinary : ℕ→Dated.Ordinary) (prev : DatePorts) (floor : ℕ)
          (space : ScheduledCodeRoom G S rates.board k tb i p f g drift degree h ordinary op s Z
            prev.operandLanes prev.roleLanes prev.venue prev.io floor w prev.archive),
        let a:=scheduled G S rates.board k tb i p f g drift degree h ordinary op s Z prev.operandLanes prev.roleLanes
          prev.venue prev.io.wire prev.io.roster floor
        let u:=DatePorts.innerResetInputs G S rates.board k tb i p f g drift degree h ordinary op s Z prev floor w space
        i < S.length → i%(S.rounds+1)=S.rounds → p ≤ h → 2^h ≤ copies → w ≤ ratio*h →
        prev.venue.degree=D → prev.venue.paidBits=S.censusBits p → prev.venue.lanes=incoming S k tb p f h ordinary i →
        r.placement.cap=((capCalendar G.b S.rounds g S.height).take i).prod*256 →
        (∀x : Fin (2^k),(prev.io.atoms x.val).work ≤ 7) →
        8*S.localWalshBits p (S.groupWidth k tb i+k) f (quota t) ≤ h →
        8*a.successor.groupWidth ≤ h → a.successor.groupWidth ≤ TerminalScale.scale J receiver →
        a.PrimeRoom (a.stageStart floor) u.src u.count u.sourceRows u.oldDegree w →
        (DatePorts.resetCharges G S rates.board k tb i p f g drift degree h ordinary op s Z prev floor w space).roots ≤
          S.hostSize i*h*TerminalScale.scale J exponent+S.hostSize i*(S.groupCount i*S.radix)*TerminalScale.scale J exponent+
            6*(copies/(2^J)^saving) := by
  obtain ⟨lead,exp,native⟩:=selected_root_uniform_all G t f g reset D n d op.C z ratio receiver saving
  refine ⟨selectedRootRate G t f g reset exp,?_⟩
  intro τ B time den lane table
  have complete:=native τ B time den lane table
  unfold RootDatePriceAll at complete
  filter_upwards [complete,selected_root_unit_scale G t f g reset τ B D ratio lead exp den] with h bound unit
  intro P₀ d₀ bs₀ world q₀ ε₀ copies i p w state wire hist drift degree s Z J tb S k r rates ordinary prev floor space a u
    live atReset payload ambient hardware oldDegree precision pitch cap array bits room width ready
  let M:=incoming S k tb p f h ordinary (i+1)
  have bill:=bound P₀ d₀ bs₀ world q₀ ε₀ copies i p w state wire hist r rates drift degree M op.w prev.operandLanes prev.roleLanes
    (printedBits G s Z op) ordinary prev.venue prev.io floor prev.archive.count live atReset payload ambient
    hardware oldDegree precision pitch cap array bits room width
  change a.PrimeRoom (a.stageStart floor) (a.ingress.source floor) prev.archive.count (S.groupCount i) prev.venue.degree w at ready
  let front:=a.ingress.phase floor w prev.io.hubs (fun x=>prev.io.atoms x.val)
    (fun t=>prev.io.wire t.1.val t.2.val)
  let amount (d₀ : ℕ):=
    let ticks:=a.throughPublishedTicks u.shape (a.stageStart floor) u.count u.hub u.g u.Y u.roots u.book
      u.sourceRows d₀ w u.bookFits
    let body:=a.throughPublishedRoots u.shape (a.stageStart floor) u.count u.hub u.g u.Y u.roots u.book u.src
      u.sourceRows d₀ w u.bookFits
    (front.ticks+ticks+7*names (front.program.seq body))*w
  change amount prev.venue.degree ≤ _
  rw [oldDegree]
  have prime : a.PrimeRoom (a.stageStart floor) (a.ingress.source floor) prev.archive.count (S.groupCount i) D w :=
    oldDegree ▸ ready
  have original:=bill (by
    change a.PrimeRoom (a.stageStart floor) (a.ingress.source floor) prev.archive.count (S.groupCount i) D w
    exact prime) space.prepared
  apply original.trans
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left _ unit) (Nat.mul_le_mul_left _ unit)) _

theorem registered_root_tariff (op : RotorSpec) (t f g reset D n d z ratio receiver saving : ℕ) :
    ∃exponent : ℕ,∀τ B,0 < τ → 0 < B →
      2*(1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g) ≤ B →
      2*(3*stencilRate G t f g reset+1) ≤ B →
      ∀ᶠ h:ℕ in atTop,∀ copies i p w state wire hist drift degree s Z : ℕ,
        let J:=Nat.log 2 h/(2*B)
        let tb:=tail τ J
        let S:=stageNumbers G t J f g reset copies tb
        let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
        ∀(r : Reached W G q ε S k i state D wire hist) (rates : ResetRates G S k D n d op.C f g z tb)
          (ordinary : ℕ→Dated.Ordinary) (prev : DatePorts) (floor : ℕ)
          (space : ScheduledCodeRoom G S rates.board k tb i p f g drift degree h ordinary op s Z
            prev.operandLanes prev.roleLanes prev.venue prev.io floor w prev.archive),
        let a:=scheduled G S rates.board k tb i p f g drift degree h ordinary op s Z prev.operandLanes prev.roleLanes
          prev.venue prev.io.wire prev.io.roster floor
        let u:=DatePorts.innerResetInputs G S rates.board k tb i p f g drift degree h ordinary op s Z prev floor w space
        i < S.length → i%(S.rounds+1)=S.rounds → p ≤ h → 2^h ≤ copies → w ≤ ratio*h →
        prev.venue.degree=D → prev.venue.paidBits=S.censusBits p → prev.venue.lanes=incoming S k tb p f h ordinary i →
        r.placement.cap=((capCalendar G.b S.rounds g S.height).take i).prod*256 →
        (∀x : Fin (2^k),(prev.io.atoms x.val).work ≤ 7) →
        8*S.localWalshBits p (S.groupWidth k tb i+k) f (quota t) ≤ h →
        8*a.successor.groupWidth ≤ h → a.successor.groupWidth ≤ TerminalScale.scale J receiver →
        a.PrimeRoom (a.stageStart floor) u.src u.count u.sourceRows u.oldDegree w →
        (DatePorts.resetCharges G S rates.board k tb i p f g drift degree h ordinary op s Z prev floor w space).roots ≤
          S.hostSize i*h*TerminalScale.scale J exponent+S.hostSize i*(S.groupCount i*S.radix)*TerminalScale.scale J exponent+
            6*(copies/(2^J)^saving) := by
  obtain ⟨ex,price⟩:=registered_root_tariff_all G op t f g reset D n d z ratio receiver saving
  refine ⟨ex,?_⟩
  intro τ B time den lanes tables
  exact (price τ B time den lanes tables).mono fun _ h=>h P deg bs W q ε

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
