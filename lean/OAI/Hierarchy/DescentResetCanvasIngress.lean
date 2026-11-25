import OAI.Hierarchy.DescentResetCanvasIngressShape
import OAI.Hierarchy.DescentResetCanvasAmount
import OAI.Hierarchy.DescentVenueExprSlabs
import OAI.Hierarchy.DescentVenueSlabPhase
import OAI.Hierarchy.DescentResetSignedTokens

namespace OAI
/-! # Old funded columns and incidences at the fixed lane width of a reset -/
namespace Hierarchy.DescentResetCanvasIngress
open DescentSIMDLookup DescentPackedColony DescentSixParty.Chronology ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical
noncomputable section
namespace Layout
variable (s : Layout)
def source (base : ℕ) := s.collector.amount (s.atomEnd base)
def tokens (base : ℕ) := s.signed.bank base
def phase (base w : ℕ) (hubs : Bank) (atom : Fin (2^s.k)→Expr) (ports : s.signed.Slot→Bank) : NativePhase w :=
  ((s.signed.phase base w ports).seq (DescentVenueSlabs.ExprInputs.phase s.amounts atom (s.signedEnd base) w)).seq
    (s.collector.phase (s.atomEnd base) w hubs (s.atomBank base) (s.signed.raw base))

private theorem dictionary_before (base : ℕ) : (s.signed.dictionary base).base ≤ s.signedEnd base := by
  let b := s.signed.dictionary base
  change b.base ≤ b.base+b.size+s.signed.slots*s.signed.rows+2^Nat.clog 2 s.signed.rows
  exact (Nat.le_add_right b.base b.size).trans
    ((Nat.le_add_right _ (s.signed.slots*s.signed.rows)).trans (Nat.le_add_right _ _))

theorem order (base : ℕ) : base≤ s.signedEnd base ∧ s.signedEnd base≤ s.atomEnd base ∧ s.atomEnd base≤ s.endAddress base := by
  have one : base≤DescentVenueSlabs.endAddress s.signed.venue base := by rw [DescentVenueSlabs.translates];omega
  have two : s.signedEnd base≤ s.atomEnd base := by unfold atomEnd;rw [DescentVenueSlabs.translates];omega
  have three := s.collector.positions (s.atomEnd base)
  exact ⟨one.trans (dictionary_before s base),two,
    three.1.trans (three.2.1.trans ((Nat.le_add_right ..).trans three.2.2))⟩

theorem any {w : ℕ} (base : ℕ) (hubs : Bank) (atom : Fin (2^s.k)→Expr) (ports : s.signed.Slot→Bank)
    (m : Memory w) (oldHub : hubs.Fits w base) (oldAtom : ∀x,(atom x).Fits w base)
    (oldPorts : ∀j,(ports j).Fits w base) (room : s.endAddress base<2^w) :
    (s.phase base w hubs atom ports).Runs m ∧
    ∀a,a<base ∨ s.endAddress base≤a→(s.phase base w hubs atom ports).image m a=m a := by
  obtain ⟨one,two,three⟩:=s.order base
  have atomRoom:=three.trans_lt room
  have signedRoom:=two.trans_lt atomRoom
  obtain ⟨run1,frame1⟩:=s.signed.any base ports m oldPorts signedRoom
  let mid:=(s.signed.phase base w ports).image m
  obtain ⟨run2,frame2⟩:=DescentVenueSlabs.ExprInputs.any s.amounts atom (s.signedEnd base) mid
    (fun x=>ProtocolRAMGeneratedWrite.fits_mono _ one (oldAtom x)) atomRoom
  let mem:=DescentVenueSlabs.ExprInputs.image s.amounts atom (s.signedEnd base) mid
  have oldRaw (j : s.signed.Slot) : (s.signed.raw base j).Fits w (s.atomEnd base) := by
    have h:=((s.signed.room signedRoom).2.1 j).1
    exact ⟨h.1,h.2.1,h.2.2.trans ((dictionary_before s base).trans two)⟩
  obtain ⟨run3,frame3⟩:=s.collector.any (s.atomEnd base) hubs (s.atomBank base) (s.signed.raw base) mem
    ⟨oldHub.1,oldHub.2.1,oldHub.2.2.trans (one.trans two)⟩
    (fun x=>(DescentVenueSlabs.page_room s.amounts (s.signedEnd base) w x atomRoom).1) oldRaw room
  let signed := s.signed.phase base w ports
  let atoms := DescentVenueSlabs.ExprInputs.phase s.amounts atom (s.signedEnd base) w
  let collected := s.collector.phase (s.atomEnd base) w hubs (s.atomBank base) (s.signed.raw base)
  refine ⟨NativePhase.seq_runs (signed.seq atoms) collected m
    (NativePhase.seq_runs signed atoms m run1 run2) run3,?_⟩
  intro a h
  have third : a<s.atomEnd base ∨ s.endAddress base≤a :=
    h.imp (fun lo=>lo.trans_le (one.trans two)) id
  have second : a<s.signedEnd base ∨ s.atomEnd base≤a :=
    h.imp (fun lo=>lo.trans_le one) (fun hi=>three.trans hi)
  have first : a<base ∨ s.signedEnd base≤a :=
    h.imp id (fun hi=>(two.trans three).trans hi)
  exact (frame3 a third).trans ((frame2 a second).trans (frame1 a first))

end Layout
end
end Hierarchy.DescentResetCanvasIngress

end OAI
