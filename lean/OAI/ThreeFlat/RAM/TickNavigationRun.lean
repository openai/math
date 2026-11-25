import OAI.ThreeFlat.RAM.TickActiveROM
import OAI.ThreeFlat.RAM.TickStageSpec
import OAI.ThreeFlat.RAM.TickNavigationEntry
import OAI.ThreeFlat.RAM.TickFuel

namespace OAI
/-! # Native chronological replay and group-length installation in the emitted tick -/

noncomputable section
namespace ThreeFlat.RAM.TickActiveROM
open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink DescriptorScan Diagonal.TickChronology TickFuel
open BitLayout Contraction
open scoped Fin.CommRing Classical

variable {F : Type*} [Field F] [Fintype F] {p H J w k n m nr mr r pc : ℕ}

def boundsMemory (B : Layout) (clock : Clock) (out : Memory w) : Memory w :=
  TickControlHeader.store (range w B.bounds) (TickPairHeader.values (1+B.capacity : ℕ)
    (TickPairHeader.selected out B.clockWords B.groupCounts clock.groups) B.oldAux) out

theorem navigate (B : Layout) (clock : Clock) (fit : Fits (TickWeightedBank.shape F p H J) w)
    (M : Machine w pc r k) (nav : Block w n nr k) (prep : Block w m mr k)
    (P : Labels (n:=n) (m:=m) (k:=k) B clock fit ↪ Fin pc)
    (R : Registers B clock fit nr mr r k) (K : Fin 7 → Fin k)
    (rom : ∀ i, M.code (P i) = emit B clock fit nav prep P R K i)
    (team step : ℕ) (c : Config w pc r) (mem : Memory w)
    (here : c.pc=P (.control (.inl (TickFrontROM.phaseNo (clock.phase step),0))))
    (teamReg : c.reg (R.control 0) = (team : Word w)) (stepReg : c.reg (R.control 1) = (step : Word w))
    (phaseReg : c.reg (R.control 2) = ((clock.phase step).tag : Word w))
    (marker : mem (TickControlHeader.markerAddr (w:=w) (clock.phase step) B.oldAux B.newAux).val = 1)
    (disjoint : B.control+4 ≤ B.clockWords) (fitClock : B.clockWords+4 < 2^w)
    (td : clock.groupDuration < 2^w) (tb : clock.beginTick < 2^w) (ts : step < 2^w)
    (pre ok : Memory w → Prop) (post : Memory w → Memory w → Prop) (budget tail : ℕ) (weight : F)
    (admission : TickStageSpec.Admission (codec (TickWeightedBank.shape F p H J) fit) nav M.publicData
      pre ok post budget)
    (init : pre (TickNavigationEntry.input B clock team step mem))
    (branches : ∀ (out : Memory w), post (TickNavigationEntry.input B clock team step mem) out →
      ∀ d : Config w pc r, d.pc=TickHistoryCore.resumeAux (B.aux w k)
        (inside P Label.control (fun _ _ h => by cases h; rfl)) →
      Returns (codec (TickWeightedBank.shape F p H J) fit) M.program tail d (boundsMemory B clock out) weight) :
    Returns (codec (TickWeightedBank.shape F p H J) fit) M.program (1470+budget+21+tail) c mem
      (if ok (TickNavigationEntry.input B clock team step mem) then weight else 0) := by
  let field := codec (TickWeightedBank.shape F p H J) fit
  let core := inside P Label.control (fun _ _ h => by cases h; rfl)
  let clk := inside P Label.writeClock (fun _ _ h => by cases h; rfl)
  let nv := inside P Label.navigate (fun _ _ h => by cases h; rfl)
  let ph := clock.phase step
  let start := TickNavigationEntry.input B clock team step mem
  have ctrl (i : Fin 10) := rom (.control (.inl (TickFrontROM.phaseNo ph,i)))
  simp only [emit,TickHistoryCore.emit,TickFrontROM.phase_phaseNo] at ctrl
  obtain ⟨s,sBound,d,dpc,begin⟩ := TickNavigationEntry.advance_entry B clock M team step R.control
    (fun i => P (.control (.inl (TickFrontROM.phaseNo ph,i)))) clk R.clock (nv nav.first) c mem
    ctrl (fun i => rom (.writeClock i)) here teamReg stepReg phaseReg marker disjoint fitClock td tb ts
  obtain ⟨yes,no⟩ := admission M nv R.navigator id (P (.bound 0)) (fun i => rom (.navigate i))
    (fun _ => rfl) d start dpc init
  by_cases active : ok start
  · rw [ite_eq_left active]
    obtain ⟨t,tBound,f,out,ready,postOut,reu⟩ := yes active
    obtain ⟨wtime,wBound,z,zpc,deliver⟩ := TickPairHeader.advance_header M (fun i => P (.bound i))
      R.control (range w B.bounds) B.clockWords B.groupCounts clock.groups (1+B.capacity : ℕ) B.oldAux
      (TickHistoryCore.resumeAux _ core) (fun i => rom (.bound i)) f out ready
    have result := (((branches out postOut z zpc).prefix deliver).prefix reu).prefix begin
    exact result.later (by omega)
  · rw [ite_eq_right active]
    have reject : Returns field M.program budget d start 0 := no active
    exact (reject.prefix begin).later (by omega)


end ThreeFlat.RAM.TickActiveROM

end
end OAI
