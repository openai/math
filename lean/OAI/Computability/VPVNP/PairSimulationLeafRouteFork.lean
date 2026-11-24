import OAI.Computability.VPVNP.PairSimulationRouteValidator
import OAI.Computability.VPVNP.PairSimulationLeafHandler

/-! # Returning from the route scan or entering the private stack verifier -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafRouteFork

open BurstRAM PrivateRAM CursorRouting CursorNetwork PrimedCounter.GuessWord DFS
open scoped Fin.CommRing

variable {d H w W p r k : ℕ} [NeZero d]
  {M : Machine W p r k} {P : RouteSchedule.Program p r}
  {c : Config W p r} (v : Position d) (buf : Buffers d H w) (base : LocalPort → Word W)

/-- Once the native scan passes, its preserved cursor determines whether
the local factor returns immediately or executes the virtual validator. -/
theorem after_scan {init transit : Fin p} {t : ℕ}
    (inputs : RouteSchedule.Inputs P.reg v buf base c)
    (fit : d ≤ 2^W)
    (row : M.code P.yes = .jumpEq (P.reg 0) (P.reg 17) init transit)
    (stop : M.code P.no = .reject) {u : Config W p r}
    (scan : Prefix M c (List.replicate t .tick) u)
    (status : u.pc = (if routeAccept H w v (readBuffer buf) then P.yes else P.no))
    (frame : RouteRange.Frame (RouteSchedule.Keep P.reg) c u) :
    (routeAccept H w v (readBuffer buf) = true →
      ∃ out, Prefix M c (List.replicate (t+1) .tick) out ∧
        out.pc = (if v.1 = 0 then init else transit) ∧
        RouteRange.Frame (RouteSchedule.Keep P.reg) c out) ∧
    (routeAccept H w v (readBuffer buf) = false →
      ∀ mem bits, ¬ Returns M c mem bits) := by
  constructor
  · intro good
    have hp : u.pc = P.yes := by simpa only [good,↓reduceIte] using status
    have hu := inputs.transfer frame
    have eqz : u.reg (P.reg 0) = u.reg (P.reg 17) ↔ v.1 = 0 := by
      rw [hu.cursor,hu.zero]
      constructor
      · intro eq
        apply Fin.ext
        have hv := congrArg Fin.val eq
        rw [Fin.val_natCast,Nat.mod_eq_of_lt (v.1.isLt.trans_le fit)] at hv
        exact hv
      · rintro hz
        simp [hz]
    let out := {u with pc := if v.1=0 then init else transit}
    have step : M.program.step u = .localStep out := by
      simp only [Machine.program,hp,row,Instr.run,eqz,out]
    refine ⟨out,?_,rfl,⟨frame.regs,frame.memory,frame.persistent⟩⟩
    rw [List.replicate_add]
    exact scan.append (.tick step (.nil _))
  · intro bad mem bits ok
    obtain ⟨fuel,rep,hr⟩ := ok
    have hp : u.pc = P.no := by simpa only [bad,Bool.false_eq_true,↓reduceIte] using status
    have nope := MapLookup.reject_after_ticks scan (fun _ h => List.eq_of_mem_replicate h) (hp ▸ stop) fuel mem bits
    rw [nope] at hr; contradiction

/-- The actual fixed cursor route checker followed by the returning branch,
at the application's word widths and record capacities. -/
theorem native {e n : ℕ} {init transit : Fin p} (budget : ProcessorBudget n d e w) (host : w ≤ W)
    (hl : P.Linked M) (v : Position d) (buf : Buffers d (2^e) w) (base : LocalPort → Word W)
    (atPC : c.pc = P.pc 0) (inputs : RouteSchedule.Inputs P.reg v buf base c)
    (width : c.reg (P.reg 21) = ((8*w : ℕ) : Word W))
    (row : M.code P.yes = .jumpEq (P.reg 0) (P.reg 17) init transit)
    (stop : M.code P.no = .reject) :
    (routeAccept (2^e) w v (readBuffer buf) = true →
      ∃ out, Prefix M c (List.replicate (RouteSchedule.routeTicks W v (2^e) w+1) .tick) out ∧
        out.pc = (if v.1 = 0 then init else transit) ∧ RouteRange.Frame (RouteSchedule.Keep P.reg) c out) ∧
    (routeAccept (2^e) w v (readBuffer buf) = false → ∀ mem bits, ¬ Returns M c mem bits) := by
  obtain ⟨hd,hs,ht⟩ := RouteSchedule.hostFits budget host
  obtain ⟨out,path,pc,frame⟩ := RouteSchedule.native_exact hl v buf base c atPC inputs width hd hs ht
  exact after_scan v buf base inputs (hd.le.trans (Nat.lt_two_pow_self.le)) row stop path pc frame

end PairSimulation.LeafRouteFork

end VPVNP
end Computability
end OAI
