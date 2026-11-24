import OAI.Computability.VPVNP.CompressorGreedyPlannerFootprint

/-! # Evaluating each greedy packet in its own source memory

The old level scalars, incidence heads and table pointer are below the
greedy workspace. The six native workers preserve that prefix. Their
dynamic launch expressions consequently read the same inputs at each
stage, even after earlier workers have written the two directories.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.GreedyVisit

open BurstRAM Compression DescriptorSpace PhaseRecipe SourceTransport
open scoped Fin.CommRing

variable {w a g z : ℕ} {X : GreedyArena.ShrinkingState a g} {T : IncidenceDirectory w}
  {m : Memory w}

private theorem transfer {D : ℕ → Prop} {pub : Fin 5 → Word w} {s : Word w} {input : Memory w}
    (e : Expr) (same : ∀ x < z, input x = m x)
    (low : e.ReadsFrom (· < z) pub s m) (reads : e.ReadsFrom D pub s m) :
    e.eval pub s input = e.eval pub s m ∧ e.ReadsFrom D pub s input := by
  induction e with
  | lit | publicWord | state => exact ⟨rfl,trivial⟩
  | load e ih =>
    obtain ⟨addr,hr⟩ := ih low.1 reads.1
    exact ⟨(congrArg (fun x : Word w => input x.val) addr).trans (same _ low.2),hr,addr ▸ reads.2⟩
  | binary op e f he hf =>
    obtain ⟨er,es⟩ := he low.1 reads.1
    obtain ⟨fr,fs⟩ := hf low.2 reads.2
    exact ⟨congrArg₂ op.eval er fr,es,fs⟩

/-- Uniform fuel bound obtained by summing the fuel budgets of all greedy stages. -/
def maxFuel (a : ℕ) := (stages.map (fuel a)).sum

theorem fuel_le (j : Stage) : fuel a j ≤ maxFuel a := by
  apply List.single_le_sum
  · exact fun _ _ => Nat.zero_le _
  exact List.mem_map.mpr ⟨j,by cases j <;> decide,rfl⟩

/-- Turn the six actual native kernels into header-relative source packets.
The only memory facts used about their traces are the two access bounds. -/
theorem packet_walk (r : GreedyArena.Run X T z m) (L : Layout) (shape : Shape) (step : ℕ)
    (origin : Expr) (pub : Fin 5 → Word w) (s : Word w) (D : ℕ → Prop)
    (initial : GreedyLevelPlan.Reads shape step a origin pub s m (Fintype.card X.Base) g z T)
    (low : ∀ j, HeaderOperands.Supported (· < z) pub s m (visit shape step a origin j))
    (supported : ∀ j, HeaderOperands.Supported D pub s m (visit shape step a origin j))
    (floor : levelStart L 0 ≤ z)
    (reads : ∀ j, Reads (levelStart L 0 ≤ ·) (eventLog (packetReports r j)))
    (writes : ∀ j, Writes (z ≤ ·) (eventLog (packetReports r j))) (bound : ℕ) (budget : maxFuel a ≤ bound) :
    SourceWalk (fun v input rs => ∃ f bits, f ≤ bound ∧ HeaderPacket.Run L pub s v input rs f bits ∧
      HeaderOperands.Supported D pub s input v)
      (GreedyLevelPlan.visits shape step a origin) m r.reports := by
  let P := fun j input rs => input = packetInput r j ∧ rs = packetReports r j ∧ Source r shape step origin j input rs
  have lift {js : List Stage} {input : Memory w} {rs : List (Report w)} (walk : SourceWalk P js input rs)
      (same : ∀ x < z, input x=m x) :
      SourceWalk (fun v input rs => ∃ f bits, f ≤ bound ∧ HeaderPacket.Run L pub s v input rs f bits ∧
        HeaderOperands.Supported D pub s input v)
        (js.map (visit shape step a origin)) input rs := by
    induction walk with
    | done => exact .done _
    | @next j js cur head tail stage _ ih =>
      obtain ⟨_,rfl,hsrc⟩ := stage
      obtain ⟨ha,hb,hc⟩ := values r initial j
      have hi := transfer _ same (low j).initial (supported j).initial
      have hs := transfer _ same (low j).stop (supported j).stop
      have hp k := transfer _ same ((low j).params k) ((supported j).params k)
      have hargs : (fun k => ((visit shape step a origin j).params k).eval pub s cur) =
          params r shape step origin j := (funext fun k => (hp k).1).trans hc
      have srun : HeaderPacket.Run L pub s (visit shape step a origin j) cur (packetReports r j) (fuel a j) (choices X j) := by
        refine ⟨fuel_pos _,?_,?_,reads j,fun x v hx => floor.trans (writes j x v hx)⟩
        · dsimp only
          rw [hargs,hi.1,ha]; exact hsrc.native
        · rw [hi.1,ha,hs.1,hb]; exact hsrc.progress
      exact .next ⟨_,_,(fuel_le j).trans budget,srun,⟨hi.2,hs.2,fun k => (hp k).2⟩⟩
        (ih (fun x hx => (after_outside cur (writes j) (Nat.not_le_of_lt hx)).trans (same x hx)))
  rw [← visits_eq]
  exact lift (indexed_walk r shape step origin) (fun _ _ => rfl)

end CompressorRecords.GreedyVisit

end VPVNP
end Computability
end OAI
