import OAI.Computability.BorderVNP.PackedHistoryGeometryPaths
import OAI.Computability.BorderVNP.FiniteDiagonalUnitTraceProduct

/-! # Ordinary events and field weight of the native history prefix

The pin chooser consumes one private bit at a branch. Its two arms and the public
history interpreter use ordinary memory accesses. This controls individual events
as well as the accumulated time and applies to every return of the prefix.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM RoutingISA TeamContraction TeamRAM

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

private theorem ordinary_choices {S : Type*} (i : Instr w S) {p bs vs z sign}
    (action : i.action = some (.ordinary p)) (step : i.advance bs vs = some (z,sign)) :
    bs.length ≤ 1 := by
  rcases bs with _ | ⟨b,_ | ⟨b',bs⟩⟩
  · exact Nat.zero_le _
  · exact le_rfl
  · cases i <;> first | contradiction | simp_all [Instr.action]

private theorem positive_events {c : Code} {s m es z mz} (r : Runs pub mac c s m es z mz)
    (positive : c.positive = true) :
    ∀ e ∈ es, (∃ probe, e.action = .ordinary probe) ∧ e.choices.length ≤ 1 := by
  induction r with
  | @atom c s m a t sign bits hc ha hs =>
    have det : c.deterministic = true := by
      cases c <;> first | rfl | contradiction
    let atom := Runs.atom hc ha hs
    intro e he
    obtain rfl := List.mem_singleton.mp he
    obtain ⟨probe,hp⟩ := FiniteDiagonal.ordinary_of_deterministic atom det _ (List.mem_singleton_self _)
    change a = .ordinary probe at hp
    exact ⟨⟨probe,hp⟩,ordinary_choices _ (ha.trans (congrArg some hp)) hs⟩
  | seq _ _ ih ih' =>
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp positive
    exact fun e he => (List.mem_append.mp he).elim (ih ha e) (ih' hb e)
  | ifEq _ ih | ifLt _ ih | choose _ _ ih =>
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp positive
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨⟨none,rfl⟩,by first | exact Nat.zero_le _ | exact le_rfl⟩
    · exact ih (by split <;> assumption) e he
  | whileDone =>
    intro e he
    obtain rfl := List.mem_singleton.mp he
    exact ⟨⟨none,rfl⟩,Nat.zero_le _⟩
  | whileStep _ _ _ ih ih' =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨⟨none,rfl⟩,Nat.zero_le _⟩
    · exact (List.mem_append.mp he).elim (ih positive e) (ih' positive e)

set_option maxRecDepth 4000 in
/-- Every returning pin and profile trace has ordinary one-tick positive events
and at most one private choice at each event. -/
theorem pinGeometry_trace {s m es z mz} (r : Runs pub mac pinGeometry s m es z mz) :
    traceCost es = es.length ∧ ∀ e ∈ es, (∃ probe, e.action = .ordinary probe) ∧
      e.action.extra = 0 ∧ e.choices.length ≤ 1 ∧ e.sign = .plus := by
  have good : pinGeometry.positive = true := by decide
  refine ⟨(DiagonalResidueRAM.plain_return pinGeometry (by decide) r).1,?_⟩
  intro e he
  obtain ⟨⟨pr,hp⟩,bit⟩ := positive_events r good e he
  exact ⟨⟨pr,hp⟩,by simp [hp,TeamTranscript.Action.extra],bit,r.positive good e he⟩

/-- The measured trace charge suffices for the native path's tick, burst and private
clock guards. -/
theorem pinGeometry_within {s m es z mz t} (r : Runs pub mac pinGeometry s m es z mz)
    (cost : traceCost es ≤ t) : Within t 0 1 es :=
  ⟨cost,fun e he => ((pinGeometry_trace r).2 e he).2.1.le,
    fun e he => ((pinGeometry_trace r).2 e he).2.2.1⟩

/-- At the actual processor entry the profile prefix has field weight one, for every
field and every library of private return functions. -/
theorem pinGeometry_pathProduct {Q Γ : Type} {F : Type*} [Field F] {m g : ℕ}
    (lib : Fin 8 → TeamSite.Macro Q Γ m g) (ret : FieldProcessor.Returns Q Γ F m 8) (fuel : ℕ)
    {s mem es z mz} (r : Runs pub (TeamSiteEvents.macros lib fuel) pinGeometry s mem es z mz) :
    FieldProcessor.pathProduct pinGeometry.program pub lib ret fuel ⟨0,s⟩ es = 1 :=
  FiniteDiagonal.pathProduct_ordinary_positive _ _ _ _ _ _ _ (execute_spec r.execute).1
    (fun e he => ((pinGeometry_trace r).2 e he).1)
    (fun e he => ((pinGeometry_trace r).2 e he).2.2.2)

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
