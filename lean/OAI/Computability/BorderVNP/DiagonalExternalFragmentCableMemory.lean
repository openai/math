import OAI.Computability.BorderVNP.DiagonalExternalFragmentCables
import OAI.Computability.BorderVNP.CubeHostScatterProgram

/-! # The cable geometry image after an actual host-scatter run

The occupied and vacant cable rows are both read-only metadata of the
host program. Their preservation follows already from separation of each
write from its inputs, including when distinct output intervals overlap.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.Fragments

open BorderVNP.Cube RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

variable {l : HostScatter.Layout} {before after : ℕ → ℕ}

/-- The physical interval occupied by all cable triples and both endpoint
offsets is in the host's immutable input. -/
theorem cableRectangle_input (relative : l.relative = l.cables+3*l.count) {a : ℕ}
    (lo : l.cables ≤ a) (hi : a < l.cables+5*l.count) : l.Input before a := by
  by_cases triple : a < l.cables+3*l.count
  · let i := (a-l.cables)/3
    have bound : i < l.count := by dsimp [i]; omega
    have pos : a = l.cables+3*i ∨ a = l.cables+3*i+1 ∨ a = l.cables+3*i+2 := by
      dsimp [i]; omega
    refine ⟨i,bound,false,Or.inl ?_⟩
    rcases pos with h | h | h <;> simp [HostScatter.Layout.rowReads,h]
  · let i := (a-l.relative)/2
    have bound : i < l.count := by dsimp [i]; omega
    have pos : a = l.relative+2*i ∨ a = l.relative+2*i+1 := by dsimp [i]; omega
    rcases pos with h | h
    · exact ⟨i,bound,false,Or.inl (by simp [HostScatter.Layout.rowReads,h])⟩
    · exact ⟨i,bound,true,Or.inl (by simp [HostScatter.Layout.rowReads,h])⟩

/-- A frozen post-run image reads every word of the cable geometry from
the original geometry block. -/
theorem cableRectangle_frozen (frozen : l.Frozen before after)
    (relative : l.relative = l.cables+3*l.count) {a : ℕ}
    (lo : l.cables ≤ a) (hi : a < l.cables+5*l.count) : after a = before a :=
  frozen a (cableRectangle_input relative lo hi)

private theorem prefix_frozen {w : ℕ} (fit : l.Fits w before) {i : ℕ} (hi : i ≤ l.count) :
    l.Frozen before (l.prefix before i) := by
  induction i with
  | zero => exact fun _ _ => rfl
  | succ i ih =>
    have h := ih (Nat.le_of_succ_le hi)
    exact (h.copyEnd fit hi false).copyEnd fit hi true

/-- Every concrete native host-scatter execution preserves every physical
geometry word, for all scanned sparse IDs including holes. -/
theorem cableRectangle_run {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (fit : l.Fits w (readings m))
    (hf : readings pub 0 = l.frame) (frame : l.Frame (readings m))
    (frameFit : l.frame+94 < 2^w) (headerFit : readings m (l.frame+63)+8 < 2^w)
    {es : List (TeamRAM.Event w)} {t : Bank w} {mt : Memory w}
    (run : Runs pub macros HostScatter.program s m es t mt)
    (relative : l.relative = l.cables+3*l.count) {a : ℕ}
    (lo : l.cables ≤ a) (hi : a < l.cables+5*l.count) : readings mt a = readings m a := by
  have exec := HostScatter.program_all_runs pub macros l s m fit hf frame frameFit headerFit run
  rw [exec.2.2.2]
  exact cableRectangle_frozen (prefix_frozen fit (le_refl _)) relative lo hi

end Diagonal.ExternalSew.Fragments

end BorderVNP
end Computability
end OAI
