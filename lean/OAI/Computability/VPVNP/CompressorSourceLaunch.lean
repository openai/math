import OAI.Computability.VPVNP.CompressorSourceOnline
import OAI.Computability.VPVNP.CompressorScriptSnapshot

/-! # The physical launch certificate for the current script phase -/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SourceOnline

open BurstRAM Schedule BlockPlanner DescriptorSpace

variable {w : ℕ} (A : Script) (base : Word w)
local notation "g₀" => arity A.catalog
local notation "P₀" => Workspace.ports g₀ base

/-- Actual stage operands depend on the current memory. Choice strings and
the worker's private clock are supplied by the source scan. -/
def evaluated (m : Memory w) (j : Fin A.size) (fuel : ℕ) (bits : List (List Bool)) : Visit A w :=
  ⟨j,fuel,A.operand base m j (A.visit j).initial,A.operand base m j (A.visit j).stop,
    fun i => A.operand base m j ((A.visit j).params i),bits⟩

theorem evaluated_launch (L : Layout) (hg : g₀=L.shape.arity) (hb : base.val=L.base) (fit : levelStart L 0 < 2^w)
    (m : Memory w) (j : Fin A.size) (fuel : ℕ) (bits : List (List Bool))
    (room : (m (P₀).ordinal.val).val < directoryRows L) (active : m (P₀).ordinal.val < m (P₀).rows.val) :
    (evaluated A base m j fuel bits).Launch P₀ m := by
  obtain ⟨ord,rows,tag,start,stop,params,ready,next,same⟩ := A.snapshot L base hg hb fit m j room active
  exact ⟨tag,ord,rows,start,stop,params,ready,next,same⟩

/-- Public field evaluation is all that a typed source stage needs to supply
to identify its computed runtime launch. -/
theorem launch_of_evaluation (L : Layout) (hg : g₀=L.shape.arity) (hb : base.val=L.base) (fit : levelStart L 0 < 2^w)
    (m : Memory w) (v : Visit A w) (room : (m (P₀).ordinal.val).val < directoryRows L)
    (active : m (P₀).ordinal.val < m (P₀).rows.val)
    (st : A.operand base m v.phase (A.visit v.phase).initial = v.start)
    (stop : A.operand base m v.phase (A.visit v.phase).stop = v.stop)
    (args : ∀ i, A.operand base m v.phase ((A.visit v.phase).params i) = v.params i) : v.Launch P₀ m := by
  have eq : evaluated A base m v.phase v.fuel v.choices = v := by
    cases v
    simp_all [evaluated]
    exact funext args
  exact eq ▸ evaluated_launch A base L hg hb fit m v.phase v.fuel v.choices room active

/-- A valid row at a script visit has the worker tag selected by that visit.
This equality is recovered from the prepared memory even when the source scan
is empty. -/
theorem worker_eq_phase (L : Layout) (hg : g₀=L.shape.arity) (hb : base.val=L.base) (fit : levelStart L 0 < 2^w)
    (m : Memory w) {cap : ℕ} (s : Online.Run.Step A.size A.size w)
    (valid : s.Valid A.plan P₀ cap m) (room : (m (P₀).ordinal.val).val < directoryRows L)
    (tags : A.size+1 ≤ 2^w) : s.row.worker=s.phase := by
  have ready : Ready A.catalog s.row.worker P₀ (Directory.words A.catalog P₀ s.row.worker s.row.input)
      (Directory.bound A.catalog P₀ s.row.input) (s.row.dataMemory A.catalog P₀) := by
    have h := valid.source.frame
    cases hlist : s.row.reports <;> rw [hlist] at h <;> exact h.1
  have a := ready.1
  change (Directory.prepared A.catalog P₀ s.row.input) (P₀).tag.val = _ at a
  rw [valid.input] at a
  have b := (evaluated_launch A base L hg hb fit m s.phase s.row.fuel s.row.choices room valid.active).ready.1
  have eq : LiveStageLink.tagWord w s.row.worker.succ = LiveStageLink.tagWord w s.phase.succ := a.symm.trans b
  have val := congrArg Fin.val eq
  change (s.row.worker.val+1)%2^w = (s.phase.val+1)%2^w at val
  have hw : s.row.worker.val+1 < 2^w := s.row.worker.succ.isLt.trans_le tags
  have hj : s.phase.val+1 < 2^w := s.phase.succ.isLt.trans_le tags
  rw [Nat.mod_eq_of_lt hw,Nat.mod_eq_of_lt hj] at val
  exact Fin.ext (by omega)

end CompressorRecords.SourceOnline

end VPVNP
end Computability
end OAI
