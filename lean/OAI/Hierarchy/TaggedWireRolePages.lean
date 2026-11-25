import OAI.Hierarchy.TaggedWireRolePageCore

namespace OAI
/-! # A single native memory image for consecutive public role tables -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleROM
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM
open scoped Classical
variable {w : ℕ}

structure Page where
  rows : ℕ
  word : Fin rows→ℕ

def words : List Page→ℕ
  | [] => 0
  | p::ps => p.rows+words ps

def publish (base : ℕ) : List Page→Memory w→Memory w
  | [], m => m
  | p::ps, m => init base p.word (publish (base+p.rows) ps m)

theorem init_frame (p : Page) (base a : ℕ) (m : Memory w)
    (outside : a < base ∨ base+p.rows≤a) : init base p.word m a=m a := by
  have miss : ¬(base≤a ∧ a<base+p.rows) := by omega
  simp [init,fillSegment,miss]

theorem mounted_at (before : List Page) (p : Page) (after : List Page) (base : ℕ) (m : Memory w) :
    Mounted (base+words before) p.word (publish base (before++p::after) m) := by
  induction before generalizing base with
  | nil => simpa only [words,Nat.add_zero,List.nil_append,publish] using
      mount base p.word (publish (base+p.rows) after m)
  | cons x xs ih =>
    intro i
    have prev := ih (base+x.rows) i
    change init base x.word (publish (base+x.rows) (xs++p::after) m)
      (base+(x.rows+words xs)+i.val)=_
    rw [init_frame x base _ _ (Or.inr (by omega))]
    simpa only [Nat.add_assoc] using prev

theorem publish_frame (ps : List Page) (base a : ℕ) (m : Memory w)
    (outside : a < base ∨ base+words ps≤a) : publish base ps m a=m a := by
  induction ps generalizing base with
  | nil => rfl
  | cons p ps ih =>
    change a < base ∨ base+(p.rows+words ps)≤a at outside
    change init base p.word (publish (base+p.rows) ps m) a=_
    rw [init_frame p base a _ (by omega)]
    exact ih (base+p.rows) (by omega)

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleROM
end

end OAI
