import OAI.Hierarchy.DescentDatePortArchiveDensity
import OAI.Hierarchy.DescentDatedArchiveWidths

namespace OAI
/-! # Numerical room for both source buses, including the last short group -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler DescentInitialHost DescentDatedAddressBook DescentPrimitivePalette
noncomputable section

structure ArchivePitchRoom (p : DatePorts) (groups h argUnit roleUnit : ℕ) : Prop extends
    p.ArchiveDensity groups h argUnit roleUnit where
  operandPos : 0<p.operandLanes
  rolePos : 0<p.roleLanes
  operandHalf : p.operandLanes≤h/2
  roleHalf : p.roleLanes≤h/2

private theorem positive_pitch {g h m u : ℕ} (gPos : 0<g) (hPos : 0<h) (room : g≤ m ∨ h≤ m*u) :
    0< m:=by
  by_contra! bad
  have eqn:m=0:=by omega
  rcases room with all | fill
  · omega
  · simp only [eqn,Nat.zero_mul] at fill;omega

/-- Positive dimensions follow from the actual dated formats, even for a single
padded source node. Word room then bounds both independently chosen pitches. -/
theorem ArchiveDensity.pitch_room {F : Type} [Field F] {G : PoweredGadget F} {S : AtomSchedule}
    {op : RotorSpec} {p : DatePorts} {k last grain drift degree h age g a b : ℕ}
    (density : p.ArchiveDensity g h a b) (words : ArchiveWidths G S op p k last grain drift degree h age)
    (hPos : 0<h) (gPos : 0<g) : p.ArchivePitchRoom g h a b:=by
  have nodes : 0<p.nodes:=by
    rw [words.nodes];split
    · decide
    · exact Nat.pow_pos (Nat.two_pow_pos _)
  have arg : 0<p.operandBits:=by
    rw [words.digits];exact (Nat.succ_pos _).trans_le (Nat.le_max_right ..)
  have role : 0<printedBits G (S.firstWidth G.b grain) (S.grainAt G.b grain 0) op:=by
    apply Nat.clog_pos (by decide : 1<2)
    unfold colors
    omega
  exact ⟨density,positive_pitch gPos hPos density.operands,positive_pitch gPos hPos density.roles,
    (Nat.le_mul_of_pos_left p.operandLanes (Nat.mul_pos arg nodes)).trans words.operands,
    (Nat.le_mul_of_pos_left p.roleLanes (Nat.mul_pos role nodes)).trans words.roles⟩

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
