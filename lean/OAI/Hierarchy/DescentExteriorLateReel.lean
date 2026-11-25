import OAI.Hierarchy.DescentExteriorPrime

namespace OAI
/-! # Replay the saved public matrices a second time above the attained preflight -/
namespace Hierarchy.DescentExteriorMatrixUpdate
open Computability.BorderVNP.Crossing DescentCompiler DescentGL DescentColonies DescentExterior
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section

/-- Both flights consume the same chronological rotation and immutable update
table. The second flight stores its running matrix in the later scratch band. -/
def Reel.late (P : Reel) (base : ℕ) : Reel :=
  {P with old:=fun t=>base+t,output:=fun t=>base+(t+1)}

theorem Reel.late_room {w d age f origin base next} (P : Reel) (old : P.Room w d age f origin)
    (earlier : origin≤base) (gap : base+age+1≤next) (bank : next<2^w) :
    (P.late base).Room w d age base next := by
  refine ⟨by simp [late],?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp only [late,Nat.add_zero];omega
  · simp only [late,Nat.add_zero];omega
  · intro t ht;dsimp [late];omega
  · intro t ht
    exact (old.rotation t ht).trans_le (((old.high t ht).le.trans earlier).trans (Nat.le_add_right ..))
  · intro t ht
    exact (old.table t ht).trans (((old.high t ht).le.trans earlier).trans (Nat.le_add_right ..))
  · intro t ht;dsimp [late];omega
  · intro t ht;exact Nat.le_add_right ..
  · intro t ht;dsimp [late];omega
  · intro t _;rfl
  · dsimp [late];omega

theorem Reel.Slot.late {w h d : ℕ} {P : Reel} {i f start : ℕ} {ext : Layout h→Layout d}
    {rot : Layout h} {m : Memory w} (old : P.Slot i f ext rot m) (later : f≤ start)
    (space : start+(i+1)+1<2^w) : (P.late start).Slot i start ext rot m :=
  ⟨old.size,by dsimp [Reel.late];omega,space,old.rotation_low.trans_le later,old.table_low.trans later,
    old.saved,old.printed⟩

end
end Hierarchy.DescentExteriorMatrixUpdate

namespace Hierarchy.DescentSixParty.Chronology
open Computability.BorderVNP.Crossing DescentCompiler DescentGL DescentColonies DescentExterior DescentKernelHistory
open PinCohorts DescentExteriorMatrixUpdate
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {d k tail wire hist : ℕ} {bits:P→ℕ} {G:PoweredGadget F}
    {S:AtomSchedule} {q ε:ℝ} {I W:MarkedWorld F d P bits} {z₀ D₀ i z D:ℕ}
    {initial:Reached I G q ε S k 0 z₀ D₀ wire hist} {current:Reached W G q ε S k i z D wire hist}
    (path : Path initial current) (plan : Reel) (fence : ℕ) {bw : ℕ}

omit [Fintype P] in
theorem Path.saved_late {m : Memory bw} (saved : path.savedRotations plan fence tail m)
    {base : ℕ} (later : fence≤base) (space : base+i+1<2^bw) :
    path.savedRotations (plan.late base) base tail m := by
  induction path with
  | here => trivial
  | ordinary prev ticket ih => exact ⟨ih saved.1 (by omega),saved.2.late later space⟩
  | reset prev b ih => exact ⟨ih saved.1 (by omega),saved.2.late later space⟩

end
end Hierarchy.DescentSixParty.Chronology

end OAI
