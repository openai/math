import OAI.Hierarchy.DescentExteriorReelPrograms

namespace OAI
/-! # The saved rotation and its product table at one physical date -/
namespace Hierarchy.DescentExteriorMatrixUpdate
open DescentGL DescentExterior DescentPackedColony.Phase.Arena
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Fin.CommRing
noncomputable section
structure Reel.Slot {w h d : ℕ} (P : Reel) (age fence : ℕ) (ext : Layout h→Layout d)
    (rot : Layout h) (m : Memory w) : Prop where
  size : P.localWidth age=h
  prior : P.old age < P.output age
  charged : P.output age+1 < 2^w
  rotation_low : P.rotation age < fence
  table_low : P.table age+pages d h ≤ fence
  saved : m (P.rotation age)=((matrixCode rot).val:Word w)
  printed : (tableSheet (P.table age) ext).Resident m

theorem Reel.Slot.move {w h d : ℕ} {P : Reel} {age fence : ℕ} {ext : Layout h→Layout d}
    {rot : Layout h} {m o : Memory w} (old : P.Slot age fence ext rot m)
    (low : ∀a,a < fence → o a=m a) : P.Slot age fence ext rot o := by
  refine {old with saved:=(low _ old.rotation_low).trans old.saved,printed:=?_}
  intro a start stop
  change a < P.table age+pages d h at stop
  exact (low a (stop.trans_le old.table_low)).trans (old.printed a start stop)

theorem Reel.Slot.raise {w h d : ℕ} {P : Reel} {age fence top : ℕ} {ext : Layout h→Layout d}
    {rot : Layout h} {m : Memory w} (old : P.Slot age fence ext rot m) (increase : fence ≤ top) :
    P.Slot age top ext rot m :=
  ⟨old.size,old.prior,old.charged,old.rotation_low.trans_le increase,old.table_low.trans increase,old.saved,old.printed⟩

theorem Reel.Slot.read {w h d : ℕ} {P : Reel} {age fence : ℕ} {ext : Layout h→Layout d}
    {rot : Layout h} {m : Memory w} (row : P.Slot age fence ext rot m)
    (high : ∀i≤age,fence ≤ P.output i) :
    ((P.cells d) age).Room w d h ∧
      ((P.cells d) age).Shelf (reached (P.cells d) m age) ext rot := by
  have kept : ∀a,a < fence → reached (P.cells d) m age a=m a:=by
    intro a low
    apply DescentExteriorShelf.reached_frame
    intro i hi
    change P.output i ≠ a
    have ge:=high i hi.le
    omega
  have after:=row.move kept
  change (cell _ _ _ _ _ (P.localWidth age)).Room _ _ _ ∧
    (cell _ _ _ _ _ (P.localWidth age)).Shelf _ _ _
  rw [row.size]
  exact ⟨cell_room _ _ _ _ _ _ _ row.prior (row.rotation_low.trans_le (high age le_rfl))
      (row.table_low.trans (high age le_rfl)) row.charged,
    shelf_of_rotate _ _ _ _ ext rot _ after.saved after.printed⟩


/-- Native publication of this date's product table appends the saved ordinal to the log.
The preserved low interval contains all prior date words and all input data. -/
theorem Reel.issueSlot {w h d : ℕ} (P : Reel) (age fence : ℕ) (ext : Layout h→Layout d)
    (m : Memory w) (size : P.localWidth age=h) (prior : P.old age < P.output age)
    (charge : P.output age+1 < 2^w) (before : P.rotation age < P.table age)
    (within : P.table age+pages d h ≤ fence) (fit : P.table age+pages d h < 2^w) :
    let I:=tableSheet (P.table age) ext
    I.program.Exec m (I.output m) (4+10*pages d h) ∧
    ProtocolRAM.CheapCode I.program ∧
    (∀rot : Layout h,m (P.rotation age)=((matrixCode rot).val:Word w)→P.Slot age fence ext rot (I.output m)) ∧
    ∀a,a < P.table age ∨ P.table age+pages d h ≤ a→I.output m a=m a := by
  intro I
  have len : I.length=pages d h:=by change P.table age+pages d h-P.table age=_;omega
  obtain ⟨write,resident,outer⟩:=I.issue m (by change P.table age+I.length < 2^w;omega)
  rw [len] at write
  refine ⟨write,I.hardware.1,?_,outer⟩
  intro rot chosen
  exact ⟨size,prior,charge,(by omega),within,(outer _ (.inl before)).trans chosen,resident⟩

end
end Hierarchy.DescentExteriorMatrixUpdate

end OAI
