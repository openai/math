import OAI.Computability.VPVNP.CompressorBlockInitialPackets

/-!
# Planner reads for the initial and substep header visits

The first-header formula reads the row count. Level offsets read the pitch.
Only the cursor planner loads additional words, namely its six scalar inputs
in the permanent first-level frame. These facts apply to each reference
memory at which the corresponding visit is prepared.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.HeaderOperands

open BurstRAM PhaseRecipe BlockPlanner BlockHeaderRun DescriptorSpace
open scoped Fin.CommRing
open private fit_fields address_val from OAI.Computability.VPVNP.CompressorBlockHeaderRun

variable {w : ℕ} (D : ℕ → Prop) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)

/-- The start, stop, and parameter expressions of a visit read only addresses allowed by the
specified region. -/
structure Supported (v : Visit) : Prop where
  initial : v.initial.ReadsFrom D pub s m
  stop : v.stop.ReadsFrom D pub s m
  params : ∀ j, (v.params j).ReadsFrom D pub s m

private theorem first (rows : D (pub 3).val) : BlockHeaderPlan.firstHeader.ReadsFrom D pub s m :=
  ⟨trivial,⟨⟨⟨trivial,trivial⟩,trivial⟩,trivial,rows⟩⟩

private theorem atLevel (pitch : D (pub 1-1).val) (i : ℕ) : (LevelFields.atLevel i).ReadsFrom D pub s m :=
  ⟨trivial,trivial,⟨trivial,trivial⟩,pitch⟩

private theorem formula {g : ℕ} (r : FormulaRow g) (src dest : Expr) (hs : src.ReadsFrom D pub s m)
    (hd : dest.ReadsFrom D pub s m) : Supported D pub s m (BlockHeaderPlan.formula r src dest) := by
  refine ⟨hs,⟨hs,trivial⟩,?_⟩
  intro i
  fin_cases i <;> first | exact hd | trivial

private theorem heads (F : Shape) (dest : Expr) (hd : dest.ReadsFrom D pub s m)
    (rows : D (pub 3).val) : Supported D pub s m (BlockHeaderPlan.heads F dest) := by
  refine ⟨trivial,trivial,?_⟩
  intro i
  fin_cases i <;> first | exact hd | exact first D pub s m rows | trivial

private theorem cursor (L : Layout) (nonempty : 0 < L.levels) (fields : 14 ≤ L.shape.scalarFields)
    (fit : endAddress L < 2^w) (rows : D (pub 3).val) (data : ∀ x, levelStart L 0 ≤ x → D x)
    (hFirst : BlockHeaderPlan.firstHeader.eval pub s m = header w L 0) :
    Supported D pub s m (BlockPlanner.cursor BlockHeaderPlan.persistentFrame) := by
  let frame := BlockHeaderPlan.persistentFrame
  let read := fun i : ℕ ↦ Expr.load (frame.add (.lit i))
  have hf : frame.eval pub s m = header w L 0+6 := by
    change BlockHeaderPlan.firstHeader.eval pub s m + ((6 : ℕ) : Word w) = _
    rw [hFirst,Nat.cast_ofNat]
  have hdr : frame.ReadsFrom D pub s m := ⟨first D pub s m rows,trivial⟩
  have ok (i : ℕ) (hi : i < 8) : (read i).ReadsFrom D pub s m := by
    refine ⟨⟨hdr,trivial⟩,?_⟩
    change D (frame.eval pub s m+(i : Word w)).val
    rw [hf,show header w L 0+6+(i : Word w) = header w L 0+((6+i : ℕ) : Word w) by simp [add_assoc]]
    have bound := fit_fields L ⟨0,nonempty⟩ fit
    change levelStart L 0+L.shape.scalarFields < 2^w at bound
    rw [address_val L 0 _ (by omega)]
    exact data _ (Nat.le_add_right ..)
  let cnt := (((read 3).mul (read 4)).mul (read 5)).mul (read 2)
  have hc : cnt.ReadsFrom D pub s m := ⟨⟨⟨ok 3 (by decide),ok 4 (by decide)⟩,ok 5 (by decide)⟩,ok 2 (by decide)⟩
  refine ⟨trivial,hc,?_⟩
  change ∀ j : Fin (5+6), ((Fin.append (fun j : Fin 5 ↦ read (j.val+2))
      (fun c : Fin 6 ↦ (read 7).add ((Expr.lit c.val).mul cnt))) j).ReadsFrom D pub s m
  apply Fin.addCases
  · intro i
    rw [Fin.append_left]
    exact ok _ (by have := i.isLt; omega)
  · intro i
    rw [Fin.append_right]
    exact ⟨ok 7 (by decide),trivial,hc⟩

/-- Covers the concrete four visits in their true order, including the
level-zero role word at offset 27. -/
theorem initial (L : Layout) (a : ℕ) (nonempty : 0 < L.levels) (fields : 14 ≤ L.shape.scalarFields)
    (fit : endAddress L < 2^w) (rows : D (pub 3).val) (pitch : D (pub 1-1).val)
    (data : ∀ x, levelStart L 0 ≤ x → D x) (hFirst : BlockHeaderPlan.firstHeader.eval pub s m = header w L 0)
    (v : Visit) (hv : v ∈ BlockInitialPackets.order L a) : Supported D pub s m v := by
  rcases List.mem_cons.mp hv with rfl|hv
  · exact formula D pub s m _ _ _ ⟨first D pub s m rows,trivial⟩ (first D pub s m rows)
  rcases List.mem_cons.mp hv with rfl|hv
  · exact heads D pub s m _ _ (first D pub s m rows) rows
  rcases List.mem_cons.mp hv with rfl|hv
  · exact cursor D pub s m L nonempty fields fit rows data hFirst
  obtain rfl := List.mem_singleton.mp hv
  refine ⟨trivial,trivial,?_⟩
  intro i
  fin_cases i
  · exact ⟨atLevel D pub s m pitch 0,trivial⟩
  · trivial

/-- At any substep the two scalar publishers need only the runtime pitch.
The pointer publisher also reads the row count to locate the first level. -/
theorem substep (F : Shape) {a b : ℕ} (step : ℕ) (p : Scalars.Pass a b) (rows : D (pub 3).val)
    (pitch : D (pub 1-1).val) (v : Visit) (hv : v ∈ BlockHeaderPlan.substep F step p) :
    Supported D pub s m v := by
  rcases List.mem_cons.mp hv with rfl|hv
  · exact formula D pub s m _ _ _ (atLevel D pub s m pitch step) (atLevel D pub s m pitch step)
  rcases List.mem_cons.mp hv with rfl|hv
  · exact formula D pub s m _ _ _ (atLevel D pub s m pitch step) (atLevel D pub s m pitch (step+1))
  obtain rfl := List.mem_singleton.mp hv
  exact heads D pub s m _ _ (atLevel D pub s m pitch (step+1)) rows

end CompressorRecords.HeaderOperands

end VPVNP
end Computability
end OAI
