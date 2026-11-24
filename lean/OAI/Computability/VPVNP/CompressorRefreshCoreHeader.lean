import OAI.Computability.VPVNP.CompressorRefreshTraversalHeaders
import OAI.Computability.VPVNP.CompressorRefreshStageSupport
import OAI.Computability.VPVNP.CompressorGreedyPlannerFootprint

/-!
# Current header readback for the native refresh

The scalar publisher supplies the old vertex and residual lane counts. The
pointer publisher supplies the old incidence columns and the scratch origin.
These cells precede the first refresh array, so all stages of the native
refresh continue to read them at their original values.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.RefreshCore

open BurstRAM Compression PhaseRecipe DescriptorSpace LevelFields PortRefresh NewSlots LevelRecipe
open scoped Fin.CommRing

variable {w : ℕ}

/-- Specifies the vertex count, residual-lane count, six incidence column heads and scratch
start in a level header that fits in memory. -/
structure Header (vertices g head start : ℕ) (old : IncidenceDirectory w)
    (m : Memory w) : Prop where
  room : head + 60 < 2 ^ w
  vertices_eq : m (head + 0) = word vertices
  residual : m (head + 3) = word (2 ^ g)
  incidence : ∀ c : Fin 6, m (head + 54 + c.val) = old.column c
  scratch : m (head + 60) = word start

theorem Header.keep {V g head start : ℕ} {old : IncidenceDirectory w} {m m' : Memory w}
    (h : Header V g head start old m) (keep : ∀ n ≤ 60, m' (head + n) = m (head + n)) :
    Header V g head start old m' := by
  refine ⟨h.room,(keep 0 (by decide)).trans h.vertices_eq,(keep 3 (by decide)).trans h.residual,
    fun c ↦ ?_,(keep 60 le_rfl).trans h.scratch⟩
  rw [Nat.add_assoc,keep _ (by have := c.isLt; omega),← Nat.add_assoc]
  exact h.incidence c

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
variable {R : Type*} [CommRing R] {f : B.Entry → R} {hf : B.IsSolution f}

/-- The live scalar and pointer publications produce the exact header used
by the refresh, including the packed old - slot incidence table. -/
theorem Header.ofPublished {L : Layout} {i dH : ℕ} {m : Memory w} {v : SelectedLevel B f hf}
    (h : Published L i v dH m) (bank : TraversalHeaders.HeadBank L i v.oldSlots m)
    (fields : L.shape.scalarFields = 54) (tables : 0 < L.shape.tables)
    (room : levelStart L i + 60 < 2 ^ w) :
    Header (Fintype.card v.input.Base) v.outputLanes (levelStart L i) (arrayBase L i)
      (packedIncidence L w i v.oldSlots) m := by
  refine ⟨room,h.vertices,h.residual,fun c ↦ ?_,?_⟩
  · rw [packed_column]
    simpa only [incidenceHead,fields] using bank.incidence c
  · simpa [tableHead,tableBase,fields,Nat.add_assoc] using bank.tables ⟨0,tables⟩

variable {L : Layout} {first step start g : ℕ} {C : Context w}
variable {s : LevelRecipe.Shape} {X : State s.a (s.a + g)} {old : IncidenceDirectory w}
variable {F : DescriptorSpace.Shape} (field : F.scalarFields = 54) (j : Fin F.tables)
    (zero : j.val = 0)

include field zero in
theorem Header.describes (e : Entry L first C.pub C.state C.memory)
    (h : Header (Fintype.card X.Base) g (levelStart L (first + step)) start old C.memory) :
    Describes (s := s) (RefreshBlockPlan.input F step j) C X start old := by
  let head := levelStart L (first + step)
  have read (n : ℕ) (hn : n ≤ 60) : C.eval (scalar step n) = C.memory (head + n) :=
    eval_scalar e step n ((Nat.add_le_add_left hn _).trans_lt h.room)
  have arr : C.eval (table F step j) = C.memory (head + 60) := by
    simpa only [table,field,zero,Nat.reduceAdd,Nat.add_zero] using read 60 le_rfl
  have inc (c : Fin 6) : C.eval (LevelFields.incidence F step c) = old.column c := by
    unfold LevelFields.incidence
    rw [field,read _ (by have := c.isLt; omega),← Nat.add_assoc]
    exact h.incidence c
  exact ⟨arr.trans h.scratch,(read 0 (by decide)).trans h.vertices_eq,
    (read 3 (by decide)).trans h.residual,inc 0,inc 2,inc 5⟩

include field zero in
/-- Operand support of the six physical level-header loads. -/
theorem Header.reads (e : Entry L first C.pub C.state C.memory) {D : ℕ → Prop}
    {V lanes : ℕ} (h : Header V lanes (levelStart L (first + step)) start old C.memory)
    (pitch : D (C.pub 1 - 1).val) (region : ∀ n ≤ 60, D (levelStart L (first + step) + n)) :
    InputReads D C.pub C.state C.memory (RefreshBlockPlan.input F step j) := by
  have read (n : ℕ) (hn : n ≤ 60) : (scalar step n).ReadsFrom D C.pub C.state C.memory :=
    GreedyVisit.scalar_support D L first step n e pitch (region n hn)
      ((Nat.add_le_add_left hn _).trans_lt h.room)
  refine ⟨?_,read 0 (by decide),read 3 (by decide),?_,?_,?_⟩
  all_goals
    simp only [RefreshBlockPlan.input,table,LevelFields.incidence,field,zero,Fin.val_zero,
      Nat.reduceAdd,Nat.add_zero]
    exact read _ (by decide)

end CompressorRecords.RefreshCore

end VPVNP
end Computability
end OAI
