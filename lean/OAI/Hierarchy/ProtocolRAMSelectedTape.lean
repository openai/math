import OAI.Hierarchy.ProbeRepairHistogramAccount
import Mathlib.Data.Finset.Sort

namespace OAI
/-! # The occurrence index of the compact selected row tape -/

namespace Hierarchy.ProtocolRAM.SelectedRows
open AdaptiveProbe AdaptiveProbe.OuterBank
open scoped BigOperators Classical
noncomputable section
variable {r n : ℕ} {I X : Type*} [Fintype I]

/-- Stable row order in the physical failure-mask tape. -/
def row (selected : Finset (Fin r)) : Fin selected.card ↪ Fin r :=
  ((selected.orderIsoOfFin rfl).toEquiv.toEmbedding).trans (Function.Embedding.subtype _)

theorem row_mem (selected : Finset (Fin r)) (x : Fin selected.card) : row selected x∈selected :=
  ((selected.orderIsoOfFin rfl) x).property

theorem covers_row (selected : Finset (Fin r)) (x : Fin r) (active : x∈selected) :
    ∃ j, row selected j=x := by
  obtain ⟨j,hit⟩ := (selected.orderIsoOfFin rfl).surjective ⟨x,active⟩
  exact ⟨j,congrArg Subtype.val hit⟩

/-- Each selected row retains its native occurrence slot for every local port. -/
def port (selected : Finset (Fin r)) (width : Fin r→ℕ) (enum : (Σ v,Fin (width v)) ≃ Fin n) :
    (Σ j, Fin (width (row selected j))) ↪ Fin n :=
  ((row selected).sigmaMap (fun _=>Function.Embedding.refl _)).trans enum.toEmbedding

theorem off_port (selected : Finset (Fin r)) (width : Fin r→ℕ) (enum : (Σ v,Fin (width v)) ≃ Fin n)
    (e : Fin n) (away : ∀ a,port selected width enum a≠e) : (enum.symm e).1 ∉ selected := by
  obtain ⟨⟨j,k⟩,rfl⟩ := enum.surjective e
  simp only [Equiv.symm_apply_apply]
  intro live
  obtain ⟨i,rfl⟩ := covers_row selected j live
  exact away ⟨i,k⟩ rfl

theorem totals {T : Type*} [AddCommMonoid T] (selected : Finset (Fin r)) (price : Fin r→T)
    (inactive : ∀ j,j∉selected → price j=0) : ∑ j,price (row selected j)=∑ j,price j := by
  classical
  let f := row selected
  have eq : (∑ j∈Finset.univ.map f,price j) = ∑ j,price j := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ away
    apply inactive
    intro use
    obtain ⟨i,rfl⟩ := covers_row selected j use
    exact away (Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  simpa [f] using eq

/-- The widths and weights below still read every occurrence in the chronology.
The compacted families used by `FailedRows` keep exactly the live ones. -/
structure Tape (r n : ℕ) (I : Type*) where
  selected : Finset (Fin r)
  ports : Fin r→ℕ
  enum : (Σ j,Fin (ports j)) ≃ Fin n
  kind : Fin n→Option I
  put : Fin n→ℕ
  take : Fin n→ℕ
  weight : Fin n→ℝ
  broadcast : Fin r→ℝ
  dead : ∀ e, (enum.symm e).1∉selected → put e=0 ∧ take e=0
  quiet : ∀ j, j∉selected → broadcast j=0

def Tape.use (T : Tape r n I) := port T.selected T.ports T.enum

omit [Fintype I] in
theorem Tape.off (T : Tape r n I) {e : Fin n} (away : ∀a,T.use a≠e) :
    T.put e=0 ∧ T.take e=0 := T.dead e (off_port _ _ _ _ away)

omit [Fintype I] in
theorem Tape.delta (T : Tape r n I) (w : ℕ) (i : I) :
    stockChange (fun e=>T.kind (T.use e)) (netUnits w (fun e=>T.put (T.use e)) (fun e=>T.take (T.use e))) i =
    stockChange T.kind (netUnits w T.put T.take) i := by
  classical
  let val := fun j => if T.kind j=some i then netUnits w T.put T.take j else 0
  have eq : (∑j∈Finset.univ.map T.use,val j)=∑ j,val j := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ away
    have dead := T.off (e:=j) (fun a same=>away (Finset.mem_map.mpr ⟨a,Finset.mem_univ _,same⟩))
    simp [val,netUnits,dead.1,dead.2]
  simpa [val,stockChange,netUnits] using eq

end
end Hierarchy.ProtocolRAM.SelectedRows

end OAI
