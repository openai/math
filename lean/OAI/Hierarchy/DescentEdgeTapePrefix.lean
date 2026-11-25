import OAI.Hierarchy.ProtocolRAMEndpointPrefix
import OAI.Hierarchy.ProtocolRAMPortRanks

namespace OAI
/-! # Prefixing a sparse physical edge tape without renumbering its inputs -/

namespace Hierarchy.DescentEdgeTapePrefix
open ThreeFlat.RAM PhysicalProcedure
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAMPortRanks
open scoped Fin.CommRing BigOperators Classical
noncomputable section
variable {E : Type} [Fintype E] (repetitions rank : E→ℕ)
def before (j : ℕ) := ∑e,if rank e<j then repetitions e else 0
def row (j : ℕ) := ∑e,if rank e=j then repetitions e else 0

theorem before_zero : before repetitions rank 0=0 := by simp [before]

theorem before_succ (j : ℕ) : before repetitions rank (j+1)=before repetitions rank j+row repetitions rank j := by
  unfold before row
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases lt : rank e<j
  · simp [lt,lt.ne,lt.trans (Nat.lt_succ_self j)]
  by_cases eqn : rank e=j
  · simp [eqn]
  · have larger : ¬ rank e<j+1 := by omega
    simp [lt,eqn,larger]

theorem row_present (injective : Function.Injective rank) (e : E) :
    row repetitions rank (rank e)=repetitions e := by
  simp [row,injective.eq_iff]

theorem row_absent (j : ℕ) (absent : ∀e,rank e≠j) : row repetitions rank j=0 := by simp [row,absent]

theorem before_rank (e : E) : before repetitions rank (rank e)=ProtocolRAMPortRanks.«prefix» repetitions rank e := by
  simp [before,ProtocolRAMPortRanks.«prefix»,Finset.sum_filter]

theorem before_end (n : ℕ) (room : ∀e,rank e<n) : before repetitions rank n=∑e,repetitions e := by
  simp [before,room]

/-- The dense readback at the actual sparse source slot says where its output
starts. The rank may have holes; its cardinality is never used as a bound. -/
theorem physical {n w counts starts : ℕ} (m : Memory w) (sep : counts+n≤ starts) (fit : starts+n+1<2^w)
    (loaded : ∀i<n,m (counts+i)=(row repetitions rank i:Word w)) :
    (ProtocolRAMEndpointPrefix.exclusive w counts starts n).Exec m
      (ProtocolRAMEndpointPrefix.image starts (before repetitions rank) m n) (10+(3+12*n)) := by
  apply ProtocolRAMEndpointPrefix.run _ _ _ _ _ sep fit (before_zero ..)
  intro i hi
  rw [before_succ,loaded i hi,Nat.cast_add]

theorem physical_read {n w starts : ℕ} (m : Memory w) (e : E) (within : rank e≤n) :
    ProtocolRAMEndpointPrefix.image starts (before repetitions rank) m n (starts+rank e)=
      (ProtocolRAMPortRanks.«prefix» repetitions rank e:Word w) := by
  rw [ProtocolRAMEndpointPrefix.read _ _ _ _ _ within,before_rank]

end
end Hierarchy.DescentEdgeTapePrefix

end OAI
