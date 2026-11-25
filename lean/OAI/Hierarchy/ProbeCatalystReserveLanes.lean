import OAI.Hierarchy.ProbeCatalystArchiveGeometry
import OAI.Hierarchy.ProbeCoreReserve

namespace OAI
/-! # Disjoint chronological intervals in the original column reserves -/

noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open ProbeStage ProbeStage.CoreBoard
open scoped Classical BigOperators
variable {n count R : ℕ} (owner : Fin n→Fin count) (bits : Fin n→ℕ)

/-- Number of earlier debit bits from this same physical resource. -/
def usedBefore (i : Fin n) := ∑ j : Fin n, if j < i ∧ owner j=owner i then bits j else 0

theorem through_le (i : Fin n) :
    usedBefore owner bits i+bits i≤∑ j,if owner j=owner i then bits j else 0 := by
  have single : (∑ j : Fin n,if j=i then bits i else 0)=bits i := by simp
  unfold usedBefore
  rw [← single,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  by_cases eq : j=i
  · subst j; simp
  · by_cases same : owner j=owner i <;> by_cases earlier : j < i <;> simp [eq,same,earlier]

theorem through_le_next {i j : Fin n} (first : i < j) (same : owner i=owner j) :
    usedBefore owner bits i+bits i≤usedBefore owner bits j := by
  have single : (∑ v : Fin n,if v=i then bits i else 0)=bits i := by simp
  unfold usedBefore
  rw [← single,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v _
  by_cases eq : v=i
  · subst v; simp [first,same]
  · by_cases earlier : v < i
    · have before := earlier.trans first
      simp [eq,earlier,before,same]
    · simp [eq,earlier]

/-- Every paid unit gets one distinct bit in its own advance reserve,
including when other rows at the same date debit different accounts. -/
def reserveLanes (funded : ∀i, (∑ j,if owner j=i then bits j else 0)≤R) :
    (Σ i : Fin n, Fin (bits i)) ↪ Fin count × Fin R where
  toFun x := (owner x.1,⟨usedBefore owner bits x.1+x.2.val,by
    have covered := (through_le owner bits x.1).trans (funded (owner x.1))
    have inside := x.2.isLt
    omega⟩)
  inj' := by
    rintro ⟨i,u⟩ ⟨j,v⟩ eq
    have same : owner i=owner j := congrArg Prod.fst eq
    have lane : usedBefore owner bits i+u.val=usedBefore owner bits j+v.val :=
      congrArg (fun p : Fin count × Fin R=>p.2.val) eq
    have ui := u.isLt
    have vj := v.isLt
    rcases lt_trichotomy i j with lt|rfl|gt
    · have gap := through_le_next owner bits lt same
      omega
    · have uv : u=v := Fin.ext (by omega)
      subst v; rfl
    · have gap := through_le_next owner bits gt same.symm
      omega

variable {h d k : ℕ}

def physicalLanes (id : Fin n→Fin (Fintype.card (Columns h d)*k))
    (amt : Fin n→ℕ) (funded : ∀p, (∑ j,if id j=p then amt j else 0)≤R) :
    (Σ i : Fin n,Fin (amt i)) ↪ ReserveBits h d k R :=
  (reserveLanes id amt funded).trans
    (((pairKeys (Columns h d) k).symm.prodCongr (Equiv.refl (Fin R))).trans
      (reserveSeats h d k R).symm).toEmbedding

theorem physical_owner (id : Fin n→Fin (Fintype.card (Columns h d)*k))
    (amt : Fin n→ℕ) (funded : ∀p, (∑ j,if id j=p then amt j else 0)≤R)
    (i : Fin n) (u : Fin (amt i)) :
    reserveLocation h d k R (physicalLanes id amt funded ⟨i,u⟩)=(pairKeys (Columns h d) k).symm (id i) := by
  change ((reserveSeats h d k R) ((reserveSeats h d k R).symm _)).1=_
  exact congrArg Prod.fst ((reserveSeats h d k R).apply_symm_apply _)

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
