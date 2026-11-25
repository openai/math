import OAI.Hierarchy.ProbeCatalystReserveLanes

namespace OAI
/-! # Exact partition into withdrawn bits and untouched return wires -/

noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open ProbeStage ProbeStage.CoreBoard
open scoped Classical BigOperators
variable {n count R : ℕ} (owner : Fin n→Fin count) (amt : Fin n→ℕ)

def usedAt (p : Fin count) := ∑ j,if owner j=p then amt j else 0

theorem total_used : ∑ p,usedAt owner amt p=∑ i,amt i := by
  unfold usedAt
  rw [Finset.sum_comm]
  simp

variable (available : ∀p,usedAt owner amt p≤R)

def returnLanes : (Σ p : Fin count,Fin (R-usedAt owner amt p)) ↪ Fin count × Fin R where
  toFun x := (x.1,⟨usedAt owner amt x.1+x.2.val,by
    have fits := available x.1
    have inside := x.2.isLt
    omega⟩)
  inj' := by
    rintro ⟨i,u⟩ ⟨j,v⟩ eq
    have same : i=j := congrArg Prod.fst eq
    subst j
    have exactLane : usedAt owner amt i+u.val=usedAt owner amt i+v.val :=
      congrArg (fun p : Fin count × Fin R=>p.2.val) eq
    have uv : u=v := Fin.ext (by omega)
    subst v; rfl

theorem apart (x : Σ i : Fin n,Fin (amt i)) (y : Σ p : Fin count,Fin (R-usedAt owner amt p)) :
    reserveLanes owner amt available x ≠ returnLanes owner amt available y := by
  intro eq
  have key : owner x.1=y.1 := congrArg Prod.fst eq
  have point : usedBefore owner amt x.1+x.2.val=usedAt owner amt y.1+y.2.val :=
    congrArg (fun p : Fin count × Fin R=>p.2.val) eq
  have inside := x.2.isLt
  have bound : usedBefore owner amt x.1+amt x.1≤usedAt owner amt y.1 :=
    key ▸ through_le owner amt x.1
  omega

def reservePartition :
    ((Σ i : Fin n,Fin (amt i)) ⊕ (Σ p : Fin count,Fin (R-usedAt owner amt p))) ≃ Fin count × Fin R := by
  let spent := reserveLanes owner amt available
  let back := returnLanes owner amt available
  let assign := Sum.elim spent back
  apply Equiv.ofBijective assign
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · rintro (i|p) (j|q) eq
    · exact congrArg Sum.inl (spent.injective eq)
    · exact False.elim (apart owner amt available i q eq)
    · exact False.elim (apart owner amt available j p eq.symm)
    · exact congrArg Sum.inr (back.injective eq)
  · simp only [Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin,Fintype.card_prod]
    rw [← total_used owner amt,← Finset.sum_add_distrib]
    calc
      _ = ∑ _p : Fin count,R := Finset.sum_congr rfl (fun p _=>by have := available p; omega)
      _ = _ := by simp

/-- Every original advance bit is either assigned to its unique live
debit occurrence or returned untouched in its own signed column. -/
def physicalPartition {h d k : ℕ} (id : Fin n→Fin (Fintype.card (Columns h d)*k))
    (a : Fin n→ℕ) (fund : ∀p,usedAt id a p≤R) :
    ((Σ i : Fin n,Fin (a i)) ⊕ (Σ p : Fin (Fintype.card (Columns h d)*k),Fin (R-usedAt id a p))) ≃
      ReserveBits h d k R :=
  (reservePartition id a fund).trans
    (((pairKeys (Columns h d) k).symm.prodCongr (Equiv.refl (Fin R))).trans (reserveSeats h d k R).symm)

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
