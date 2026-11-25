import OAI.LinearAlgebra.FiniteFourier.PrimeHermiteOps

/-! # Serial and parallel circuits on ordinary work rows -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {K α : Type*} [CommSemiring K] [Fintype α]
  {I J O I' O' : Type*} [Fintype I] [Fintype J] [Fintype I']

/-- Row-indexed notation for a circuit on the wires `I × α`. -/
def RealizesRows (F : (I → α → K) → O → α → K) (c : ℕ) : Prop :=
  RealizesOp (fun x (p : O × α) => F (Function.curry x) p.1 p.2) c

theorem RealizesRows.comp {F : (I → α → K) → J → α → K}
    {G : (J → α → K) → O → α → K} {c d : ℕ}
    (hG : RealizesRows G d) (hF : RealizesRows F c) : RealizesRows (G ∘ F) (d+c) :=
  RealizesOp.comp hG hF

theorem RealizesRows.id : RealizesRows (id : (I → α → K) → _) 0 :=
  RealizesOp.id

theorem RealizesRows.parallel {F : (I → α → K) → O → α → K}
    {G : (I' → α → K) → O' → α → K} {c d : ℕ}
    (hF : RealizesRows F c) (hG : RealizesRows G d) :
    RealizesRows (fun x => Sum.elim (F (x ∘ Sum.inl)) (G (x ∘ Sum.inr))) (c+d) := by
  refine Eq.mp ?_ ((RealizesOp.parallel hF hG).reindex
    (Equiv.sumProdDistrib I I' α).symm (Equiv.sumProdDistrib O O' α).symm)
  unfold RealizesRows
  congr 1
  funext x p
  rcases p with ⟨i | j, a⟩ <;> rfl

theorem RealizesRows.fanout {F : (I → α → K) → O → α → K}
    {G : (I → α → K) → O' → α → K} {c d : ℕ}
    (hF : RealizesRows F c) (hG : RealizesRows G d) :
    RealizesRows (fun x => Sum.elim (F x) (G x)) (c+d) := by
  refine Eq.mp ?_ ((RealizesOp.fanout hF hG).reindex (Equiv.refl _) (Equiv.sumProdDistrib O O' α).symm)
  unfold RealizesRows
  congr 1
  funext x p
  rcases p with ⟨i | j, a⟩ <;> rfl

theorem RealizesRows.iterate {F : (I → α → K) → I → α → K}
    {c : ℕ} (hF : RealizesRows F c) (n : ℕ) : RealizesRows (F^[n]) (n*c) := by
  induction n with
  | zero => simpa using (RealizesRows.id (I := I) (α := α) (K := K))
  | succ n ih => simpa [Function.iterate_succ, Nat.succ_mul] using ih.comp hF

end FiniteFourier
end LinearAlgebra
end OAI
