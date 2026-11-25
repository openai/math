import OAI.Hierarchy.DescentMeasuredRectangle

namespace OAI
/-! # Stable estimator row addresses under public host and port capacity bounds -/
namespace Hierarchy.DescentMeasuredWeights
open DescentGL DescentIntegerScale DescentWeightColumnRAM
open scoped Classical BigOperators
noncomputable section
variable {A C : Type} [Fintype A] [Fintype C] {H P Δ D m : ℕ}

/-- Keep the level and contact columns as separate regions. The split point always uses
the public host capacity, and each contact row always uses the public port pitch. -/
def widen (hosts : H≤P) (ports : Δ≤D) :
    Fin (H*(m+1)+H*Δ) ↪ Fin (P*(m+1+D)) :=
  let left := finProdFinEquiv.symm.toEmbedding.trans
    (((Fin.castLEEmb hosts).prodMap (Function.Embedding.refl (Fin (m+1)))).trans finProdFinEquiv.toEmbedding)
  let right := finProdFinEquiv.symm.toEmbedding.trans
    (((Fin.castLEEmb hosts).prodMap (Fin.castLEEmb ports)).trans finProdFinEquiv.toEmbedding)
  finSumFinEquiv.symm.toEmbedding.trans ((left.sumMap right).trans
    (finSumFinEquiv.toEmbedding.trans (finCongr (Nat.mul_add P (m+1) D).symm).toEmbedding))

def publicRectangle (idx : A ≃ Fin H) (levels : A→ℕ) (fit : ∀a,levels a≤ m+1)
    (edges : C ↪ Fin H×Fin Δ) (hosts : H≤P) (ports : Δ≤D) :
    Item levels C ↪ Fin (P*(m+1+D)) :=
  (rectangle idx levels fit edges).trans (widen hosts ports)

omit [Fintype A] [Fintype C] in
theorem public_site (idx : A ≃ Fin H) (levels : A→ℕ) (fit : ∀a,levels a≤ m+1)
    (edges : C ↪ Fin H×Fin Δ) (hosts : H≤P) (ports : Δ≤D) (v : A) (j : Fin (levels v)) :
    (publicRectangle idx levels fit edges hosts ports (.inl ⟨v,j⟩)).val =
      (idx v).val*(m+1)+j.val := by
  simp [publicRectangle,rectangle,widen,siteSlot,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
  rfl

omit [Fintype A] [Fintype C] in
theorem public_port (idx : A ≃ Fin H) (levels : A→ℕ) (fit : ∀a,levels a≤ m+1)
    (edges : C ↪ Fin H×Fin Δ) (hosts : H≤P) (ports : Δ≤D) (e : C) :
    (publicRectangle idx levels fit edges hosts ports (.inr e)).val =
      P*(m+1)+(edges e).1.val*D+(edges e).2.val := by
  simp [publicRectangle,rectangle,widen,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm,
    Nat.add_left_comm]

theorem padded_widen {I X : Type} {n N : ℕ} (loc : I↪Fin n) (embed : Fin n↪Fin N)
    (x : I→X) (empty : X) (row : Fin N) :
    padded embed (padded loc x empty) empty row=padded (loc.trans embed) x empty row := by
  by_cases hit : ∃i,embed i=row
  · obtain ⟨i,rfl⟩:=hit
    rw [padded_at]
    by_cases real : ∃a,loc a=i
    · obtain ⟨a,rfl⟩:=real
      exact (padded_at loc x empty a).trans (padded_at (loc.trans embed) x empty a).symm
    · rw [padded_else loc x empty i real,padded_else]
      intro ⟨a,ha⟩
      exact real ⟨a,embed.injective ha⟩
  · rw [padded_else embed _ empty row hit,padded_else]
    rintro ⟨v,eq⟩
    exact hit ⟨loc v,eq⟩

end
end Hierarchy.DescentMeasuredWeights

end OAI
