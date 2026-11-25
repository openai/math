import OAI.ThreeFlat.Diagonal.GroupedRewrite

namespace OAI
/-! # A compressor history step with a common, term-dependent placement

The term array determines the layout and its successor graph. Each kernel
factors through its owner's old indices and the surviving half-wires at
that site. The term numbering is supplied by the chosen history encoding.
-/

namespace ThreeFlat.Diagonal.MotifKernel

open LinearAlgebra.SpectralBooks HistoryContraction
open scoped Classical BigOperators

variable {M J E G F : Type} [Fintype M] [Fintype J] [Fintype E] [Fintype G] [DecidableEq G] [CommSemiring F]

variable (S : Shape) [∀ i, Inhabited (S.Half i)] (H : M → Type) [∀ m, Fintype (H m)]
  (P : M → PortGraph J E) (I : ∀ m, H m → E → Type) [∀ m t e, Fintype (I m t e)] [∀ m t e, Inhabited (I m t e)]
  (place : (∀ m,H m) → M → J → G) (owner : (∀ m, H m) → S.Site → G)

/-- Fill the old half-indices not needed at this current owner. -/
def extendRow {X : Type} (A : X → Type) [∀ x, Inhabited (A x)]
    (own : X → G) (g : G) (row : ∀ i : {i // own i = g}, A i) (i : X) : A i :=
  if h : own i = g then row ⟨i,h⟩ else default

variable (K : ∀ m t j, (∀ i, S.Half i) → (P m).State (I m t) j → F)

/-- The actual per-site kernel of this stage in the history interpreter. -/
noncomputable def stepKernel (h : ∀ m,H m) (g : G) (row : ∀ i : {i // owner h i = g}, S.Half i)
    (y : (crossShape P (place h) (fun m => I m (h m))).Half g) : F :=
  ∏ m, groupedFactor (P m) (place h m) (fun j => K m (h m) j (extendRow S.Half (owner h) g row)) g
    (visible P (place h) (fun m => I m (h m)) g y m)

/-- Turn the actual motif substitution into the recursive history object's
rewrite operation; the successor consists of precisely its crossing edges. -/
noncomputable def historyStep {count : ℕ} (enum : Fin count ≃ (∀ m, H m))
    (locality : ∀ h m j (a b : ∀ i, S.Half i), (∀ i, owner h i = place h m j → a i = b i) →
      K m (h m) j a = K m (h m) j b)
    (wiring : ∀ a, S.graph.wiring S.Label a = ∏ m, ∑ t, (P m).contraction (fun j => K m t j a)) :
    Rewrite S F where
  count := count
  target i := crossShape P (place (enum i)) (fun m => I m (enum i m))
  owner i := owner (enum i)
  kernel i := stepKernel S H P I place owner K (enum i)
  wire_eq a := by
    let target (h : ∀ m,H m) := crossShape P (place h) (fun m => I m (h m))
    let result (h : ∀ m,H m) := (target h).contract (fun g y => stepKernel S H P I place owner K h g (fun i => a i) y)
    change _ = ∑ i, result (enum i)
    rw [enum.sum_comp, wiring, simultaneous_grouping P H I (fun m t j => K m t j a) place]
    apply Finset.sum_congr rfl
    intro h _
    rw [← cross_contract P (place h) (fun m => I m (h m)) (fun m j => K m (h m) j a)]
    apply congrArg (target h).contract
    funext g y
    apply Finset.prod_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.prod_congr rfl
    rintro ⟨j,rfl⟩ _
    exact congrFun (locality h m j a (extendRow S.Half (owner h) (place h m j) (fun i => a i))
      (fun i hi => by simp [extendRow,hi])) _

end ThreeFlat.Diagonal.MotifKernel

end OAI
