import OAI.Computability.VPVNP.RAMLayout
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI
/-! # Arithmetic numbering for all shared CPU and sort messages

The common wire space can have exponentially many bits. Its encoding and
inverse therefore use only fixed mixed-radix products and sums. -/

namespace ThreeFlat.Diagonal.TracePhysical

open Computability.VPVNP

abbrev Shared (w r f d : ℕ) :=
  (Fin f × Fin ((5+r)*(w+1))) ⊕
    ((Fin (RAMLayout.layerCount d) × Fin (2^d) × Fin 2 × Fin (7*(w+1))) ⊕
     (Fin (2^d-1) × Fin (7*(w+1))))

private def product {α β : Type*} {a b : ℕ} (e : α ≃ Fin a) (f : β ≃ Fin b) :
    (α × β) ≃ Fin (a*b) := (e.prodCongr f).trans finProdFinEquiv

private def sum {α β : Type*} {a b : ℕ} (e : α ≃ Fin a) (f : β ≃ Fin b) :
    (α ⊕ β) ≃ Fin (a+b) := (e.sumCongr f).trans finSumFinEquiv

/-- Total sizes of the three disjoint blocks, before any ordinal casts. -/
def sharedCount (w r f d : ℕ) : ℕ :=
  f*((5+r)*(w+1)) + ((RAMLayout.layerCount d)*(2^d*(2*(7*(w+1)))) + (2^d-1)*(7*(w+1)))

theorem sharedCount_card (w r f d : ℕ) : sharedCount w r f d = Fintype.card (Shared w r f d) := by
  simp [sharedCount,Shared]

/-- An explicit mixed-radix encoding. Its inverse uses division with
remainder and two comparisons with block lengths at most. -/
def sharedOrdinal (w r f d : ℕ) : Shared w r f d ≃ Fin (Fintype.card (Shared w r f d)) :=
  (sum (product (Equiv.refl _) (Equiv.refl _))
    (sum (product (Equiv.refl _) (product (Equiv.refl _) (product (Equiv.refl _) (Equiv.refl _))))
      (product (Equiv.refl _) (Equiv.refl _)))).trans (finCongr (sharedCount_card w r f d))

theorem cpuOrdinal {w r f d : ℕ} (t : Fin f) (j : Fin ((5+r)*(w+1))) :
    (sharedOrdinal w r f d (.inl (t,j))).val = j.val + ((5+r)*(w+1))*t.val := rfl

theorem sortOrdinal {w r f d : ℕ} (l : Fin (RAMLayout.layerCount d)) (v : Fin (2^d))
    (s : Fin 2) (j : Fin (7*(w+1))) :
    (sharedOrdinal w r f d (.inr (.inl (l,v,s,j)))).val =
      f*((5+r)*(w+1)) + ((j.val + 7*(w+1)*s.val + (2*(7*(w+1)))*v.val) +
        (2^d*(2*(7*(w+1))))*l.val) := rfl

theorem boundaryOrdinal {w r f d : ℕ} (v : Fin (2^d-1)) (j : Fin (7*(w+1))) :
    (sharedOrdinal w r f d (.inr (.inr (v,j)))).val =
      f*((5+r)*(w+1)) + ((RAMLayout.layerCount d)*(2^d*(2*(7*(w+1)))) +
        (j.val + 7*(w+1)*v.val)) := rfl

end ThreeFlat.Diagonal.TracePhysical

end OAI
