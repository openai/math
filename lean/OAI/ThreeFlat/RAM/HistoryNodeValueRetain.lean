import OAI.ThreeFlat.RAM.HistoryNodeValue
import OAI.ThreeFlat.RAM.HistoryNodeAddress

namespace OAI
/-! # Preserving every used word of a physically stored node -/

namespace ThreeFlat.RAM.HistoryStageBody.Physical.NodeValue
open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.TickWorkspace
open scoped Fin.CommRing
variable {F : Type*} {W : ℕ}
variable (v : NodeValue F) (id : ((Fin 3→Bool)→F)→ℕ)

def uses (u i a : ℕ) :=
  (base u 13+8*i≤a ∧ a<base u 13+8*i+6) ∨
  (v.stream≤a ∧ a<v.stream+4*v.net.cells) ∨ (v.ext≤a ∧ a<v.ext+v.external)

theorem Cached.retain {u i : ℕ} {m m' : Memory W} (h : v.Cached id u i m)
    (frame : ∀ a,v.uses u i a → m' a=m a) : v.Cached id u i m' := by
  have head (j : ℕ) (hj : j<6) : m' (base u 13+8*i+j)=m (base u 13+8*i+j) :=
    frame _ (Or.inl (by omega))
  constructor
  · simpa only [HistoryStageRoot.atResult,head 1 (by decide),head 2 (by decide),head 3 (by decide),
      head 4 (by decide),head 5 (by decide),show m' (base u 13+8*i)=m (base u 13+8*i) by simpa using head 0 (by decide)] using h.header
  · intro r j
    rw [frame _ (Or.inr (Or.inl (by have := r.isLt; have := j.isLt; omega)))]
    exact h.rows r j
  · intro j
    rw [frame _ (Or.inr (Or.inr (by have := j.isLt; omega)))]
    exact h.ends j

end ThreeFlat.RAM.HistoryStageBody.Physical.NodeValue

end OAI
