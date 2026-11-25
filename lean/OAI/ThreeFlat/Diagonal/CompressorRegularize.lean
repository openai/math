import OAI.ThreeFlat.Diagonal.CompressorRefreshGraph
import Mathlib.Data.Finset.Sort

namespace OAI
/-! # Numbering the surviving parallel wires of a shrinking step

Each edge label records its motif occurrence, its surviving supply type and
the index of the parallel piece. Incoming and outgoing labels are sorted
independently at each base vertex. Distinct labels stay distinct even when
they have the same endpoints and displacement. -/

namespace ThreeFlat.Diagonal.CompressorRegularize

open Computability.VPVNP.Compression

variable {E B L : Type*} [Fintype E] [LinearOrder E] [DecidableEq B] {d : ℕ}

/-- Labels incident to `b` at the specified end of an edge. -/
def incident (f : E → B) (b : B) : Finset E := Finset.univ.filter (fun e => f e = b)

/-- Sort each incidence fiber by the label order and number it consecutively. -/
def numbering (f : E → B) (h : ∀ b, (incident f b).card = d) : E ≃ B × Fin d :=
  (Equiv.sigmaFiberEquiv f).symm.trans (Equiv.sigmaEquivProdOfEquiv fun b =>
    (Equiv.subtypeEquivRight (p := fun e => f e = b) (q := fun e => e ∈ incident f b)
      (fun e => by simp [incident])).trans ((incident f b).orderIsoOfFin (h b)).toEquiv.symm)

@[simp] theorem numbering_base (f : E → B) (h : ∀ b, (incident f b).card = d) (e : E) :
    (numbering f h e).1 = f e := rfl

/-- Matching the two sorted lists through the underlying edge identity
simultaneously enumerates all incoming and all outgoing slots. -/
def graph (src dst : E → B) (shift : E → L) (hs : ∀ b, (incident src b).card = d)
    (ht : ∀ b, (incident dst b).card = d) (hne : ∀ e, dst e ≠ src e) : LiftedSlots B d L where
  base := {
    target := (numbering src hs).symm.trans (numbering dst ht)
    ends_ne := by
      intro p
      obtain ⟨e, rfl⟩ := (numbering src hs).surjective p
      simpa only [Equiv.trans_apply, Equiv.symm_apply_apply, numbering_base] using hne e
  }
  displacement p := shift ((numbering src hs).symm p)

/-- On every lane, a labelled edge sends the old slot to its prescribed
receiving slot and translates exactly by the prescribed displacement. -/
theorem edge_lift [AddCommGroup L] (src dst : E → B) (shift : E → L)
    (hs : ∀ b, (incident src b).card = d) (ht : ∀ b, (incident dst b).card = d)
    (hne : ∀ e, dst e ≠ src e) (e : E) (g : L) :
    (graph src dst shift hs ht hne).actualTarget ((numbering src hs e), g) =
      ((numbering dst ht e), g + shift e) := by
  simp [graph]

/-- Pad a regular family of labelled edges to the next degree by rotating
the tag at each vertex; these new slots carry zero displacement. -/
def padGraph {V : Type*} [DecidableEq V] [Zero L] {D d' : ℕ}
    (src dst : E → V × Fin D) (shift : E → L)
    (hs : ∀ b, (incident src b).card = d) (ht : ∀ b, (incident dst b).card = d)
    (hne : ∀ e, dst e ≠ src e) (hD : 2 ≤ D) (hd : d ≤ d') : LiftedSlots (V × Fin D) d' L :=
  let G := graph src dst shift hs ht hne
  let padding := CompressorRefresh.internal (L := L) V (CompressorRefresh.padding hD (d'-d))
  (show d + (d'-d) = d' by omega) ▸ CompressorRefresh.union G padding

end ThreeFlat.Diagonal.CompressorRegularize

end OAI
