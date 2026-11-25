import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarCertificateCounts
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarPortEuler

/-! # The root Euler test from local port counts

At a vertex each outgoing port contributes one wire, and each port reporting
itself as face minimum contributes one marked dart. The two subtree totals
aggregate these local contributions. A connected map whose root has no ports
uses the single exterior face.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PlanarPatch

open Finset

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
variable (G : PortGraph V E) {r : V} {parent : V → V} {depth total : V → ℕ}

/-- The wire contribution counts only tail ports at this vertex. -/
def edgeWeight (v : V) : ℕ :=
  (univ.filter (fun p : G.Port v => p.val.2 = false)).card

theorem edgeTotal_root_eq (ht : SubtreeTotals r parent (edgeWeight G) total) :
    total r = Fintype.card E := by
  simp only [SubtreeTotals, edgeWeight, count_tail_ports] at ht
  exact rootTotal_eq_card_fibers (s := univ) (owner := G.tail) (parent := parent) ht

theorem edgeTotal_le_card (hd : ∀ w, w ≠ r → depth (parent w) < depth w)
    (ht : SubtreeTotals r parent (edgeWeight G) total) (v : V) : total v ≤ Fintype.card E :=
  (subtreeTotal_le_root hd ht v).trans_eq (edgeTotal_root_eq G ht)

/-- The adjustment for a root of degree zero uses only its own port count. -/
def observedFaces (root : V) (rawFaces : ℕ) : ℕ :=
  if Fintype.card (G.Port root) = 0 then 1 else rawFaces

variable [LinearOrder (E × Bool)]

/-- The face contribution counts the ports reporting themselves as the minimum. -/
def faceWeight (record : E × Bool → (E × Bool) × ℕ) (v : V) : ℕ :=
  (univ.filter (fun p : G.Port v => (record p.val).1 = p.val)).card

/-- The raw face total counts each reported minimum once at its own vertex. -/
theorem rawFaceTotal_root_eq (record : E × Bool → (E × Bool) × ℕ)
    (ht : SubtreeTotals r parent (faceWeight G record) total) :
    total r = (univ.filter (fun d => (record d).1 = d)).card := by
  let _ : DecidableEq E := Classical.decEq E
  let marked := univ.filter (fun d => (record d).1 = d)
  have hweight (v : V) : faceWeight G record v =
      (marked.filter (fun p => G.vertex p.1 p.2 = v)).card := by
    rw [← count_marked_ports G marked v]
    apply congrArg card
    ext p
    simp [marked]
  calc
    total r = marked.card := rootTotal_eq_card_fibers (s := marked)
      (owner := fun p : E × Bool => G.vertex p.1 p.2) (parent := parent)
      (by simpa only [SubtreeTotals, hweight] using ht)
    _ = _ := congrArg card (by ext d; simp [marked])

theorem rawFaceTotal_le_card (record : E × Bool → (E × Bool) × ℕ)
    (hd : ∀ w, w ≠ r → depth (parent w) < depth w)
    (ht : SubtreeTotals r parent (faceWeight G record) total) (v : V) :
    total v ≤ Fintype.card (E × Bool) :=
  (subtreeTotal_le_root hd ht v).trans ((rawFaceTotal_root_eq G record ht).le.trans (card_le_univ _))

/-- The root recovers precisely the face count including the isolated vertex. -/
theorem observedFaces_eq_faceCount (hc : (underlying G.tail G.head).Connected)
    {record : E × Bool → (E × Bool) × ℕ} (ht : SubtreeTotals r parent (faceWeight G record) total) :
    observedFaces G r (total r) = PlanarFace.faceCount record := by
  cases isEmpty_or_nonempty E with
  | inl hempty =>
    simp [observedFaces, PlanarFace.faceCount_dartless]
  | inr hne =>
    have := PortGraph.Rotation.nonempty_ports_of_connected hc r
    simp [observedFaces, PlanarFace.faceCount, rawFaceTotal_root_eq G record ht]

/-- Checking the three local aggregate records at the root implements the
integer Euler test on the rotation system. -/
theorem rootEuler_iff_genusZero [DecidableEq E] (ρ : G.Rotation)
    (hc : (underlying G.tail G.head).Connected) {record : E × Bool → (E × Bool) × ℕ}
    (hrec : PlanarFace.Valid ρ.picture.face record) {size edges faces : V → ℕ}
    (hs : SubtreeTotals r parent (fun _ => 1) size)
    (he : SubtreeTotals r parent (edgeWeight G) edges)
    (hf : SubtreeTotals r parent (faceWeight G record) faces) :
    (size r : ℤ) - edges r + observedFaces G r (faces r) = 2 ↔ ρ.picture.GenusZero := by
  rw [root_subtreeSize_eq_card hs, edgeTotal_root_eq G he, observedFaces_eq_faceCount G hc hf]
  exact ρ.certifiedEuler_iff_genusZero hc hrec

end PlanarPatch

end SpectralBooks
end LinearAlgebra
end OAI
