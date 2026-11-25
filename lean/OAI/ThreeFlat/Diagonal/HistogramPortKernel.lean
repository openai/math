import OAI.ThreeFlat.Diagonal.SelectorPortKernel
import OAI.ThreeFlat.Diagonal.MotifDemandPadding
import OAI.ThreeFlat.Diagonal.MotifHistogram
import OAI.ThreeFlat.Diagonal.MotifBinaryPacking

namespace OAI
/-! # Histogram-indexed kernels for arbitrarily padded motif widths

The demand is sliced across base copies. The supply selector sequences are
packed on each edge and synchronized by the actual port checks. Only the
histogram of base selectors is retained as an outer term.
-/

namespace ThreeFlat.Diagonal.MotifOuterTerms

open LinearAlgebra.SpectralBooks Computability.VPVNP.MotifSelector MotifDemandPadding
open scoped BigOperators Classical

variable {J E S H F : Type*} [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [Fintype H] [DecidableEq H]
  [CommSemiring F] {r k : ℕ}

/-- A valid selector uniquely splits each incident payload into the fields
read by its respective base copies. -/
def unpackHistAt (w : H → S → ℕ) (v : Histogram H r) (t : {s // histogram s = v}) (e : S)
    (x : Fin (2 ^ histWidth w v e)) (j : Fin r) : Fin (2 ^ w (t.1 j) e) :=
  let he := (histogram_width w t.1 e).symm.trans (congrArg (fun a => histWidth w a e) t.2)
  (MotifBinaryPacking.pack (fun i => w (t.1 i) e)).symm (Fin.cast (congrArg (2 ^ ·) he.symm) x) j

def packHistPayload (w : H → S → ℕ) (s : Fin r → H) :
    (∀ j e, Fin (2 ^ w (s j) e)) ≃ (∀ e, Fin (2 ^ histWidth w (histogram s) e)) :=
  (Equiv.piComm (fun j e => Fin (2 ^ w (s j) e))).trans (Equiv.piCongrRight fun e =>
    (MotifBinaryPacking.pack (fun i => w (s i) e)).trans (finCongr (congrArg (2 ^ ·) (histogram_width w s e).symm)))

omit [Fintype S] in
private theorem unpack_histogram (w : H → S → ℕ) (t : Fin r → H)
    (a : ∀ j e, Fin (2 ^ w (t j) e)) (e : S) (j : Fin r) :
    unpackHistAt w (histogram t) ⟨t,rfl⟩ e (packHistPayload w t a e) j = a j e := by
  unfold unpackHistAt
  simp only [packHistPayload, Fin.cast_cast, Fin.cast_refl, finCongr_apply,
    Equiv.trans_apply, Equiv.piCongrRight_apply, Equiv.piComm_apply, Pi.map_apply, id_eq, Equiv.symm_apply_apply]

variable (D : PortGraph J E) (G : Supply J S)
  (w base : E → ℕ) (hpad : ∀ e, w e ≤ base e*r) (supplyWidth : H → S → ℕ)
  (code : H ↪ Fin (2^k))
  (M : ∀ h v, D.State (fun e => Fin (2^base e)) v →
    (ports G).State (fun e => Fin (2^supplyWidth h e)) v → F)

/-- The product of the constant base maps selected by a valid histogram word. -/
noncomputable def histogramTileProduct (v : Histogram H r) (j : J)
    (x : D.State (fun e => Fin (2^w e)) j) (s : {t // histogram t = v})
    (y : (ports G).State (fun e => Fin (2^histWidth supplyWidth v e)) j) : F :=
  ∏ i, M (s.1 i) j (readSlice D (fun e => digits (w e) (base e) r (hpad e)) i j x)
    (fun p => unpackHistAt supplyWidth v s p.1.1 (y p) i)

/-- The local map used on genuine old and new half-port words. -/
noncomputable def histogramKernel (v : Histogram H r) (j : J) (x : D.State (fun e => Fin (2^w e)) j) :=
  checkedPort G (histogram (H := H) (r := r)) (sequenceCode code r)
    (fun v e => Fin (2^histWidth supplyWidth v e)) v j (histogramTileProduct D G w base hpad supplyWidth M v j x)

set_option maxHeartbeats 2400000 in
omit [Fintype J] [Nonempty J] [Fintype E] in
/-- Decode the common selector if every incident word agrees and the
histogram check passes. All other cases give coefficient zero. -/
theorem histogramKernel_eq (v : Histogram H r) (j : J) (x : D.State (fun e => Fin (2^w e)) j)
    (y : (ports G).State (fun e => (Fin r → Fin (2^k)) × Fin (2^histWidth supplyWidth v e)) j) :
    histogramKernel D G w base hpad supplyWidth code M v j x y =
      if ∀ i, (y i).1 = (y (anchorPort G j)).1 then
        if h : ∃ t : {s // histogram s = v}, sequenceCode code r t.1 = (y (anchorPort G j)).1 then
          histogramTileProduct D G w base hpad supplyWidth M v j x h.choose (fun i => (y i).2)
        else 0 else 0 := by
  classical
  unfold histogramKernel checkedPort decodeLocal
  split_ifs <;> first | rfl

omit [Fintype E] in
/-- Exact tile substitution with a single outer branch per canonical histogram. -/
theorem histogram_port_kernel
    (tile : ∀ x, D.wiring (fun e => Fin (2 ^ base e)) x =
      ∑ h, ∑ a : ∀ e, Fin (2 ^ supplyWidth h e), ∏ v, M h v (x v) ((ports G).atVertex a v))
    (x : ∀ j, D.State (fun e => Fin (2^w e)) j) :
    D.wiring (fun e => Fin (2^w e)) x = ∑ v : Histogram H r,
      (ports G).contraction (A := fun e => (Fin r → Fin (2^k)) × Fin (2^histWidth supplyWidth v e)) (fun j => histogramKernel D G w base hpad supplyWidth code M v j (x j)) := by
  classical
  rw [show (∑ v : Histogram H r, (ports G).contraction (A := fun e => (Fin r → Fin (2^k)) × Fin (2^histWidth supplyWidth v e)) (fun j => histogramKernel D G w base hpad supplyWidth code M v j (x j))) = _ from
    contraction_checked_ports G (histogram (H := H) (r := r)) (sequenceCode code r)
      (fun v e => Fin (2^histWidth supplyWidth v e)) (fun v j => histogramTileProduct D G w base hpad supplyWidth M v j (x j))]
  rw [tiled_words D (ports G) w base hpad (fun h e => Fin (2 ^ supplyWidth h e)) M tile x]
  apply Finset.sum_congr rfl
  intro s _
  let f := fun z : ∀ e, Fin (2 ^ histWidth supplyWidth (histogram s) e) =>
    ∏ j, histogramTileProduct D G w base hpad supplyWidth M (histogram s) j (x j) ⟨s,rfl⟩
      ((ports G).atVertex z j)
  change _ = ∑ z, f z
  rw [← (packHistPayload supplyWidth s).sum_comp f]
  apply Finset.sum_congr rfl
  intro a _
  simp only [f, histogramTileProduct, PortGraph.atVertex, unpack_histogram]; rfl

end ThreeFlat.Diagonal.MotifOuterTerms

end OAI
