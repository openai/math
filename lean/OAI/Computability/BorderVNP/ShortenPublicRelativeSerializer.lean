import OAI.Computability.BorderVNP.ShortenPublicRelativePlacement
import OAI.Computability.BorderVNP.ShortenPublicEndpointSuccessor
import OAI.Computability.BorderVNP.ShortenPublicSegmentJoin

/-!
# Wiring the physical site batch into the next endpoint table

The serializer sees the tile and successor catalog wires produced by the
placement circuit. Its other inputs are the interval directory and the public
histogram. All cable rows share this one site batch, including the repeated
requests for the reserved site of an unused cable row.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicRelative

open Epoch Catalog Crossing CombiningStep Cover Cover.AddressCircuit StaticRows PublicEndpoints
open PublicEndpoints.Successor PublicSegments
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

variable {D m : ℕ} {K : Type*} [Field K] {P : Type*} {bits : P → ℕ}

/-- The two raw cable-field arrays forwarded alongside the generated site payload. -/
abbrev CableFields (e : PaidIdentity K D m) (A : Type*) (edges w : ℕ) :=
  (Serializer.Row edges D × Serializer.DirectoryInput w) ⊕ (A × Option (Fin e.count) × Fin w)

variable {X B : Type*} [Fintype X] [Fintype B] {A : Type} [Fintype A] {sites edges seeds w : ℕ}

/-- Run the geometric circuit once. All directory and histogram columns
are forwarded by wires to the shared successor serializer. -/
noncomputable def preparedSource (e : PaidIdentity K D m)
    (sf : Frame X (Fin (siteCapacity e sites seeds) × B)) :
    Frame (X ⊕ CableFields e A edges w) (Source e B A sites edges seeds w) :=
  parallelFrame (sf.subst (Frame.initial Sum.inl)) (Frame.initial Sum.inr)

/-- The source preparation costs exactly the number of gates in the site batch. -/
theorem preparedSource_size (e : PaidIdentity K D m) (sf : Frame X (Fin (siteCapacity e sites seeds) × B)) :
    (preparedSource (A := A) (edges := edges) (w := w) e sf).size = sf.size := by simp [preparedSource]

/-- Directory and histogram words keep their exact values; the site field
bank contains the outputs of the single geometry circuit. -/
theorem preparedSource_eval (e : PaidIdentity K D m) (sf : Frame X (Fin (siteCapacity e sites seeds) × B))
    (geo : X → Bool) (c : CableFields e A edges w → Bool) :
    (preparedSource e sf).eval (Sum.elim geo c) = Sum.elim (sf.eval geo) c := by
  have h : (Frame.initial (Sum.inl : X → X ⊕ CableFields e A edges w)).eval (Sum.elim geo c) = geo :=
    funext fun _ => by simp
  funext j
  cases j <;> simp [preparedSource,Frame.subst_eval,h]

variable {q : ℕ} {I : Type*} [Fintype I] [NeZero D]

/-- Both circuits at the prescribed static dimensions. For every genuine
directory and histogram the combined circuit gives the sewn network's exact
stable endpoint/width table, occupancy bits, and computed site payloads. -/
theorem serializer_frames (enum : Fin q ≃ I) (pat : Pattern I D) (e : PaidIdentity K D m)
    (S : Finset (HyperbolicHost I)) :
    ∃ C k : ℕ, ∀ (d : ℕ), 1 ≤ d → ∀ (copies sites edges seeds w : ℕ) (home : Fin sites → Fin copies)
      (seed : A ≃ Fin seeds), siteCapacity e sites seeds ≤ 2^w → edgeCapacity e edges seeds ≤ 2^w →
      let B := ProductSlots q (d+2*pat.depth) ⊕ ↥(pat.nextSites e S)
      ∃ (sf : Frame (BatchPorts q pat S d copies sites seeds) (Fin (siteCapacity e sites seeds) × B))
        (f : Frame (BatchPorts q pat S d copies sites seeds ⊕ CableFields e A edges w)
          (Next B (siteCapacity e sites seeds) (edgeCapacity e edges seeds) w)),
        BatchRows enum pat e S d home sf ∧
        f.size ≤ (1+siteCapacity e sites seeds)*C*(d+1)^k + cost e edges seeds w ∧
        ∀ (N : Pack D P bits K) (bin : N.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
          (positive : N.layout.Edge → Bool) (old : N.layout.Site ↪ Fin sites) (rows : N.layout.Edge ↪ Fin edges)
          (dummy : Fin (edgeCapacity e edges seeds) → SiteShape e N A)
          (first : Fin D × Bool) (hist : Counts e N bin perm) geo c,
          SourceData e N bin perm positive old rows seed dummy first hist (Sum.elim (sf.eval geo) c) →
            Result e N bin perm positive old rows seed dummy first hist (Sum.elim (sf.eval geo) c)
              (f.eval (Sum.elim geo c)) := by
  obtain ⟨C,k,frames⟩ := batchRow_frames enum pat e S
  refine ⟨C,k,?_⟩
  intro d hd copies sites edges seeds w home seed hs he B
  obtain ⟨sf,hgeo,hsize⟩ := frames d hd copies sites seeds home
  obtain ⟨wire,hw,hout⟩ := Successor.exists_frame e B sites edges w seed hs he
  refine ⟨sf,wire.subst (preparedSource e sf),hgeo,?_,?_⟩
  · rw [Frame.subst_size,preparedSource_size]
    exact Nat.add_le_add hsize hw
  · intro N bin perm positive old rows dummy first hist geo c src
    have hv : (wire.subst (preparedSource e sf)).eval (Sum.elim geo c) = wire.eval (Sum.elim (sf.eval geo) c) := by
      funext j; rw [Frame.subst_eval,preparedSource_eval]
    rw [hv]
    exact hout N bin perm positive old rows dummy first hist _ src

/-- Reindex the row's product-address wires to the factor order used by the
oriented segment reader. The finite successor tag is already the same type. -/
def segmentField (enum : Fin q ≃ I) (S : Finset (HyperbolicHost I)) {l lev : ℕ} (hl : lev+1=l) :
    FieldBit (↥S) I (lev+1) → ProductSlots q l ⊕ ↥S :=
  Sum.elim Sum.inr (fun s => .inl (enum.symm s.1,hl ▸ s.2))

omit [NeZero D] in
/-- The actual quotient encoding from the site serializer agrees bit by bit
with the canonical payload expected by the sparse endpoint type join. -/
theorem quotientRow_siteBits (enum : Fin q ≃ Cube D) (S : Finset (HyperbolicHost (Cube D)))
    {l lev : ℕ} (hl : lev+1=l) (x : SurfaceHost (Cube D) (lev+1)) (hx : relative lev x ∈ S) :
    quotientRow enum S lev hl x ∘ segmentField enum S hl = siteBits x hx := by
  subst l
  funext j
  rcases j with t | ⟨i,j⟩
  · apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,segmentField,Sum.elim_inl,quotientRow,siteBits,
      Sum.elim_inr,decide_eq_true_eq,Subtype.ext_iff]
  · simp only [Function.comp_apply,segmentField,Sum.elim_inr,quotientRow,Sum.elim_inl,
      productWires,Equiv.apply_symm_apply,siteBits]

end Shortening.PublicRelative

end BorderVNP
end Computability
end OAI
