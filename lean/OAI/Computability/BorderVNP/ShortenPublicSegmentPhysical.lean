import OAI.Computability.BorderVNP.ShortenPublicSegmentJoin
import OAI.Computability.BorderVNP.ShortenPublicPopulationInput

/-!
# Public reconstruction for a family of physically placed packs

Following stable endpoint names once yields all four inputs of the moved-row
histogram: exact positive charge, width, the selected oriented type and the
source tile. Padded cables read their own dummy site at both ends and are
inactive irrespective of their saved flag.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicSegments

open Cover Cover.AddressCircuit Epoch Catalog Crossing Packing PreparedBins PackMotions
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

variable {D copies q V E k w d : ℕ} {Data : Type*} [Fintype Data]
variable {P : Type} {bits : P → ℕ} {K : Type*}
variable {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ} (B : PreparedBins D S h η)
variable (enum : Fin q ≃ Cube D)

/-- The positive part of the old geometric charge flag. -/
noncomputable def positiveMask {l : ℕ} (input : Fin copies → Pack D P bits K)
    (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) l)
    (charged : ∀ i, (input i).layout.Edge → Bool) (i : Fin copies) (e : (input i).layout.Edge) : Bool :=
  charged i e && decide (sites i ((input i).layout.src e) ≠ sites i ((input i).layout.dst e))

/-- Width read from the cable record after the shared endpoint join. -/
def widthPin {T : Type*} (i : Fin E) (j : Fin w) : Classified Data T V E k w :=
  .inl (.inr (.inl (.inr (i,.inl j))))

/-- Tile of the joined source endpoint in the public factor ordering. -/
def sourcePin {T : Type*} {l : ℕ} (field : FieldBit (↥S) (Cube D) l → Data)
    (i : Fin E) (j : ProductSlots q l) : Classified Data T V E k w :=
  .inl (pairAt field i (true,.inr (enum j.1,j.2)))

/-- The geometric fields of a reconstructed batch, valid for all occupied
and reserved physical cable names in a common array. -/
structure PhysicalReads {l : ℕ} (hl : 0 < l) (field : FieldBit (↥S) (Cube D) l → Data)
    (input : Fin copies → Pack D P bits K) (active : ∀ i, (input i).layout.Edge → Bool)
    (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) l) (L : Labels B input active sites)
    (rows : (parallelPacks input).layout.Edge ↪ Fin E) (y : Classified Data (↥B.types) V E k w → Bool) : Prop where
  /-- The enable wire agrees with the physical positive charge. -/
  live : ∀ e, y (.inr (rows e,.inl ())) = active e.1 e.2
  /-- An unused padded row has zero charge. -/
  empty : ∀ u, u ∉ Set.range rows → y (.inr (u,.inl ())) = false
  /-- The stored width is the old cable width. -/
  widths : ∀ z : Active input active, ParseBatchSort.value (y ∘ widthPin (rows ⟨z.1,z.2.val⟩)) =
    (input z.1).layout.width z.2.val
  /-- The chosen type belongs to the same joint geometric lift used in the shortening step. -/
  kinds : ∀ z : Active input active, (fun t => y (.inr (rows ⟨z.1,z.2.val⟩,.inr t))) = fun t => decide (t=L.kind z)
  /-- The true source tile of the occupied cable is forwarded in its canonical wire encoding. -/
  sources : ∀ z : Active input active, y ∘ sourcePin enum field (rows ⟨z.1,z.2.val⟩) = productWires l
    (fun j => addressAt l hl ((sites z.1 ((input z.1).layout.src z.2.val)) (enum j)))

set_option maxHeartbeats 1200000 in
/-- The circuit precedes the choice of physical inputs, layout, field coefficients,
charged subset, placement, and cable widths. The linear number of padded rows is
multiplied only by the per-row table cost and the shared join's polylog overhead. -/
theorem physical_batch (field : FieldBit (↥S) (Cube D) (d+1) → Data)
    {f : Frame (Bool × FieldBit (↥S) (Cube D) (d+1)) B.types} (row : TypeRow B d f) (fit : V ≤ 2^k) :
    ∃ g : Frame (Raw Data V E k w) (Classified Data (↥B.types) V E k w),
      g.size ≤ 300*(V+2*E+1)*(Nat.clog 2 (V+2*E)+k+Fintype.card Data+1)^3 +
        (1+E*(f.size+2*Fintype.card B.types+3)) ∧
      ∀ {copies : ℕ} {P : Type} {bits : P → ℕ} {K : Type*} (input : Fin copies → Pack D P bits K)
        (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) (d+1))
        (valid : ∀ i v, relative d (sites i v) ∈ S) (charged : ∀ i, (input i).layout.Edge → Bool)
        (site : (parallelPacks input).layout.Site ↪ Fin V) (rows : (parallelPacks input).layout.Edge ↪ Fin E)
        (dummy : Fin E → (parallelPacks input).layout.Site) (x : Raw Data V E k w → Bool),
        PublicEndpoints.Represents (parallelPacks input).layout site rows dummy (x ∘ Sum.inr) →
        (∀ (v : (parallelPacks input).layout.Site) j, x (.inr (.inl (site v,field j))) =
          siteBits (sites v.1 v.2) (valid _ _) j) →
        (∀ e : (parallelPacks input).layout.Edge, x (.inl (rows e)) = charged e.1 e.2) →
        (∀ i e, charged i e = true → dist (sites i ((input i).layout.src e))
          (sites i ((input i).layout.dst e)) ≤ 2*h) →
        let active := positiveMask input sites charged
        ∃ L : Labels B input active sites, PhysicalReads B enum (Nat.zero_lt_succ d) field input active sites L rows
          (g.eval x) := by
  obtain ⟨g,gs,read⟩ := batch_frames (w := w) (E := E) field f fit
  refine ⟨g,gs,?_⟩
  intro copies P bits K input sites valid charged site rows dummy x names payload mask short active
  let N := (parallelPacks input).layout
  let pos (v : N.Site) := sites v.1 v.2
  let hc (v : N.Site) := valid v.1 v.2
  let y := (expand Data w fit).eval x
  have hh := read x
  have occupied (e : N.Edge) : y ∘ pairAt field (rows e) = cableBits input sites valid e.1 e.2 :=
    expanded_occupied N site rows dummy pos hc field x fit names payload e
  have empty (i : Fin E) (hi : i ∉ Set.range rows) :
      y ∘ pairAt field i = endpointBits (pos (dummy (Names.rowSlot i))) (pos (dummy (Names.rowSlot i))) (hc _) (hc _) :=
    expanded_unused N site rows dummy pos hc field x fit names payload i hi
  have test (z : Active input active) := z.2.property
  simp only [active,positiveMask,Bool.and_eq_true,decide_eq_true_eq] at test
  obtain ⟨L,tags⟩ := labels_of_typeRow B input active sites valid row (fun z => (test z).2)
    (fun z => short _ _ (test z).1)
  refine ⟨L,?_,?_,?_,?_,?_⟩
  · intro e
    rw [hh.2,occupied e,mask e]
    apply Bool.eq_iff_iff.mpr
    rw [markRow_enabled]
    constructor
    · rintro ⟨ch,t,ht⟩
      have hn : sites e.1 ((input e.1).layout.src e.2) ≠ sites e.1 ((input e.1).layout.dst e.2) := by
        intro he
        have hz : f.eval (cableBits input sites valid e.1 e.2) = fun _ => false := by
          have zero (a b : SurfaceHost (Cube D) (d+1)) (ha : relative d a ∈ S) (hb : relative d b ∈ S)
              (eq : a=b) : f.eval (endpointBits a b ha hb) = fun _ => false := by
            subst b
            exact row.1 _ _
          exact zero _ _ _ _ he
        simp [hz] at ht
      simp [active,positiveMask,ch,hn]
    · intro ha
      let z : Active input active := ⟨e.1,e.2,ha⟩
      refine ⟨(test z).1,L.kind z,?_⟩
      exact (congrFun (tags z) (L.kind z)).trans (by simp)
  · intro u hu
    rw [hh.2,empty u hu]
    apply Bool.eq_false_iff.mpr
    intro hLive
    obtain ⟨_,t,ht⟩ := (markRow_enabled _ _ _).mp hLive
    simp [row.1] at ht
  · intro z
    let e : N.Edge := ⟨z.1,z.2.val⟩
    have hj := PublicEndpoints.join_occupied N site rows dummy fit names e
    have hw (j : Fin w) : g.eval x (widthPin (rows e) j) =
        (PublicEndpoints.join Data w fit).eval (x ∘ Sum.inr) (.inl (.inr (rows e,.inl j))) :=
      (hh.1 _).trans (expand_join fit x _)
    exact (congrArg ParseBatchSort.value (funext hw)).trans hj.2.2
  · intro z
    let e : N.Edge := ⟨z.1,z.2.val⟩
    funext t
    exact ((hh.2 (rows e) (.inr t)).trans (markRow_tag f _ _ t)).trans
      ((congrFun (congrArg f.eval (occupied e)) t).trans (congrFun (tags z) t))
  · intro z
    let e : N.Edge := ⟨z.1,z.2.val⟩
    funext j
    exact (hh.1 _).trans (congrFun (occupied e) (true,.inr (enum j.1,j.2)))

end Shortening.PublicSegments

end BorderVNP
end Computability
end OAI
