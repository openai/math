import OAI.Computability.BorderVNP.ShortenPublicSegmentStage
import OAI.Computability.BorderVNP.ShortenPublicPopulationJoint
import OAI.Computability.BorderVNP.ShortenPublicPopulationMovedRows

/-!
# The exact moved histogram from the named geometric network

One public circuit reads the stable source/destination identifiers, recovers
actual shortest oriented types, applies the selected common whole-pack motions,
and returns the integer allocator population at every legal geometric seed.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicSegments

open Cover Cover.Frame Cover.AddressCircuit Epoch Catalog Crossing Packing PreparedBins PackMotions
open PublicPopulation Hecke
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

variable {D q n copies V E k w : ℕ} {Data M : Type*} [Fintype Data] [Fintype M] [DecidableEq M]
variable {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ} (B : PreparedBins D S h η)
variable (enum : Fin q ≃ Cube D) (perm : M → Equiv.Perm (Cube D))
variable (word : M → ProductSample (lattice 1) elliptic (Cube D) n)

private noncomputable def withMotion {l : ℕ}
    (g : Frame (Raw Data V E k w) (Classified Data (↥B.types) V E k w)) :
    Frame (Motion M q l copies ⊕ Raw Data V E k w)
      (Motion M q l copies ⊕ Classified Data (↥B.types) V E k w) :=
  parallelFrame (Frame.initial Sum.inl) (g.subst (Frame.initial Sum.inr))

omit [DecidableEq M] in
private theorem withMotion_eval {l : ℕ} (g : Frame (Raw Data V E k w) (Classified Data (↥B.types) V E k w))
    (b : Motion M q l copies → Bool) (x : Raw Data V E k w → Bool) :
    (withMotion B g).eval (Sum.elim b x) = Sum.elim b (g.eval x) := by
  have get : (Frame.initial (Sum.inr : Raw Data V E k w → Motion M q l copies ⊕ Raw Data V E k w)).eval
      (Sum.elim b x) = x := funext fun _ => by simp
  funext j
  cases j <;> simp [withMotion,Frame.subst_eval,get]

/-- Physical meaning of the live fields, moved bin addresses and bin counts
emitted by a stage. The joint lifts are chosen before the pack motion bank. -/
def HistogramRows {d : ℕ} (hd : 1 ≤ d)
    (field : FieldBit (↥S) (Cube D) (d+2*n+2*n) → Data) (home : Fin E → Fin copies)
    (f : Frame (Motion M q (d+2*n) copies ⊕ Raw Data V E k w)
      (Classified Data (↥B.types) V E k w ⊕
        ((Fin E × (ProductSlots q (d+2*n) ⊕ B.Bin)) ⊕ (((Cube D → Deck (d+2*n)) × B.Bin) × Fin w)))) : Prop :=
  ∀ {P : Type} {bits : P → ℕ} {K : Type*} (input : Fin copies → Pack D P bits K)
    (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) (d+2*n+2*n))
    (valid : ∀ i v, relativeAt _ (by omega) (sites i v) ∈ S)
    (charged : ∀ i, (input i).layout.Edge → Bool)
    (site : (parallelPacks input).layout.Site ↪ Fin V) (rows : (parallelPacks input).layout.Edge ↪ Fin E)
    (dummy : Fin E → (parallelPacks input).layout.Site) (x : Raw Data V E k w → Bool),
    (∀ e, home (rows e) = e.1) →
    PublicEndpoints.Represents (parallelPacks input).layout site rows dummy (x ∘ Sum.inr) →
    (∀ (v : (parallelPacks input).layout.Site) j, x (.inr (.inl (site v,field j))) =
      siteAtBits (by omega) (sites v.1 v.2) (valid _ _) j) →
    (∀ e : (parallelPacks input).layout.Edge, x (.inl (rows e)) = charged e.1 e.2) →
    (∀ i e, charged i e = true → dist (sites i ((input i).layout.src e))
      (sites i ((input i).layout.dst e)) ≤ 2*h) →
    let active := positiveMask input sites charged
    ∃ L : Labels B input active sites, ∀ (pick : Fin copies → M)
      (shift : Fin copies → Cube D → Deck (d+2*n)),
      let bin := jointTags B perm word input active sites L pick shift
      let run := f.eval (Sum.elim (motionWires enum pick shift) x)
      PhysicalReads B enum (by omega) field input active sites L rows (run ∘ Sum.inl) ∧
      (∀ cable : Active input active, ∃ v, bin ⟨cable.1,cable.2.val⟩ = some v ∧
        ∀ j, run (.inr (.inl (rows ⟨cable.1,cable.2.val⟩,j))) = PublicMovedBin.binWires B enum v j) ∧
      ((∀ z, SeedIntervals.count (parallelPacks input).layout bin z < 2^w) → ∀ z,
        ParseBatchSort.value (fun j => run (.inr (.inr (z,j)))) =
          SeedIntervals.count (parallelPacks input).layout bin z)

set_option maxHeartbeats 1200000 in
/-- Exact aggregate of selected bins, starting with the two actual endpoint IDs
and the site table rather than precomputed cable labels or bin populations. -/
theorem rawHistogram_frames :
    ∃ cut A a C c H b : ℕ, ∀ (d : ℕ) (hd : 1 ≤ d), cut ≤ d+2*n+2*n →
      ∀ (Data : Type*) [Fintype Data] (V E k w copies : ℕ) (_ : V ≤ 2^k)
        (field : FieldBit (↥S) (Cube D) (d+2*n+2*n) → Data) (home : Fin E → Fin copies),
      ∃ f : Frame (Motion M q (d+2*n) copies ⊕ Raw Data V E k w)
        (Classified Data (↥B.types) V E k w ⊕
          ((Fin E × (ProductSlots q (d+2*n) ⊕ B.Bin)) ⊕ (((Cube D → Deck (d+2*n)) × B.Bin) × Fin w))),
        (let v := E + Fintype.card (Cube D → Deck (d+2*n))*Fintype.card B.Bin
         let r := Nat.clog 2 (Fintype.card B.Bin)
         f.size ≤ (300*(V+2*E+1)*(Nat.clog 2 (V+2*E)+k+Fintype.card Data+1)^3 +
           (1+E*(A*(d+2*n+2*n+1)^a+2*Fintype.card B.types+3))) +
           ((1+E*(H*(d+1)^b))+(1+E*(C*(d+1)^c)+(E*r*(2*Fintype.card B.Bin+1)+
             2*(v+1)*laneCost (Nat.clog 2 v) (r+keyWidth q (d+2*n)) w)))) ∧
        HistogramRows B enum perm word hd field home f := by
  obtain ⟨cut,A,a,geom⟩ := reconstruct_frames B enum
  -- A single gate polynomial serves every input wire set and every padded row count.
  obtain ⟨C,c,moves⟩ := joint_frames B enum perm word
  obtain ⟨H,b,placed⟩ := jointRows_frames B enum perm word
  refine ⟨cut,A,a,C,c,H,b,?_⟩
  intro d hd hcut Data inst V E k w copies fit field home
  obtain ⟨g,gs,rg⟩ := geom _ (by omega) hcut Data V E k w fit field
  let pins := jointPins (V := V) (k := k) (w := w) B enum home field (M := M)
  obtain ⟨hist,hs,hm⟩ := moves d hd w copies pins
  obtain ⟨emit,em,he⟩ := placed d hd w copies pins
  let out := parallelFrame (Frame.initial Sum.inr) (parallelFrame emit hist)
  refine ⟨out.subst (withMotion B g),?_,?_⟩
  · simp only [out,Frame.subst_size,withMotion,parallelFrame_size,Frame.initial_size,zero_add]
    exact Nat.add_le_add gs (by simpa only [Fintype.card_fin] using Nat.add_le_add em hs)
  · intro P bits K input sites valid charged site rows dummy x owner names data mask short active
    obtain ⟨L,read⟩ := rg input sites valid charged site rows dummy x names data mask short
    refine ⟨L,?_⟩
    intro pick shift bin run
    let y := Sum.elim (motionWires enum pick shift) (g.eval x)
    have reads := jointReads_of_physical B enum home field input active sites L rows owner (g.eval x) hd read pick shift
    have state : run ∘ Sum.inl = g.eval x := by
      funext j
      simp [run,out,Frame.subst_eval,withMotion_eval]
    refine ⟨state.symm ▸ read,?_,?_⟩
    · intro cable
      obtain ⟨v,hv,encoded⟩ := he input active sites L rows pick shift y reads cable
      exact ⟨v,hv,fun j => by
        simpa only [run,Frame.subst_eval,withMotion_eval,out,parallelFrame_eval_inr,parallelFrame_eval_inl,y]
          using encoded j⟩
    · intro fits z
      have histOK := hm input active sites L rows pick shift y reads fits z
      simpa only [run,out,Frame.subst_eval,withMotion_eval,parallelFrame_eval_inr,y] using histOK

end Shortening.PublicSegments

end BorderVNP
end Computability
end OAI
