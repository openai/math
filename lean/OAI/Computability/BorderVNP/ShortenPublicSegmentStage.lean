import OAI.Computability.BorderVNP.ShortenPublicSegmentPhysical

/-!
# Depth-uniform reconstruction of the geometric histogram input

The circuit first receives ordinary stable site/cable arrays. Its outputs
can feed every candidate histogram before the selector, and the chosen-motion
histogram after the selector, by wiring the shared per-pack motion bank.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicSegments

open Cover Cover.AddressCircuit Epoch Catalog Crossing Packing PreparedBins PackMotions PublicPopulation
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

variable {D q V E k w copies l n d : ℕ} {Data M : Type*}
variable {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ} (B : PreparedBins D S h η)
variable (enum : Fin q ≃ Cube D)

/-- Catalogued relative point at an arbitrary positive depth. -/
noncomputable def relativeAt {I : Type*} : (z : ℕ) → 0 < z → SurfaceHost I z → HyperbolicHost I
  | 0, h, _ => False.elim (Nat.lt_irrefl 0 h)
  | z+1, _, x => relative z x

/-- The concrete public encoding of a quotient site at any positive depth. -/
noncomputable def siteAtBits {l : ℕ} (hl : 0 < l) (x : SurfaceHost (Cube D) l)
    (hx : relativeAt l hl x ∈ S) : FieldBit (↥S) (Cube D) l → Bool :=
  Sum.elim (fun u => decide (u=(⟨relativeAt l hl x,hx⟩ : ↥S)))
    (fun z => deckWires l (addressAt l hl (x z.1)) z.2)

/-- Semantics of the raw stable-name processor at one physical depth. -/
def Reconstructs [Fintype Data] (hl : 0 < l) (field : FieldBit (↥S) (Cube D) l → Data)
    (g : Frame (Raw Data V E k w) (Classified Data (↥B.types) V E k w)) : Prop :=
  ∀ {copies : ℕ} {P : Type} {bits : P → ℕ} {K : Type*} (input : Fin copies → Pack D P bits K)
    (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) l)
    (valid : ∀ i v, relativeAt l hl (sites i v) ∈ S) (charged : ∀ i, (input i).layout.Edge → Bool)
    (site : (parallelPacks input).layout.Site ↪ Fin V) (rows : (parallelPacks input).layout.Edge ↪ Fin E)
    (dummy : Fin E → (parallelPacks input).layout.Site) (x : Raw Data V E k w → Bool),
    PublicEndpoints.Represents (parallelPacks input).layout site rows dummy (x ∘ Sum.inr) →
    (∀ (v : (parallelPacks input).layout.Site) j, x (.inr (.inl (site v,field j))) =
      siteAtBits hl (sites v.1 v.2) (valid _ _) j) →
    (∀ e : (parallelPacks input).layout.Edge, x (.inl (rows e)) = charged e.1 e.2) →
    (∀ i e, charged i e = true → dist (sites i ((input i).layout.src e)) (sites i ((input i).layout.dst e)) ≤ 2*h) →
    ∃ L : Labels B input (positiveMask input sites charged) sites, PhysicalReads B enum hl field input
      (positiveMask input sites charged) sites L rows (g.eval x)

/-- Uniform public reader for raw named cables at any deep input level. -/
theorem reconstruct_frames :
    ∃ cut C e : ℕ, ∀ (l : ℕ) (hl : 0 < l), cut ≤ l → ∀ (Data : Type*) [Fintype Data]
      (V E k w : ℕ) (_ : V ≤ 2^k) (field : FieldBit (↥S) (Cube D) l → Data),
      ∃ g : Frame (Raw Data V E k w) (Classified Data (↥B.types) V E k w),
        g.size ≤ 300*(V+2*E+1)*(Nat.clog 2 (V+2*E)+k+Fintype.card Data+1)^3 +
          (1+E*(C*(l+1)^e+2*Fintype.card B.types+3)) ∧ Reconstructs B enum hl field g := by
  obtain ⟨cut,C,e,rows⟩ := totalTypeRow_frames B
  refine ⟨cut,C,e,?_⟩
  intro l hl hc Data inst V E k w fit field
  cases l with
  | zero => omega
  | succ z =>
    obtain ⟨f,hf,row⟩ := rows z hc
    obtain ⟨g,gs,sem⟩ := physical_batch B enum (E := E) (w := w) field row fit
    refine ⟨g,gs.trans ?_,sem⟩
    gcongr

/-- Per-pack candidate and shift bank. -/
abbrev Motion (M : Type*) (q l copies : ℕ) := Fin copies × (M ⊕ ProductSlots q l)

/-- Real data pins for the histogram, with the selection bank on the left and
the reconstructed public rows on the right. -/
def jointPins (home : Fin E → Fin copies) (field : FieldBit (↥S) (Cube D) (d+2*n+2*n) → Data) :
    JointPins (↥B.types) M (Fin E)
      (Motion M q (d+2*n) copies ⊕ Classified Data (↥B.types) V E k w)
      q (d+2*n) (d+2*n+2*n) w copies where
  home := home
  live i := .inr (.inr (i,.inl ()))
  width i j := .inr (widthPin i j)
  kind i t := .inr (.inr (i,.inr t))
  source i j := .inr (sourcePin enum field i j)
  choice i m := .inl (i,.inl m)
  shift i j := .inl (i,.inr j)

/-- Encoded outputs of the common per-pack choice and translation. -/
def motionWires [DecidableEq M] (pick : Fin copies → M) (shift : Fin copies → Cube D → Deck l) :
    Motion M q l copies → Bool := fun z =>
  z.2.elim (fun m => decide (m=pick z.1)) (productWires l (shift z.1 ∘ enum))

/-- A single recovered set of geometric labels feeds all choices of the
motion bank, without redoing a site lookup or a shortest-lift search. -/
theorem jointReads_of_physical [DecidableEq M] {P : Type} {bits : P → ℕ} {K : Type*}
    (home : Fin E → Fin copies) (field : FieldBit (↥S) (Cube D) (d+2*n+2*n) → Data)
    (input : Fin copies → Pack D P bits K) (active : ∀ i, (input i).layout.Edge → Bool)
    (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) (d+2*n+2*n))
    (L : Labels B input active sites) (rows : (parallelPacks input).layout.Edge ↪ Fin E)
    (owner : ∀ e, home (rows e) = e.1) (y : Classified Data (↥B.types) V E k w → Bool)
    (hd : 1 ≤ d) (physical : PhysicalReads B enum (by omega) field input active sites L rows y)
    (pick : Fin copies → M) (shift : Fin copies → Cube D → Deck (d+2*n)) :
    JointReads B enum (jointPins B enum home field) input active sites L rows pick shift
      (Sum.elim (motionWires enum pick shift) y) hd :=
  ⟨owner,physical.live,physical.empty,physical.widths,physical.kinds,physical.sources,
    fun _ => rfl,fun _ => rfl⟩

end Shortening.PublicSegments

end BorderVNP
end Computability
end OAI
