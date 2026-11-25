import OAI.Computability.BorderVNP.ShortenPublicPackFrontRead
import OAI.Computability.BorderVNP.ShortenCalibratedPhysicalWidth

/-!
# Selecting one complete geometric pack motion from the predecessor records

Occupied child tables enter separately. The circuit merges their pointers,
classifies the physical rows, evaluates all exact candidate histograms and
decodes the selected forward translations. It retains the merged table and
the classification for the site mover and the cut-directory serializer.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicRelative

open PublicSegments PublicParallel Cover Cover.Frame Cover.AddressCircuit Epoch PreparedBins Crossing Packing
open Hecke PackMotions Framed PublicDirectory
open VPVNP.VerifierNetwork (Frame)
open scoped Classical BorderVNP.Epoch.Cube

universe u
variable {D n N : ℕ} {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ} (B : PreparedBins D S h η)

/-- Uniform coefficients for row reconstruction, candidate histograms,
exact selection and the forward quaternion correction. -/
structure FrontCosts where
  /-- Shared per-row reconstruction coefficient. -/
  reader : ℕ
  /-- Degree of the reconstruction depth bound. -/
  readerDegree : ℕ
  /-- Coefficient for the candidate histogram circuits. -/
  histogram : ℕ
  /-- Degree of the histogram word-size bound. -/
  histogramDegree : ℕ
  /-- Coefficient for the complete pack selector. -/
  selector : ℕ
  /-- Degree of the selector depth and word-size bound. -/
  selectorDegree : ℕ
  /-- Coefficient for the pullback-to-forward motion correction. -/
  inverse : ℕ
  /-- Degree of the inverse address calculation. -/
  inverseDegree : ℕ

/-- Gate budget on one node with original and merged tables. The two physical
volumes below count sites/cables in the merged layout and product-cover tiles. -/
def FrontCosts.bound (a : FrontCosts) (k V E w data kinds q l n vol T : ℕ) :=
  let rows := k*E
  let sites := k*V
  let merge := 1+rows*600*(w+1)^2
  let reader := 300*(sites+2*rows+1)*(Nat.clog 2 (sites+2*rows)+w+data+1)^3 +
    (1+rows*(a.reader*(l+2*n+1)^a.readerDegree+2*kinds+3))
  let hist := 1+(rows+k*(vol+1))*a.histogram*(Nat.clog 2 (T+vol+2)+1)^a.histogramDegree
  let select := 1+k*(vol*a.selector*(l+w+1)^a.selectorDegree)
  let inverse := 1+k*(1+q*a.inverse*(l+1)^a.inverseDegree)
  merge+(reader+((hist+select)+inverse))

/-- Wires used to identify the selector's exact finite pre-motion candidate. -/
noncomputable abbrev FrontCandidate (D n : ℕ) :=
  Fin (Fintype.card (PackedDeckMean.MotionCandidate (lattice 1) elliptic (Cube D) n))

private def forwardAt {X M : Type*} [Fintype X] [Fintype M] {q a b k : ℕ} (level : a=b)
    (f : Frame X (Motion M q a k)) : Frame X (Motion M q b k) := level ▸ f

private theorem forwardAt_size {X M : Type*} [Fintype X] [Fintype M] {q a b k : ℕ} (level : a=b)
    (f : Frame X (Motion M q a k)) : (forwardAt level f).size = f.size := by cases level; rfl

private theorem forwardAt_eval {X M : Type*} [Fintype X] [Fintype M] [DecidableEq M]
    {q a b k : ℕ} (enum : Fin q ≃ Cube D) (level : a=b) (f : Frame X (Motion M q a k)) (x : X → Bool)
    (pick : Fin k → M) (shift : Fin k → Cube D → Deck a) (he : f.eval x = motionWires enum pick shift) :
    (forwardAt level f).eval x = motionWires enum pick (fun i j => deckCast level (shift i j)) := by
  cases level
  exact he

/-- The actual saved public rows, common recovered labels, and decoded
geometric sample witnessed by a front-end circuit's outputs. -/
def SelectedFrontReads {d r k V E w : ℕ} (level : d+1=r+2*n) (hk : 0<k)
    {Data : Type*} (field : FieldBit (↥S) (Cube D) (d+2*n+1) → Data)
    {Port : Type} {bits : Port → ℕ} {K : Type u} (child : Fin k → PlacedPack D Port bits K (Cube D) (d+2*n))
    (sites : ∀ i, (child i).pack.layout.Site ↪ Fin V) (rows : ∀ i, (child i).pack.layout.Edge ↪ Fin E)
    (dummy : ∀ i, Fin E → (child i).pack.layout.Site)
    (y : Source Data (↥B.types) (FrontCandidate D n) (Fintype.card (Cube D)) (r+2*n) k (k*V) (k*E) w → Bool) (N : ℕ) : Prop :=
  let input := fun i => (child i).pack
  ∃ (occ : Fin (k*E) → Bool) (raw : Raw Data (k*V) (k*E) w w → Bool)
    (cls : Classified Data (↥B.types) (k*V) (k*E) w w → Bool)
    (L : Labels B input (fun i => (child i).active) (childSites child))
    (ω : Fin k → PackSample (lattice 1) elliptic (Cube D) (d+1) n),
    (∀ j, occ j = true ↔ j ∈ Set.range (parallelName rows)) ∧
    SegmentReady S (parallelPacks input).layout (parallelName sites) (parallelName rows) (parallelDummy dummy)
      (fun v => (child v.1).site v.2) field (fun a => (child a.1).charged a.2) raw ∧
    PhysicalReads B (factorEnum D) (by omega) (fieldAtLevel (Nat.add_right_comm d (2*n) 1) field)
      input (fun i => (child i).active) (childSites child) L (parallelName rows) cls ∧
    B.SampleDeviation child L ω hk N ∧
    y = Sum.elim (Sum.elim occ raw) (Sum.elim (motionWires (factorEnum D) (fun i => sampledChoice (candidateEnum D n) (ω i))
      (fun i j => deckCast level ((ω i).2.2 j))) cls)

/-- A complete selected physical front end for a node of the public combining
tree. All cutoffs and cost coefficients precede the depth, fan-in, table shape
and valuation. Every real cable and the same selected geometric motion feed
both the successor site table and the cut-directory stage. -/
theorem selectedFront_frames (compiled : CompiledAt.{u} B n N) :
    ∃ P cut : ℕ, ∃ cost : FrontCosts, 0 < P ∧ ∀ (d r k : ℕ) (_ : 0<d) (_ : 1≤r) (level : d+1=r+2*n)
      (hk : 0<k) (_ : cut ≤ d+1+2*n) {Data : Type*} [Fintype Data] (V E H w : ℕ)
      (field : FieldBit (↥S) (Cube D) (d+2*n+1) → Data),
      let vol := Fintype.card (Cube D → Deck (d+1))
      P < 2^w → H < 2^w → packRunWidth vol P k H ≤ w → k*V ≤ 2^w →
      ∃ f : Frame (Fin k × (Fin E ⊕ Raw Data V E w w))
        (Source Data (↥B.types) (FrontCandidate D n) (Fintype.card (Cube D)) (r+2*n) k (k*V) (k*E) w),
        (∀ T, k*E ≤ T → w ≤ Nat.clog 2 (T+1) →
          f.size ≤ cost.bound k V E w (Fintype.card Data) (Fintype.card B.types) (Fintype.card (Cube D)) (d+1) n vol T) ∧
        ∀ {Port : Type} {bits : Port → ℕ} {K : Type u} (child : Fin k → PlacedPack D Port bits K (Cube D) (d+2*n))
          (sites : ∀ i, (child i).pack.layout.Site ↪ Fin V) (rows : ∀ i, (child i).pack.layout.Edge ↪ Fin E)
          (dummy : ∀ i, Fin E → (child i).pack.layout.Site) (x : Fin k × (Fin E ⊕ Raw Data V E w w) → Bool),
          (∀ i j, x (i,.inl j) = true ↔ j ∈ Set.range (rows i)) →
          (∀ i, SegmentReady S (child i).pack.layout (sites i) (rows i) (dummy i) (child i).site field
            (child i).charged (fun j => x (i,.inr j))) →
          (∀ i a, (child i).charged a = true →
            dist ((child i).site ((child i).pack.layout.src a)) ((child i).site ((child i).pack.layout.dst a)) ≤ 2*h) →
          (∀ i a, (child i).active a = true → dist ((child i).midpoint a) ((child i).site ((child i).pack.layout.src a)) ≤
            dist ((child i).site ((child i).pack.layout.src a)) ((child i).site ((child i).pack.layout.dst a))/2) →
          (∀ i, (∑ a, (child i).pack.layout.width a) ≤ H) →
          SelectedFrontReads B level hk field child sites rows dummy (f.eval x) N := by
  obtain ⟨cut,R,t,reconstruct⟩ := reconstruct_frames B (factorEnum D)
  obtain ⟨P,A,p,C,e,hP,select⟩ := classifiedTraceAtWidth_frames B compiled
  obtain ⟨F,b,forward⟩ := traceMotion_frames
  let cost : FrontCosts := ⟨R,t,A,p,C,e,F,b⟩
  refine ⟨P,cut,cost,hP,?_⟩
  intro d r k hd hr level hk hc Data instData V E H w field vol den room fits hV
  let deep := fieldAtLevel (Nat.add_right_comm d (2*n) 1) field
  let home := fun j : Fin (k*E) => (finProdFinEquiv.symm j).1
  obtain ⟨merge,hm,hmerge⟩ := merge_frames Data k V E w
  obtain ⟨reader,hrd,read⟩ := reconstruct (d+1+2*n) (by omega) hc Data (k*V) (k*E) w w hV deep
  obtain ⟨table,selector,hsel,run⟩ := select d r k hd hr level hk (k*V) (k*E) w H w home deep den room fits
  obtain ⟨inverse,hinv,inv⟩ := forward (factorEnum D) B.Bin (d+1) _ w k
  let choose := selector.subst table
  let move := forwardAt level (inverse.subst choose)
  let f := frontWires (occupiedMerge merge) reader move
  refine ⟨f,?_,?_⟩
  · intro T he hw
    simp only [f,frontWires_size,occupiedMerge_size,move,forwardAt_size,Frame.subst_size]
    exact Nat.add_le_add hm (Nat.add_le_add hrd (Nat.add_le_add (hsel T he hw) hinv))
  · intro Port bits K child sites rows dummy x occupied children short midpoint cap
    let saved := (occupiedMerge merge).eval x
    let occ := saved ∘ Sum.inl
    let raw := saved ∘ Sum.inr
    have hraw : raw = merge.eval (fun z => x (z.1,.inr z.2)) := occupiedMerge_raw merge x
    have ready := merge_ready (fun i => (child i).pack) sites rows dummy (fun i => (child i).site)
      field (fun i => (child i).charged) (fun i j => x (i,.inr j)) children hV hmerge
    rw [← hraw] at ready
    obtain ⟨L,physical⟩ := frontChildRead B child sites rows dummy field raw ready short reader read
    let cls := reader.eval raw
    obtain ⟨⟨pick,pull,flags,keys,_,dev⟩,wire⟩ := run child L midpoint (parallelName rows)
      (parallelName_owner rows) cls physical cap
    let ω := fun i => deckSample (factorEnum D) (candidateEnum D n) (pick i,pull i)
    have output : (inverse.subst choose).eval cls =
        motionWires (factorEnum D) pick (fun i => (pull i ∘ (factorEnum D).symm)⁻¹) := by
      rw [funext (Frame.subst_eval inverse choose cls),wire]
      exact inv _ pick pull flags keys
    have moved := forwardAt_eval (factorEnum D) level (inverse.subst choose) cls pick
      (fun i => (pull i ∘ (factorEnum D).symm)⁻¹) output
    rw [← deckSample_motionWires (factorEnum D) (candidateEnum D n) level pick pull] at moved
    refine ⟨occ,raw,cls,L,ω,occupiedMerge_occupied merge x rows occupied,ready,physical,dev,?_⟩
    have savedBits : saved = Sum.elim occ raw := funext fun j => by cases j <;> rfl
    apply (frontWires_eval (occupiedMerge merge) reader move x).trans
    rw [← savedBits]
    exact congrArg (fun z => Sum.elim saved (Sum.elim z cls)) moved

end Shortening.PublicRelative

end BorderVNP
end Computability
end OAI
