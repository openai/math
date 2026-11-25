import OAI.Computability.BorderVNP.ShortenPublicDirectoryStage
import OAI.Computability.BorderVNP.ShortenPublicPreBatchSample

/-!
# Shared physical input of the cut directory and the moved site table

The circuit reconstructs the geometric cable labels from the preceding raw
site table. The same per-copy selection drives the numeric cable bins and the
site-placement wires. Only the input occupancy flags are carried separately,
so zero-width live edges remain distinguishable from reserved holes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicRoundInput

open Cover Cover.Frame Cover.AddressCircuit Epoch Crossing Hecke Packing PackMotions PreparedBins
open PublicSegments PublicPopulation PublicRelative Framed PublicDirectory
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

/-- Raw pack input, with its saved occupation flags and selected motion bank. -/
abbrev Inputs (Data M : Type*) (q l copies V E w : ℕ) :=
  (Fin E ⊕ Raw Data V E w w) ⊕ Motion M q l copies

variable {Data M T : Type*} [Fintype Data] [Fintype M] [Fintype T] {q l copies V E w : ℕ}

private noncomputable def cableInput (g : Frame (Raw Data V E w w) (Classified Data T V E w w)) :
    Frame (Inputs Data M q l copies V E w) (Source Data T M q l copies V E w) :=
  let old := Frame.initial (Sum.inl ∘ Sum.inr)
  parallelFrame (Frame.initial Sum.inl) (parallelFrame (Frame.initial Sum.inr) (g.subst old))

private theorem cableInput_eval (g : Frame (Raw Data V E w w) (Classified Data T V E w w))
    (occ : Fin E → Bool) (raw : Raw Data V E w w → Bool) (motion : Motion M q l copies → Bool) :
    (cableInput g).eval (Sum.elim (Sum.elim occ raw) motion) = Sum.elim (Sum.elim occ raw) (Sum.elim motion (g.eval raw)) := by
  have read : (Frame.initial (Sum.inl ∘ Sum.inr : Raw Data V E w w → Inputs Data M q l copies V E w)).eval
      (Sum.elim (Sum.elim occ raw) motion) = raw := funext fun _ => by simp
  funext j
  rcases j with j | (j | j) <;> simp [cableInput,Frame.subst_eval,read]

variable {D n m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ}
variable (B : PreparedBins D S h η) (enum : Fin q ≃ Cube D)
variable {Candidates : Type} [Fintype Candidates] [DecidableEq Candidates]
variable (index : Candidates ≃ PackedDeckMean.MotionCandidate (lattice 1) elliptic (Cube D) n)

/-- Read the two site-table operands directly from a shared classified source.
The numeric directory, the candidate bank, and the site mover can all consume
the same set of geometric labels. -/
private def sharedSitePin : PreInput M Data q l copies V E w w → Source Data T M q l copies V E w :=
  Sum.elim (Sum.inr ∘ Sum.inl) (Sum.inl ∘ Sum.inr)

set_option maxHeartbeats 1800000 in
/-- Assemble the numeric cut inputs and site-mover inputs for any already
reconstructed set of geometric labels. In particular, the selector can reuse
the very same labels that were used to score all candidate motions. -/
theorem ready_from_classified_frames :
    ∃ C c : ℕ, ∀ (d : ℕ) (hd : 1 ≤ d) (Data : Type*) [Fintype Data] (V E w copies seeds : ℕ)
      (home : Fin E → Fin copies) (field : FieldBit (↥S) (Cube D) (d+2*n+2*n) → Data)
      (seed : ((Cube D → Deck (d+2*n)) × B.Bin) ≃ Fin seeds),
      let pat := sitePattern (n := n) B
      let Src := Source Data (↥B.types) Candidates q (d+2*n) copies V E w
      let pins := jointPins (V := V) (k := w) (w := w) B enum home field (M := Candidates)
      let r := Nat.clog 2 (Fintype.card B.Bin)
      let k := r+keyWidth q (d+2*n)
      let code := Framed.seedCode (fun t : B.types => t.val.radius) B.chart n
      ∃ f : Frame Src (Table Src E k ⊕ BatchPorts q pat S d copies V seeds),
        f.size ≤ (1+E*(C*(d+1)^c)+E*r*(2*Fintype.card B.Bin+1)+1) +
          seeds*(pat.bins+90*q*(d+2*n+1)) ∧
        ∀ {P : Type} {bits : P → ℕ} (input : Fin copies → Pack D P bits K)
          (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) (d+2*n+2*n))
          (active : ∀ i, (input i).layout.Edge → Bool) (L : Labels B input active sites)
          (oldSite : (parallelPacks input).layout.Site ↪ Fin V) (slot : (parallelPacks input).layout.Edge ↪ Fin E)
          (dummy : Fin E → (parallelPacks input).layout.Site) (occ : Fin E → Bool) (raw : Raw Data V E w w → Bool)
          (y : Classified Data (↥B.types) V E w w → Bool),
          (∀ z, home (slot z) = z.1) → (∀ i, occ i = true ↔ i ∈ Set.range slot) →
          PublicEndpoints.Represents (parallelPacks input).layout oldSite slot dummy (raw ∘ Sum.inr) →
          PhysicalReads B enum (by omega) field input active sites L slot y →
          ∀ (pick : Fin copies → Candidates) (shift : Fin copies → Cube D → Deck (d+2*n)) (sizeBound : ℕ),
            (∑ z, (parallelPacks input).layout.width z) ≤ sizeBound →
            Nat.clog 2 (DirectoryCircuit.widthMultiplier e*sizeBound+1) ≤ w →
            let motion := motionWires enum pick shift
            let run := f.eval (Sum.elim (Sum.elim occ raw) (Sum.elim motion y))
            let bin := jointTags B (fun j => (index j).1) (fun j => (index j).2) input active sites L pick shift
            DirectoryCircuit.Ready e (populationPins (Sum.inr ∘ pins.live) oldField)
              (columns occupied oldField) (addressCode enum (binCode B.Bin)) seed (parallelPacks input)
              bin (fun _ => true) oldSite slot (nextDummy e (parallelPacks input) slot dummy seed) (run ∘ Sum.inl) ∧
            run ∘ Sum.inr = preFields enum pat (candidateIndex B index) field seed code Prod.fst (Sum.elim motion raw) := by
  obtain ⟨C,c,make⟩ := preCable_frames e B enum (fun j => (index j).1) (fun j => (index j).2)
  refine ⟨C,c,?_⟩
  intro d hd Data inst V E w copies seeds home field seed pat Src pins r k code
  obtain ⟨num,ns,_,nr⟩ := make d hd w copies V E home field
  obtain ⟨geo,gs,geoRead⟩ := preBatchPorts_frames enum pat d copies V E w w (candidateIndex B index) field seed code Prod.fst
  let tap : Frame Src (PreInput Candidates Data q (d+2*pat.depth) copies V E w w) := Frame.initial sharedSitePin
  let out := parallelFrame num (geo.subst tap)
  refine ⟨out,?_,?_⟩
  · have size := (Frame.subst_size geo tap).trans (Nat.zero_add geo.size)
    exact (parallelFrame_size num (geo.subst tap)).le.trans (Nat.add_le_add ns (size.le.trans gs))
  · intro P bits input sites active L oldSite slot dummy occ raw y owner present names read pick shift bound total room motion run bin
    let x : Src → Bool := Sum.elim (Sum.elim occ raw) (Sum.elim motion y)
    have left : run ∘ Sum.inl = num.eval x := funext fun j => parallelFrame_eval_inl _ _ _ j
    have ports : tap.eval x = Sum.elim motion raw := by
      funext j
      exact (Frame.initial_eval sharedSitePin x j).trans (by cases j <;> rfl)
    refine ⟨left.symm ▸ nr input active sites L oldSite slot dummy seed pick shift owner occ raw y present
      names read bound total room,?_⟩
    funext j
    exact (parallelFrame_eval_inr num (geo.subst tap) x j).trans ((Frame.subst_eval geo tap x j).trans
      ((congrFun (congrArg geo.eval ports) j).trans (congrFun (geoRead _) j)))

set_option maxHeartbeats 1800000 in
/-- A single producer for `DirectoryCircuit.checked_fields` and
`PublicRelative.chargedGeometry_frames_of_reads`. The labels shared between the
cable and site outputs are recovered before any whole-pack motion is chosen. -/
theorem ready_frames :
    ∃ cut A a C c : ℕ, ∀ (d : ℕ) (hd : 1 ≤ d), cut ≤ d+2*n+2*n →
    ∀ (Data : Type*) [Fintype Data] (V E w copies seeds : ℕ), V ≤ 2^w →
      ∀ (home : Fin E → Fin copies) (field : FieldBit (↥S) (Cube D) (d+2*n+2*n) → Data)
        (seed : ((Cube D → Deck (d+2*n)) × B.Bin) ≃ Fin seeds),
      let pat := sitePattern (n := n) B
      let Src := Source Data (↥B.types) Candidates q (d+2*n) copies V E w
      let pins := jointPins (V := V) (k := w) (w := w) B enum home field (M := Candidates)
      let r := Nat.clog 2 (Fintype.card B.Bin)
      let k := r+keyWidth q (d+2*n)
      let code := Framed.seedCode (fun t : B.types => t.val.radius) B.chart n
      ∃ f : Frame (Inputs Data Candidates q (d+2*n) copies V E w)
        (Table Src E k ⊕ BatchPorts q pat S d copies V seeds),
        f.size ≤ (300*(V+2*E+1)*(Nat.clog 2 (V+2*E)+w+Fintype.card Data+1)^3 +
          (1+E*(A*(d+2*n+2*n+1)^a+2*Fintype.card B.types+3))) +
          (1+E*(C*(d+1)^c)+E*r*(2*Fintype.card B.Bin+1)+1) +
          seeds*(pat.bins+90*q*(d+2*n+1)) ∧
        ∀ {P : Type} {bits : P → ℕ} (input : Fin copies → Pack D P bits K)
          (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) (d+2*n+2*n))
          (valid : ∀ i v, relativeAt _ (by omega) (sites i v) ∈ S)
          (charged : ∀ i, (input i).layout.Edge → Bool)
          (oldSite : (parallelPacks input).layout.Site ↪ Fin V) (slot : (parallelPacks input).layout.Edge ↪ Fin E)
          (dummy : Fin E → (parallelPacks input).layout.Site) (occ : Fin E → Bool) (raw : Raw Data V E w w → Bool),
          (∀ z, home (slot z) = z.1) → (∀ i, occ i = true ↔ i ∈ Set.range slot) →
          PublicEndpoints.Represents (parallelPacks input).layout oldSite slot dummy (raw ∘ Sum.inr) →
          (∀ (v : (parallelPacks input).layout.Site) j, raw (.inr (.inl (oldSite v,field j))) =
            siteAtBits (by omega) (sites v.1 v.2) (valid _ _) j) →
          (∀ z : (parallelPacks input).layout.Edge, raw (.inl (slot z)) = charged z.1 z.2) →
          (∀ i z, charged i z = true → dist (sites i ((input i).layout.src z)) (sites i ((input i).layout.dst z)) ≤ 2*h) →
          let active := positiveMask input sites charged
          ∃ L : Labels B input active sites, ∀ (pick : Fin copies → Candidates)
            (shift : Fin copies → Cube D → Deck (d+2*n)) (sizeBound : ℕ),
            (∑ z, (parallelPacks input).layout.width z) ≤ sizeBound →
            Nat.clog 2 (DirectoryCircuit.widthMultiplier e*sizeBound+1) ≤ w →
            let motion := motionWires enum pick shift
            let run := f.eval (Sum.elim (Sum.elim occ raw) motion)
            let bin := jointTags B (fun j => (index j).1) (fun j => (index j).2) input active sites L pick shift
            DirectoryCircuit.Ready e (populationPins (Sum.inr ∘ pins.live) oldField)
              (columns occupied oldField) (addressCode enum (binCode B.Bin)) seed (parallelPacks input)
              bin (fun _ => true) oldSite slot (nextDummy e (parallelPacks input) slot dummy seed) (run ∘ Sum.inl) ∧
            run ∘ Sum.inr = preFields enum pat (candidateIndex B index) field seed code Prod.fst (Sum.elim motion raw) := by
  obtain ⟨cut,A,a,reader⟩ := reconstruct_frames B enum
  obtain ⟨C,c,make⟩ := ready_from_classified_frames e B enum index
  refine ⟨cut,A,a,C,c,?_⟩
  intro d hd hcut Data inst V E w copies seeds fit home field seed pat Src pins r k code
  obtain ⟨g,gs,gr⟩ := reader _ (by omega) hcut Data V E w w fit field
  obtain ⟨both,bs,ready⟩ := make d hd Data V E w copies seeds home field seed
  let out := both.subst (cableInput g)
  refine ⟨out,?_,?_⟩
  · rw [show out = both.subst (cableInput g) from rfl,Frame.subst_size]
    simp only [cableInput,parallelFrame_size,Frame.subst_size,Frame.initial_size,zero_add]
    simpa only [Nat.add_assoc] using Nat.add_le_add gs bs
  · intro P bits input sites valid charged oldSite slot dummy occ raw owner present names payload mask short active
    obtain ⟨L,read⟩ := gr input sites valid charged oldSite slot dummy raw names payload mask short
    refine ⟨L,?_⟩
    intro pick shift bound total room motion run bin
    have ok := ready input sites active L oldSite slot dummy occ raw (g.eval raw) owner present names read
      pick shift bound total room
    have eq : run = both.eval (Sum.elim (Sum.elim occ raw) (Sum.elim motion (g.eval raw))) := by
      funext j
      simp [run,out,Frame.subst_eval,cableInput_eval]
    exact eq.symm ▸ ok

end Shortening.PublicRoundInput

end BorderVNP
end Computability
end OAI
