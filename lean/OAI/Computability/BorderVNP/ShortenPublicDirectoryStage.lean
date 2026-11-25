import OAI.Computability.BorderVNP.ShortenPublicDirectoryColumns

/-! # Physical pre-cable stage before the checked round serializer

The physical segment labels are selected once by the old endpoint join. Every
selected pack motion uses those same labels. The pre-cable stage retains the
ordinary old table and its independent occupied bits for the interval serializer.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicDirectory

open Cover Cover.Frame Cover.AddressCircuit Epoch Crossing Packing PackMotions Hecke PublicPopulation
open PublicSegments PublicEndpoints DirectoryCircuit StaticRows SeedIntervals
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

/-- Independent old occupancy plus its full raw table, alongside the motion and classified cable fields. -/
abbrev Source (Data T M : Type*) (q l copies V E w : ℕ) :=
  (Fin E ⊕ Raw Data V E w w) ⊕ (Motion M q l copies ⊕ Classified Data T V E w w)

variable {Data T M : Type*} {q l copies V E w : ℕ}

/-- Saved occupancy wire from the prior cable directory, independent of width and charge. -/
def occupied (i : Fin E) : Source Data T M q l copies V E w := .inl (.inl i)

/-- Saved input array supplying all endpoint pointers, widths and hole sites. -/
def oldField (i : PublicEndpoints.Inputs Data V E w w) : Source Data T M q l copies V E w :=
  .inl (.inr (.inr i))

private noncomputable def liftKeys {L R : Type*} [Fintype L] [Fintype R] {rows k : ℕ}
    (keys : Frame R (R ⊕ Fin rows × Fin k)) : Frame (L ⊕ R) ((L ⊕ R) ⊕ Fin rows × Fin k) :=
  ((keys.select Sum.inr).subst (Frame.initial Sum.inr)).withInput

private theorem liftKeys_value {L R : Type*} [Fintype L] [Fintype R] {rows k : ℕ}
    (keys : Frame R (R ⊕ Fin rows × Fin k)) (saved : L → Bool) (y : R → Bool) (u : Fin rows × Fin k) :
    (liftKeys keys).eval (Sum.elim saved y) (.inr u) = keys.eval y (.inr u) := by
  have hr : (Frame.initial (Sum.inr : R → L ⊕ R)).eval (Sum.elim saved y) = y := funext fun _ => by simp
  simp [liftKeys,hr]

variable {D m n : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
    {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ} (B : PreparedBins D S h η)
    (enum : Fin q ≃ Cube D) [Fintype M] [DecidableEq M]
    (perm : M → Equiv.Perm (Cube D)) (word : M → ProductSample (lattice 1) elliptic (Cube D) n)

omit [NeZero D] in
/-- The stage emits an actual `DirectoryCircuit.Ready` input for the disjoint union.
The original occupied flags are used at all rows, even when their widths are zero.
The room bound is global and independent of the motion, seed, and histogram choices. -/
theorem preCable_frames :
    ∃ C p : ℕ, ∀ (d : ℕ) (hd : 1 ≤ d) (w copies V E : ℕ) {Data : Type*} [Fintype Data]
      (home : Fin E → Fin copies) (field : FieldBit (↥S) (Cube D) (d+2*n+2*n) → Data),
      let Src := Source Data (↥B.types) M q (d+2*n) copies V E w
      let pins := jointPins (V := V) (k := w) (w := w) B enum home field (M := M)
      let r := Nat.clog 2 (Fintype.card B.Bin)
      let k := r+keyWidth q (d+2*n)
      ∃ f : Frame Src (Table Src E k),
        f.size ≤ 1+E*(C*(d+1)^p) + E*r*(2*Fintype.card B.Bin+1)+1 ∧
        (∀ x j, f.eval x (.inl (.inl j)) = x j) ∧
        ∀ {P : Type} {bits : P → ℕ} (input : Fin copies → Pack D P bits K)
          (active : ∀ i, (input i).layout.Edge → Bool)
          (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) (d+2*n+2*n))
          (L : PreparedBins.Labels B input active sites)
          (oldSite : (parallelPacks input).layout.Site ↪ Fin V) (slot : (parallelPacks input).layout.Edge ↪ Fin E)
          (oldDummy : Fin E → (parallelPacks input).layout.Site) {nSeeds : ℕ}
          (seed : ((Cube D → Deck (d+2*n)) × B.Bin) ≃ Fin nSeeds)
          (pick : Fin copies → M) (shift : Fin copies → Cube D → Deck (d+2*n)),
          (∀ c, home (slot c) = c.1) → ∀ (occ : Fin E → Bool) (raw : Raw Data V E w w → Bool)
            (y : Classified Data (↥B.types) V E w w → Bool),
          (∀ u, occ u = true ↔ u ∈ Set.range slot) →
          PublicEndpoints.Represents (parallelPacks input).layout oldSite slot oldDummy (raw ∘ Sum.inr) →
          PhysicalReads B enum (by omega) field input active sites L slot y →
          ∀ sizeBound, (∑ c, (parallelPacks input).layout.width c) ≤ sizeBound →
          Nat.clog 2 (widthMultiplier e*sizeBound+1) ≤ w →
          let run := f.eval (Sum.elim (Sum.elim occ raw) (Sum.elim (motionWires enum pick shift) y))
          Ready e (populationPins (Sum.inr ∘ pins.live) oldField) (columns occupied oldField)
            (addressCode enum (binCode B.Bin)) seed (parallelPacks input)
            (jointTags B perm word input active sites L pick shift) (fun _ => true) oldSite slot
            (nextDummy e (parallelPacks input) slot oldDummy seed) run := by
  obtain ⟨C,p,make⟩ := jointAddress_frames B enum perm word
  refine ⟨C,p,?_⟩
  intro d hd w copies V E Data instData home field Src pins r k
  obtain ⟨keys,hs,saved,rep⟩ := make d hd w copies pins
  let full : Frame Src (Src ⊕ Fin E × Fin k) := liftKeys keys
  refine ⟨withOrientation full,?_,?_,?_⟩
  · apply (withOrientation_size full).trans
    simpa only [full,liftKeys,Frame.withInput_size,Frame.subst_size,Frame.select_size,
      Frame.initial_size,zero_add,Fintype.card_fin] using Nat.add_le_add_right hs 1
  · intro x j
    simp [withOrientation,full,liftKeys]
  · intro P bits input active sites L oldSite slot oldDummy nSeeds seed pick shift owner occ raw y present names phys S₀ total wordFit run
    let z := Sum.elim (motionWires enum pick shift) y
    let left := Sum.elim occ raw
    let x : Src → Bool := Sum.elim left z
    let bin := jointTags B perm word input active sites L pick shift
    have reads := jointReads_of_physical B enum home field input active sites L slot owner y hd phys pick shift
    have hx := rep input active sites L slot pick shift z reads
    have pass (j : Src) : full.eval x (.inl j) = x j := Frame.withInput_eval_inl _ _ _
    have lift (u) : full.eval x (.inr u) = keys.eval z (.inr u) := liftKeys_value keys left z u
    have read (j) : full.eval x (.inl (.inr j)) = keys.eval z (.inl j) := (pass _).trans (saved z j).symm
    have pop : PublicPopulation.Represents (addressedPins (Sum.inr ∘ pins.live) (fun u => Sum.inr ∘ pins.width u))
        (parallelPacks input).layout bin slot (addressCode enum (binCode B.Bin)) (full.eval x) := by
      refine ⟨?_,?_,?_,?_⟩
      · intro c
        exact (read _).trans (hx.active c)
      · intro u hu
        exact (read _).trans (hx.absent u hu)
      · intro c b hb
        simpa only [addressedPins,Function.comp_def,lift] using hx.address c b hb
      · intro c b hb
        simpa only [addressedPins,Function.comp_def,read] using hx.width c b hb
    exact ready_of_keys e (parallelPacks input) oldSite slot oldDummy bin seed (addressCode enum (binCode B.Bin))
      full (Sum.inr ∘ pins.live) (fun u => Sum.inr ∘ pins.width u) occupied oldField x pass present names pop total wordFit

end Shortening.PublicDirectory

end BorderVNP
end Computability
end OAI
