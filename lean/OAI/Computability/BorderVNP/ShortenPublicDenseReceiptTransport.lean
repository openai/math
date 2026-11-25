import OAI.Computability.BorderVNP.ShortenPublicDenseReceiptKernel

/-! # Passing the same physical labels and raw wires to the circuit depth -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicDenseReceipt

open Cover Cover.Frame Cover.AddressCircuit Crossing Epoch Catalog PreparedBins
open PublicSegments PublicRelative PackMotions Packing Hecke PublicPopulation PublicDirectory DirectoryCircuit StaticRows
open scoped Classical BorderVNP.Epoch.Cube

/-- Reading a classified table at an equal depth preserves its chosen lifts and kinds. -/
theorem physical_atLevel {D q copies V E k w a b : ℕ} {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ}
    (B : PreparedBins D S h η) (enum : Fin q ≃ Cube D) {Data P : Type} {bits : P → ℕ} {K : Type*}
    (field : FieldBit (↥S) (Cube D) a → Data) (input : Fin copies → Pack D P bits K)
    (active : ∀ i, (input i).layout.Edge → Bool)
    (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) a) (L : Labels B input active sites)
    (slot : (parallelPacks input).layout.Edge ↪ Fin E) (x : Classified Data (↥B.types) V E k w → Bool)
    (ha : 0<a) (level : a=b) (read : PhysicalReads B enum ha field input active sites L slot x) :
    PhysicalReads B enum (by omega) (fieldAtLevel level field) input active (fun i v => levelCast level (sites i v))
      (Labels.transport B L level) slot x := by
  cases level
  exact read

/-- Two rewritings of the integer depth compose to one direct rewiring. -/
theorem fieldAtLevel_trans {Site I Data : Type*} {a b c : ℕ} (ab : a=b) (bc : b=c)
    (field : FieldBit Site I a → Data) : fieldAtLevel bc (fieldAtLevel ab field) = fieldAtLevel (ab.trans bc) field := by
  cases ab; cases bc; rfl

/-- Cast the classified data of the actual child packs into the stage's input
level expression without changing any semantic cable tag or stable row. -/
theorem child_reads_atLevel {D q n lev d copies V E w : ℕ} {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ}
    (B : PreparedBins D S h η) (enum : Fin q ≃ Cube D) {Data P : Type} {bits : P → ℕ} {K : Type*}
    (field : FieldBit (↥S) (Cube D) (lev+2*n+1) → Data) (child : Fin copies → PlacedPack D P bits K (Cube D) (lev+2*n))
    (L : Labels B (fun i => (child i).pack) (fun i => (child i).active) (childSites child))
    (slot : (parallelPacks fun i => (child i).pack).layout.Edge ↪ Fin E)
    (y : Classified Data (↥B.types) V E w w → Bool)
    (hd : 1 ≤ d) (level : lev+1=d+2*n)
    (read : PhysicalReads B enum (by omega) (fieldAtLevel (Nat.add_right_comm lev (2*n) 1) field)
      (fun i => (child i).pack) (fun i => (child i).active) (childSites child) L slot y) :
    let hl := congrArg (·+2*n) level
    PhysicalReads B enum (by omega) (fieldAtLevel (show lev+2*n+1=d+2*n+2*n by omega) field)
      (fun i => (child i).pack) (fun i => (child i).active) (fun i v => levelCast hl (childSites child i v))
      (Labels.transport B L hl) slot y := by
  intro hl
  have h := physical_atLevel B enum _ _ _ _ L slot y (by omega) hl read
  rw [fieldAtLevel_trans] at h
  exact h

/-- Reindexing every absolute seed by its equal quotient depth preserves the
numeric population, the physical code, and the padding source pointer. -/
theorem ready_atLevel {D m V E seeds k w a b : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)
    {σ T P : Type} {bits : P → ℕ} (level : a=b) (p : Pins (Fin E) σ k w) (col : Columns σ E D w)
    (code : ((Cube D → Deck b) × T) ↪ Fin (2^k)) (seed : ((Cube D → Deck b) × T) ≃ Fin seeds)
    (N : Pack D P bits K) (bin : N.layout.Edge → Option ((Cube D → Deck a) × T))
    (old : N.layout.Site ↪ Fin V) (slot : N.layout.Edge ↪ Fin E) (dummy : Fin E → N.layout.Site)
    (x : σ → Bool) (r : Ready e p col code seed N (fun z => (bin z).map (seedLevel level))
      (fun _ => true) old slot (nextDummy e N slot dummy seed) x) :
    Ready e p col ((seedLevel level).toEmbedding.trans code) ((seedLevel level).trans seed) N bin
      (fun _ => true) old slot (nextDummy e N slot dummy ((seedLevel level).trans seed)) x := by
  cases level
  simpa [seedLevel] using r

/-- The moved-bin computation at the numerical level sends every genuine
physical tag through the same finite seed equivalence. -/
theorem tags_atLevel {D copies a b n m : ℕ} {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ}
    (B : PreparedBins D S h η)
    (index : Fin m ≃ PackedDeckMean.MotionCandidate (lattice 1) elliptic (Cube D) n)
    (level : a=b) {P : Type} {bits : P → ℕ} {K : Type*} (input : Fin copies → Pack D P bits K)
    (active : ∀ i, (input i).layout.Edge → Bool) (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) (a+2*n))
    (L : Labels B input active sites) (ω : Fin copies → PackSample (lattice 1) elliptic (Cube D) a n) :
    let L' := Labels.transport B L (congrArg (·+2*n) level)
    let pick := fun i => sampledChoice index (ω i)
    jointBin input (B.tag (d := b) input active L'.kind L'.lift)
      (fun i => ((index (pick i)).1,(index (pick i)).2,fun j => deckCast level ((ω i).2.2 j))) =
      fun z => ((jointBin input (B.tag (d := a) input active L.kind L.lift) ω) z).map (seedLevel level) := by
  cases level
  intro L' pick
  have h : (fun i => ((index (pick i)).1,(index (pick i)).2,fun j => deckCast rfl ((ω i).2.2 j))) = ω := by
    funext i
    rw [show index (pick i) = ((ω i).1,(ω i).2.1) from index.apply_symm_apply _]
    rfl
  rw [h]
  funext z
  change (jointBin input (B.tag input active L.kind L.lift) ω z) =
    (jointBin input (B.tag input active L.kind L.lift) ω z).map _
  cases jointBin input (B.tag input active L.kind L.lift) ω z <;> rfl

end Shortening.PublicDenseReceipt

end BorderVNP
end Computability
end OAI
