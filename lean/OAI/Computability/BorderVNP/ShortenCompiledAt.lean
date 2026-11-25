import OAI.Computability.BorderVNP.ShortenCompiledChildChoice
import OAI.Computability.BorderVNP.ShortenPublicStageTrace
import OAI.Computability.BorderVNP.CoverDeckPackWidth
import OAI.Computability.BorderVNP.ParseBatchVerifierCountWords

/-!
# Calibrating the compiled pack choices before the cover depth

The deviation coefficient belongs to the count-bank selector itself. The
same coefficient, denominator and gate-size constants work at every positive
cover depth. Encoding the actual candidate populations supplies the selector
with a concrete table and gives physical samples read from its trace wires.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PreparedBins

open Cover Cover.Frame Cover.AddressCircuit Hecke Epoch PackMotions Packing Framed Crossing
open VPVNP.VerifierNetwork (Frame)
open scoped Classical BorderVNP.Epoch.Cube

universe u

variable {D : ℕ} {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ} (B : PreparedBins D S h η)

/-- Canonical order of the sign-vector coordinates used by the selector's address wires. -/
noncomputable abbrev factorEnum (D : ℕ) := (Fintype.equivFin (Cube D)).symm

/-- Canonical order of all permutation and Hecke-word tuples at the given cutoff. -/
noncomputable abbrev candidateEnum (D n : ℕ) :=
  (Fintype.equivFin (PackedDeckMean.MotionCandidate (lattice 1) elliptic (Cube D) n)).symm

/-- The selector's candidate-count input wires. -/
abbrev SelectionTables (n l w k : ℕ) :=
  PackTables B.Bin (Fintype.card (Cube D)) l (Fintype.card (PackedDeckMean.MotionCandidate (lattice 1) elliptic (Cube D) n)) w k

/-- The final count bank and the selected flags and keys for all children. -/
abbrev SelectionPins (n l w k : ℕ) :=
  PackTracePins B.Bin (Fintype.card (Cube D)) l (Fintype.card (PackedDeckMean.MotionCandidate (lattice 1) elliptic (Cube D) n)) w k

/-- A physical sample trace for one actual table and one literal selector circuit. -/
def PhysicalTrace {n d w k : ℕ} {Port : Type} {bits : Port → ℕ} {K : Type u}
    (child : Fin k → PlacedPack D Port bits K (Cube D) (d+2*n))
    (L : Labels B (fun i => (child i).pack) (fun i => (child i).active) (childSites child))
    (f : Frame (B.SelectionTables n (d+1) w k) (B.SelectionPins n (d+1) w k))
    (z : B.SelectionTables n (d+1) w k → Bool) (hk : 0 < k) (N : ℕ) : Prop :=
  let input := fun i => (child i).pack
  let tags := B.tag (d := d+1) (n := n) input (fun i => (child i).active) L.kind L.lift
  ∃ (choice : Fin k → Fin (Fintype.card (PackedDeckMean.MotionCandidate (lattice 1) elliptic (Cube D) n)))
    (deck : Fin k → Fin (Fintype.card (Cube D)) → Deck (d+1)),
    let ω := fun i => deckSample (factorEnum D) (candidateEnum D n) (choice i,deck i)
    (∀ i j, f.eval z (.inr (i,.inl j)) = true ↔ j = choice i) ∧
    (∀ i b, f.eval z (.inr (i,.inr b)) = keyWord _ (d+1) (deck i) b) ∧
    (∀ b g, ParseBatchSort.value (fun s => f.eval z (.inl (.inl (b,g,s)))) =
      SeedIntervals.count (parallelPacks input).layout (jointBin input tags ω) (g ∘ (factorEnum D).symm,b)) ∧
    B.SampleDeviation child L ω hk N

/-- The common positive denominator, gate-size constants and selector specification for
the deviation coefficient fixed at preparation time. -/
def CompiledAt (n N : ℕ) : Prop :=
  ∃ P C e : ℕ, 0 < P ∧ ∀ d k w : ℕ, 0 < d → ∀ hk : 0 < k, P < 2^w →
    ∃ f : Frame (B.SelectionTables n (d+1) w k) (B.SelectionPins n (d+1) w k),
      f.size ≤ 1+k*(Fintype.card (Cube D → Deck (d+1))*C*(d+1+w+1)^e) ∧
      ∀ {Port : Type} {bits : Port → ℕ} {K : Type u} (child : Fin k → PlacedPack D Port bits K (Cube D) (d+2*n))
        (L : Labels B (fun i => (child i).pack) (fun i => (child i).active) (childSites child)),
        (∀ i c, (child i).active c = true → dist ((child i).midpoint c) ((child i).site ((child i).pack.layout.src c)) ≤
          dist ((child i).site ((child i).pack.layout.src c)) ((child i).site ((child i).pack.layout.dst c))/2) →
        ∀ (z : B.SelectionTables n (d+1) w k → Bool) (H : ℕ),
          let counts := B.deckCounts (d := d+1) (fun i => (child i).pack) (fun i => (child i).active)
            L.kind L.lift (factorEnum D) (candidateEnum D n)
          tableCount z = counts → (∀ i j b g, counts i j b g ≤ H) →
          packRunWidth (Fintype.card (Cube D → Deck (d+1))) P k H ≤ w →
          B.PhysicalTrace child L f z hk N

/-- A single deviation coefficient is realized by the compiled physical selector on all depths. -/
theorem exists_compiledAt (n : ℕ) : ∃ N : ℕ, CompiledAt.{u} B n N := by
  obtain ⟨N,P,C,e,hP,h⟩ := B.compiledChildSample_frames (factorEnum D) (candidateEnum D n)
  refine ⟨N,P,C,e,hP,?_⟩
  intro d k w hd hk hw
  obtain ⟨f,hsize,run⟩ := h d k w hd hk hw
  exact ⟨f,hsize,fun child L hm z H hz hb hf => run child L hm z H hz hb hf⟩

/-- Read the actual physical samples and count bank from a sufficiently wide encoded
table. The width is positive and the frame is the one supplied by the calibrated selector. -/
theorem physical_trace {n N d k : ℕ} (compiled : CompiledAt.{u} B n N) (hd : 0 < d) (hk : 0 < k)
    {Port : Type} {bits : Port → ℕ} {K : Type u} (child : Fin k → PlacedPack D Port bits K (Cube D) (d+2*n))
    (L : Labels B (fun i => (child i).pack) (fun i => (child i).active) (childSites child))
    (hm : ∀ i c, (child i).active c = true → dist ((child i).midpoint c) ((child i).site ((child i).pack.layout.src c)) ≤
      dist ((child i).site ((child i).pack.layout.src c)) ((child i).site ((child i).pack.layout.dst c))/2) :
    ∃ w > 0, ∃ f : Frame (B.SelectionTables n (d+1) w k) (B.SelectionPins n (d+1) w k),
      ∃ z : B.SelectionTables n (d+1) w k → Bool,
        tableCount z = B.deckCounts (d := d+1) (fun i => (child i).pack) (fun i => (child i).active)
          L.kind L.lift (factorEnum D) (candidateEnum D n) ∧ B.PhysicalTrace child L f z hk N := by
  obtain ⟨P,C,e,hP,make⟩ := compiled
  let counts := B.deckCounts (d := d+1) (fun i => (child i).pack) (fun i => (child i).active)
    L.kind L.lift (factorEnum D) (candidateEnum D n)
  let cell := fun x : Fin k × _ × B.Bin × _ => counts x.1 x.2.1 x.2.2.1 x.2.2.2
  let H := Finset.univ.sup cell
  have cap i j b g : counts i j b g ≤ H := Finset.le_sup (f := cell) (Finset.mem_univ (i,j,b,g))
  let V := Fintype.card (Cube D → Deck (d+1))
  let w := Cover.AddressCircuit.packWidth V P k H
  obtain ⟨den,room,fits⟩ := packWidth_fits V P k H
  have wp : 0 < w := by
    by_contra! he
    have h0 : w = 0 := Nat.eq_zero_of_le_zero he
    change P < 2^w at den
    rw [h0,pow_zero] at den
    omega
  obtain ⟨f,_,run⟩ := make d k w hd hk den
  let word (i j b g) := (ParseBatchCounts.numberWords w).symm ⟨counts i j b g,(cap i j b g).trans_lt room⟩
  let z : B.SelectionTables n (d+1) w k → Bool := fun x => word x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2
  have hz : tableCount z = counts := by
    funext i j b g
    exact ParseBatchCounts.value_encode (w := w) ⟨counts i j b g,(cap i j b g).trans_lt room⟩
  exact ⟨w,wp,f,z,hz,run child L hm z H hz cap fits⟩

/-- Existence of physical samples at the calibrated coefficient, obtained by decoding
the literal selection circuit on the actual population table. -/
theorem physical_choice {n N d k : ℕ} (compiled : CompiledAt.{u} B n N) (hd : 0 < d) (hk : 0 < k)
    {Port : Type} {bits : Port → ℕ} {K : Type u} (child : Fin k → PlacedPack D Port bits K (Cube D) (d+2*n))
    (L : Labels B (fun i => (child i).pack) (fun i => (child i).active) (childSites child))
    (hm : ∀ i c, (child i).active c = true → dist ((child i).midpoint c) ((child i).site ((child i).pack.layout.src c)) ≤
      dist ((child i).site ((child i).pack.layout.src c)) ((child i).site ((child i).pack.layout.dst c))/2) :
    ∃ ω, B.SampleDeviation child L ω hk N := by
  obtain ⟨_,_,_,_,_,j,g,_,_,_,dev⟩ := B.physical_trace compiled hd hk child L hm
  exact ⟨fun i => deckSample (factorEnum D) (candidateEnum D n) (j i,g i),dev⟩

end Shortening.PreparedBins

end BorderVNP
end Computability
end OAI
