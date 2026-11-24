import OAI.Computability.VPVNP.PairSimulationHistory
import OAI.Computability.VPVNP.ShrinkMonomialWitness
import OAI.Computability.VPVNP.DegreeRefreshEntries
import OAI.Computability.VPVNP.StatePassHistory

/-!
# Binary readers at the two compression kernels

The shrinking kernel reads a separate word for each locally absorbed edge
and traverses all six-party entries resident at the site. The degree refresh
tests its diagonal segments and evaluates a single entry. The fixed motif
evaluator produces the ordered list of parameter names even before scalar
specialization.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LocalHistory

open NetworkKernel CompressorRecords MotifGrid MotifBlocks MotifConversion MotifDemandPadding MotifSelector

section Motif

variable {k : Type*} [Field k] {J D S : Type} [Fintype J] [Fintype D] [Fintype S]
  {a b : D → J} {P : Supply J S} {p : D → ℚ} {q : S → ℚ} {H H' : ℝ}
  (B : FixedBlock k a b P (realWidths p) (realWidths q) H H')

/-- The metered entry interpreter returns the exact parameter list, including
repeated labels and the empty success at zero repetitions. -/
theorem runEntry_list [DecidableEq J] (hp : ∀ i, 0 < p i) (w : D → ℕ) (v : S → ℕ)
    (j : J) (x : HalfBits a b w j) (y : Half P (fun e => Word (supplyWidths B w v e)) j) :
    (runEntry B hp w v j (MotifEntry.demandBits a b j x)
      (mapHalf P (fun _ => MotifEntry.inputBits) y)).1 = (entry B hp w v j x y).map List.ofFn := by
  unfold runEntry entry
  erw [MotifEntry.run_value]
  unfold MotifEntry.describe MotifEntry.labels
  erw [MotifEntry.indices_eq_groupedIndices (u := repetitions B w) P (basePayload B) (selectorTable B) (fun s => by simp [selectorTable])]
  simp_rw [MotifEntry.demandFields_eq a b (demand_le B hp w)]
  rw [Option.map_map]
  rfl

variable {R : Type*} [CommRing R] {Label : Type} [Fintype Label] (κ : Label → R)

/-- The executable check branches only on the output of the interpreter. -/
def listedEntryReader {u : ℕ} (idx : Option (Fin u → Label)) (names : Option (List Label))
    (hn : names = idx.map List.ofFn) : ChoiceReader (entryWitness κ idx).Choice :=
  let raw : ChoiceReader (if names.isSome then Unit else Empty) := by
    split <;> first | exact accept | exact reject
  have h : (if names.isSome then Unit else Empty) = (entryWitness κ idx).Choice := by
    cases idx <;> subst names <;> rfl
  raw.reindex (Equiv.cast h)

theorem listedEntryReader_length {u : ℕ} (idx : Option (Fin u → Label)) (names : Option (List Label))
    (hn : names = idx.map List.ofFn) (x : (entryWitness κ idx).Choice) :
    ((listedEntryReader κ idx names hn).encode x).length = 0 := by
  cases idx with
  | none => exact x.elim
  | some t => subst names; rfl

/-- Check a party's motif entry on the supplied demand and supply halves. The interpreter's
optional parameter list determines rejection or a unique zero-bit choice. -/
noncomputable def motifEntryReader [DecidableEq J] (κ : (parameterData B).Entry → R) (hp : ∀ i, 0 < p i)
    (w : D → ℕ) (v : S → ℕ) (j : J) (x : HalfBits a b w j) (y : Half P (fun e => Word (supplyWidths B w v e)) j) :
    ChoiceReader (entryWitness κ (entry B hp w v j x y)).Choice :=
  listedEntryReader κ _ _ (runEntry_list B hp w v j x y)

end Motif

section Shrink

open Compression Compression.PackingData Compression.ShrinkMotif WireTensor
open scoped Classical

variable {V H Tag L : Type} {d c d' pad : ℕ} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
  [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
  [DecidableEq V] [DecidableEq Tag] [DecidableEq L] (P : PackingData V H Tag L d c)
  (hc : 2 ≤ c) (hd : 0 < d) (number : P.BundleNumbering) (order : P.ThickNumbering)
  (w : Arc V H Tag L d c → ℕ) {next : Equiv.Perm (V × Tag)}
  {k R : Type*} [Field k] [CommRing R] {H' δ : ℝ}
  (B : FixedBlock k demandSource demandTarget supply (realWidths demandMass) (realWidths supplyMass) (31 / 16) H')
  (κ : (parameterData B).Entry → R) (hκ : (parameterData B).IsSolution κ)
  (ready : Ready d c d' δ) (I : ∀ l : Bool, P.ShrinkIndex l (subdivisions d c d') next d' pad)
  (s : ∀ m, P.ShrinkChoice number w B m)

/-- The shrinking choice is parsed from absorbed words followed by resident
map checks on the selected layout's sliced old and new indices. -/
noncomputable def shrinkReader
    (owners : ∀ v, Order {e // v = P.shrinkInternalOwner (P.shrinkTermLayout B number w s) e})
    (maps : ∀ v, Order {p : P.Motif × Fin 6 // P.shrinkPartySite (P.shrinkTermLayout B number w s) p.1 p.2 = v})
    (v a z) :
    ChoiceReader (P.shrinkKernelWitness hc hd number order w B κ hκ ready I s v a z).Choice :=
  let l := P.shrinkTermLayout B number w s
  let widths := fun m => P.shrinkSupplyWidths number w B m (s m)
  let sd := subdivisions d c d'
  let T := P.shrinkLayout hc hd number order w l sd widths (I l) ready.count_pos
    (fun m => P.shrinkMap number w B κ m (s m))
  let W := P.shrinkLayoutEntryWitness hc hd number order w l sd widths (I l) ready.count_pos
    (fun m => P.shrinkMap number w B κ m (s m)) (fun m j x y =>
      entryWitness κ (entry B demandMass_pos (P.shrinkDemandWidths number w m) (s m).val j x y))
  layoutReader T W (fun e => ChoiceReader.bounded (widths e.1 (!l,e.2)) _ le_rfl) owners
    (fun v a h z => (maps v).reader fun r =>
      motifEntryReader B κ demandMass_pos (P.shrinkDemandWidths number w r.1.1) (s r.1.1).val r.1.2
        (P.shrinkLocalDemandArg hc hd number order w l r.1.1 r.1.2 (r.2.symm ▸ a))
        (P.shrinkLocalSupplyArg l sd widths (I l) ready.count_pos r.1.1 r.1.2 (r.2.symm ▸ h) (r.2.symm ▸ z)))
    v a z

/-- The local matrix checks consume no private bits. The only guessed bits
of the shrinking kernel are the absorbed words, each at its declared width. -/
theorem shrinkReader_length
    (owners : ∀ v, Order {e // v = P.shrinkInternalOwner (P.shrinkTermLayout B number w s) e})
    (maps : ∀ v, Order {p : P.Motif × Fin 6 // P.shrinkPartySite (P.shrinkTermLayout B number w s) p.1 p.2 = v})
    (v a z) (x : (P.shrinkKernelWitness hc hd number order w B κ hκ ready I s v a z).Choice) :
    ((shrinkReader P hc hd number order w B κ hκ ready I s owners maps v a z).encode x).length =
      ∑ e : {e // v = P.shrinkInternalOwner (P.shrinkTermLayout B number w s) e},
        P.shrinkSupplyWidths number w B e.1.1 (s e.1.1) (!(P.shrinkTermLayout B number w s),e.1.2) := by
  unfold shrinkReader layoutReader
  change List.length ((_ : List Bool) ++ _) = _
  rw [List.length_append]
  erw [fiber_length, Order.reader_length]
  simp only [motifEntryReader, listedEntryReader_length, Finset.sum_const_zero, Nat.add_zero,
    ChoiceReader.bounded, PrimedCounter.digits, BurstRAM.length_wordBits]
  congr 1

end Shrink

section Refresh

open Compression Compression.Refresh SpectralGeometry Compression.DegreeRefresh
open scoped Classical

variable {k : Type*} [Field k] {D dH d₀ : ℕ} {K K' : ℝ}
  {V E L : Type} [Fintype V] [Fintype E] [Fintype L] [AddCommGroup E] [AddCommGroup L]
  (G : Compression.LiftedSlots V D (E × L)) (port : E ≃ Fin D) (w : (V × Fin D) × (E × L) → ℕ)
  (P : RegularArcGraph (Fin D) dH) (hdH : 0 < dH) (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : FixedBlock k tieSource tieTarget (expanderSupply P hdH hconn)
    (realWidths tieMass) (realWidths (expanderMass d₀)) K K')
  (hD : 1 < D) (hd : dH + 1 ≤ d₀) (c : BlockChoices G port w P hdH hconn F)
  {R : Type*} [CommRing R] [Fintype (parameterData F).Entry]
  (κ : (parameterData F).Entry → R) (hκ : (parameterData F).IsSolution κ)

/-- Run the same two external-segment tests as the refresh map, then
interpret the selected motif on its actual demand and supply arguments. -/
noncomputable def refreshNames (v : (V × Fin D) × L)
    (a : Placed (refreshPositions port) (actualWireGraph G w).Half v)
    (z : (expanderBranchGraph G port w P hdH hconn F hD hd c).Half v) : Option (List (parameterData F).Entry) :=
  let p := promotedSites.symm v
  let t := oldPortMatching G port
  let widths := groupedWidths port w
  let dst := bundleTarget G
  let n := blockSupplyWidths G port w P hdH hconn F c
  let C := fun s e ↦ Fin (2 ^ n s e)
  let old := originalIso G port w
  let new := promotedIso G port w P.toSlotGraph hD hd C n (fun s e ↦ (wordIndex (n s e)).symm)
  let x := old.pullHalf p (a (originalSites port p) (by simp [p, originalSites, promotedSites, refreshPositions]))
  let u := new.pullHalf p z
  let seg := incidentPortSegments t dst (oldPortMatching_bundle G port) widths p
    (u.1 (.inl p) rfl) (u.2 (.inl (dst.symm p)) (dst.apply_symm_apply p).symm)
  let y := supplyHalf (R := ℤ) dst widths Prod.fst (fun e ↦ (P.reverse e).1) C (d₀ - (dH + 1)) p u
  if x.1 ((p.1,p.2),p.2) rfl = seg.1 p.2 ∧
      seg.2 p.2 = incomingHalf (R := ℤ) t widths p.1 p.2 p.2 x then
    (runEntry F (fun _ ↦ zero_lt_one) (blockDemandWidths G port w p.1) (c p.1).val p.2
      (MotifEntry.demandBits _ _ p.2 (portInput (R := ℤ) t widths p.1 p.2 x seg))
      (mapHalf _ (fun _ => MotifEntry.inputBits) y)).1
  else none

omit [Fintype (parameterData F).Entry] in
theorem refreshNames_spec (v a z) :
    refreshNames G port w P hdH hconn F hD hd c v a z =
      (refreshEntryIndices G port w P hdH hconn F hD hd c (promotedSites.symm v) a z).map List.ofFn := by
  unfold refreshNames refreshEntryIndices
  dsimp only
  split_ifs
  · exact runEntry_list ..
  · rfl

/-- At a refreshed port the two ties and the entry checks determine its
choice entirely from the arguments already supplied by the descriptor. -/
noncomputable def refreshReader (v a z) :
    ChoiceReader (expanderKernelWitness G port w P hdH hconn F hD hd c κ hκ v a z).Choice :=
  listedEntryReader κ _ _ (refreshNames_spec G port w P hdH hconn F hD hd c v a z)

end Refresh
end PairSimulation.LocalHistory

end VPVNP
end Computability
end OAI
