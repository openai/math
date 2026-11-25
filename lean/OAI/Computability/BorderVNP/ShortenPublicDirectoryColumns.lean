import OAI.Computability.BorderVNP.ShortenPublicDirectoryPadding
import OAI.Computability.BorderVNP.ShortenPublicPopulationJointKeys

/-! # All fields required by the checked old-cable directory

The width and endpoints of an occupied edge are read from the original raw
array, even for inactive or width-zero cables. Occupancy is its independent
saved flag. Every successor padding pointer reads an existing old source
pointer. The single orientation literal is shared by all rows.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicDirectory

open Crossing SeedIntervals StaticRows PublicEndpoints PublicPopulation Packing DirectoryCircuit
open ParseBatchSort
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

variable {σ Data : Type*} {E V k w D : ℕ}

/-- Saved wires, numeric bin bits and the shared positive-orientation literal. -/
abbrev Table (σ : Type*) (E k : ℕ) := (σ ⊕ Fin E × Fin k) ⊕ Unit

/-- Attach the true orientation bit after the stable key table. -/
noncomputable def withOrientation [Fintype σ] (keys : Frame σ (σ ⊕ Fin E × Fin k)) : Frame σ (Table σ E k) :=
  (((Frame.initial (id : σ ⊕ Fin E × Fin k → σ ⊕ Fin E × Fin k)).step fun _ : Unit => .const true).withInput).subst keys

/-- All old operands and keys are forwarded and the orientation is a single additional gate. -/
theorem withOrientation_size [Fintype σ] (keys : Frame σ (σ ⊕ Fin E × Fin k)) :
    (withOrientation keys).size ≤ keys.size+1 := by
  have h := Frame.step_size_le (Frame.initial (id : σ ⊕ Fin E × Fin k → σ ⊕ Fin E × Fin k))
    (fun _ : Unit => .const true) 1 (fun _ => le_rfl)
  simpa [withOrientation] using Nat.add_le_add_left h keys.size

/-- Operand wires of the public population contract, using the old raw width column. -/
def populationPins (live : Fin E → σ) (raw : PublicEndpoints.Inputs Data V E w w → σ) :
    Pins (Fin E) (Table σ E k) k w where
  active u := .inl (.inl (live u))
  key u j := .inl (.inr (u,j))
  width u j := .inl (.inl (raw (.inr (u,.inl j))))

/-- Occupancy, signed orientation, source, destination, and padding operands
for the exact old interval directory. -/
def columns (occ : Fin E → σ) (raw : PublicEndpoints.Inputs Data V E w w → σ) : Columns (Table σ E k) E D w where
  occupied u := .inl (.inl (occ u))
  positive _ := .inr ()
  endpoint u s j := .inl (.inl (raw (.inr (u,.inr (s,j)))))
  padding r j := .inl (.inl (raw (.inr (r.1,.inr (true,j)))))

variable {m nSeeds : ℕ} {K : Type*} [Field K] [NeZero D] (e : PaidIdentity K D m)
    {P : Type*} {bits : P → ℕ} (pack : Pack D P bits K) (oldSite : pack.layout.Site ↪ Fin V)
    (rows : pack.layout.Edge ↪ Fin E) (oldDummy : Fin E → pack.layout.Site)
    {A : Type} [Fintype A] (bin : pack.layout.Edge → Option A)
    (seed : A ≃ Fin nSeeds) (code : A ↪ Fin (2^k))

omit [NeZero D] [Fintype A] in
/-- A real raw pointer table and the true numeric-key stage satisfy every
field of the serializer's `Ready` contract. No valid-row assumption is
required on the raw inputs outside their sparse, padded representation. -/
theorem ready_of_keys [Fintype σ] (keys : Frame σ (σ ⊕ Fin E × Fin k)) (live : Fin E → σ)
    (oldWidth : Fin E → Fin w → σ) (occ : Fin E → σ) (raw : PublicEndpoints.Inputs Data V E w w → σ)
    (x : σ → Bool) (saved : ∀ s, keys.eval x (.inl s) = x s)
    (present : ∀ u, x (occ u) = true ↔ u ∈ Set.range rows)
    (pointers : PublicEndpoints.Represents pack.layout oldSite rows oldDummy (x ∘ raw))
    (hist : PublicPopulation.Represents (addressedPins live oldWidth) pack.layout bin rows code (keys.eval x))
    {S : ℕ} (total : (∑ c, pack.layout.width c) ≤ S) (word : Nat.clog 2 (widthMultiplier e*S+1) ≤ w) :
    Ready e (populationPins live raw) (columns occ raw) code seed pack bin (fun _ => true)
      oldSite rows (nextDummy e pack rows oldDummy seed) ((withOrientation keys).eval x) := by
  have left (j : σ ⊕ Fin E × Fin k) : (withOrientation keys).eval x (.inl j) = keys.eval x j := by simp [withOrientation]
  have pass (i : σ) : (withOrientation keys).eval x (.inl (.inl i)) = x i := (left (.inl i)).trans (saved i)
  have hw (c : pack.layout.Edge) : value (fun j => x (raw (.inr (rows c,.inl j)))) = pack.layout.width c :=
    (pointers.widths (rows c)).trans (Names.width_slot pack.layout rows oldDummy c)
  have haddr (u : Fin E) (s : Bool) : value (fun j => x (raw (.inr (u,.inr (s,j))))) =
      (storedSite pack.layout oldSite rows oldDummy u s).val := pointers.addresses u s
  refine ⟨⟨?_,?_,?_,?_⟩,bin_room e pack bin total word,?_,?_,?_,?_,?_⟩
  · intro c
    exact (left _).trans (hist.active c)
  · intro u hu
    exact (left _).trans (hist.absent u hu)
  · intro c a ha
    simpa only [populationPins,addressedPins,Function.comp_def,left] using hist.address c a ha
  · intro c _ _
    simpa only [populationPins,Function.comp_def,pass] using hw c
  · intro c
    simpa only [populationPins,Function.comp_def,pass] using hw c
  · intro u
    simpa only [columns,pass] using present u
  · intro c
    simp [columns,withOrientation,BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit.Expr.eval]
  · intro c
    have hs := (haddr (rows c) true).trans
      (congrArg (fun v => (oldSite v).val) (Names.src_slot pack.layout rows oldDummy c))
    have hd := (haddr (rows c) false).trans
      (congrArg (fun v => (oldSite v).val) (Names.dst_slot pack.layout rows oldDummy c))
    simpa only [columns,Function.comp_def,pass] using And.intro hs hd
  · intro r
    simpa only [columns,Function.comp_def,pass,nextDummy_band] using haddr r.1 true

end Shortening.PublicDirectory

end BorderVNP
end Computability
end OAI
