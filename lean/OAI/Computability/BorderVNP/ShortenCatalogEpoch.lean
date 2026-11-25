import OAI.Computability.BorderVNP.ShortenCatalogProgram

/-!
# One physical shortening epoch over a finite path of prepared catalogs

Once each finite relative catalog has a geometric stage preparation, no
step witness or physical program has to be supplied by the input packs.
The path, cumulative depth drop and stage coefficients are fixed before
the fan-in. The output bounds and exact public histories belong to a
single program installed on the actual leaves at the given deep level.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.Adaptive

open Crossing Cover Epoch Filter Topology PlacedStep
open scoped Classical

variable {I P : Type} [Fintype I] {D m k b : ℕ} [NeZero D] {K : Type*} [Field K]
    {bits : P → ℕ} {e : PaidIdentity K D m} {hCap hSaving ν : ℝ}

namespace StagePath

variable (path : StagePath b e I hCap hSaving ν)

/-- The actual cover depths of the entire prepared path starting at the
specified high level, including a last word reserved for the site motion. -/
def depths (last high : ℕ) : ℕ → ℕ :=
  let word := fun i => (path.pattern i).word
  Levels.level word (high - Levels.totalDrop word last) last

/-- A single high-level threshold checks every intermediate depth floor and
the chosen floor for the final site motion. -/
def threshold (last lastFloor : ℕ) : ℕ := Levels.totalDrop (fun i => (path.pattern i).word) last +
  (lastFloor + ∑ i, (path.pattern i).floor)

/-- Actual admissible public states on the chosen path of quotient levels. -/
abbrev State (P : Type) (bits : P → ℕ) (k last high j : ℕ) :=
  {p : PlacedPack D (Port k P j) (width bits k j) K I (path.depths last high j) //
    Catalog.PlacedAt (path.catalog j) hCap p}

/-- Every such deep input level admits one actual, measured, directly stored
program with all tile counts bounded by the original product tile count. -/
theorem program_at_start (last lastFloor high : ℕ) (hhigh : path.threshold last lastFloor ≤ high)
    (hk : 0 < k) :
    path.depths last high 0 = high ∧
    lastFloor ≤ high - Levels.totalDrop (fun i => (path.pattern i).word) last ∧
    (∀ j, Fintype.card (I → Deck (path.depths last high j+1)) ≤ Fintype.card (I → Deck (high+1))) ∧
    ∃ F : Program (B := fun i => (path.pattern i).Bin) e (fun n (p : path.State P bits k last high n) => p.val),
      (∀ i c, Nonempty (Measurements (F.step i c) hk hSaving ν (path.pattern i).meanFactor
        (path.pattern i).motionFactor)) ∧
      ∀ i c q, (F.advance i c q).val = (F.step i c).result e q := by
  let word := fun i => (path.pattern i).word
  let terminal := high - Levels.totalDrop word last
  obtain ⟨hstart,hlast,hfloor⟩ := Levels.of_start word last lastFloor (fun i => (path.pattern i).floor) hhigh
  refine ⟨hstart,hlast,fun j => ?_,path.exists_program terminal last hk hfloor⟩
  exact (Levels.tiles_le_start word I terminal last j).trans_eq (congrArg (fun n =>
    Fintype.card (I → Deck (n+1))) hstart)

end StagePath

/-- The quantitative epoch on arbitrary actual placed input leaves. Each
stage's input measurements and output catalog closure follow from a single
preparation selected for that relative catalog, before the integer fan-in
and absolute cover levels. No numerical step estimates are inputs. -/
theorem exists_catalog_epoch (e : PaidIdentity K D m) (hm : 0 < m) :
    ∃ ν : ℝ, 0 < ν ∧ ∃ hSaving : ℝ, 0 < hSaving ∧
    ∀ L A : ℝ, 0 ≤ L → 0 ≤ A → ∃ b : ℕ, 0 < b ∧
    ∀ (hCap : ℝ) (initial : Finset (HyperbolicHost I)),
    (∀ S, Nonempty (StageTemplate e I hCap hSaving ν S)) →
    ∃ path : StagePath b e I hCap hSaving ν, path.catalog 0 = initial ∧
    ∀ Cin Cout : ℝ, 0 ≤ Cin → 0 ≤ Cout →
    ∃ weight : ℝ, 0 < weight ∧ ∃ E : ℝ, 0 < E ∧ ∀ᶠ k : ℕ in atTop, ∃ _hk : 0 < k,
    ∀ {P : Type} {bits : P → ℕ} (last lastFloor high : ℕ), path.threshold last lastFloor ≤ high →
      ∃ F : Program (B := fun i => (path.pattern i).Bin) e (fun n (p : path.State P bits k last high n) => p.val),
        (∀ i c q, (F.advance i c q).val = (F.step i c).result e q) ∧
        ∀ (M : ℝ), 0 ≤ M → ∀ a : Leaves k (path.State P bits k last high 0) b,
          allLeaves (fun p => p.val.length ≤ M * L ∧ p.val.concentration ≤ M * (Cin/weight)) b a →
          ∀ q : (F.system.histories b le_rfl a).Index,
          let out := ((F.system.layer b).state ((F.system.histories b le_rfl a).term q)).val
          (A*out.length + weight*Cout*out.concentration) / (k : ℝ)^b ≤
            M/2 + E * Fintype.card (I → Deck (high+1)) := by
  obtain ⟨ν,hν,hSaving,hh,epoch⟩ := exists_physical_epoch (I := I) e hm
  refine ⟨ν,hν,hSaving,hh,?_⟩
  intro L A hL hA
  obtain ⟨b,hb,calibrate⟩ := epoch L A hL hA
  refine ⟨b,hb,?_⟩
  intro hCap initial prepare
  obtain ⟨path,hpath⟩ := exists_prepared_path (StageTemplate e I hCap hSaving ν)
    (fun _ t => t.nextSites) prepare b initial
  refine ⟨path,hpath,?_⟩
  intro Cin Cout hin hout
  obtain ⟨weight,hw,E,hE,event⟩ := calibrate (fun i => (path.pattern i).Bin)
    (fun i => (path.pattern i).meanFactor) (fun i => (path.pattern i).motionFactor) Cin Cout
    (fun i => (path.pattern i).nonneg.1) (fun i => (path.pattern i).nonneg.2) hin hout
  refine ⟨weight,hw,E,hE,?_⟩
  filter_upwards [event] with k h
  obtain ⟨hk,h⟩ := h
  refine ⟨hk,?_⟩
  intro P bits last lastFloor high hhigh
  obtain ⟨_,_,vol,F,measured,stored⟩ := StagePath.program_at_start (P := P) (bits := bits) path last lastFloor high hhigh hk
  refine ⟨F,stored,?_⟩
  intro M hM a ha q
  exact h (StagePath.depths path last high) (fun n (p : StagePath.State path P bits k last high n) => p.val)
    F M _ hM (Nat.cast_nonneg _) (fun i => by exact_mod_cast vol (i.val+1)) measured a ha q

end Shortening.Adaptive

end BorderVNP
end Computability
end OAI
