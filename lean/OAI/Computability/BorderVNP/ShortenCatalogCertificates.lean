import OAI.Computability.BorderVNP.ShortenCatalogEpoch

/-!
# Keeping additional certificates for the same selected physical operations

A sampled placement can prove both the motion measurements and a public
record update. The program below selects a single jointly certified
operation at every realized child tuple. Thus a capacity or public-row
estimate proved for those same placements remains available after all
adaptive histograms have been chosen.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.Adaptive

open Crossing Epoch PlacedStep
open scoped Classical

variable {D m k b : ℕ} [NeZero D] {I P : Type} [Fintype I] {K : Type*} [Field K]
    {bits : P → ℕ} {e : PaidIdentity K D m} {hCap hSaving ν : ℝ}

/-- Choose all finite templates together with their stronger stage
certificates before selecting a level or fan-in. The successor catalog
is the successor of the same certified template. -/
theorem exists_stage_path_with (b : ℕ) (initial : Finset (HyperbolicHost I))
    (certificate : ∀ S, StageTemplate e I hCap hSaving ν S → Prop)
    (prepare : ∀ S, ∃ t : StageTemplate e I hCap hSaving ν S, certificate S t) :
    ∃ path : StagePath b e I hCap hSaving ν, path.catalog 0 = initial ∧
      ∀ i, certificate (path.catalog i.val) (path.pattern i) := by
  let T := fun S => {t : StageTemplate e I hCap hSaving ν S // certificate S t}
  obtain ⟨p,hp⟩ := exists_prepared_path T (fun _ t => t.val.nextSites)
    (fun S => (prepare S).elim fun t ht => ⟨⟨t,ht⟩⟩) b initial
  exact ⟨⟨p.catalog,fun i => (p.pattern i).val,p.next⟩,hp,fun i => (p.pattern i).property⟩

namespace Program

variable {B : Fin b → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}

/-- Choose and store one concrete step satisfying an arbitrary joint
certificate on the original child tuple. Every local coefficient table,
midpoint, and charged edge is the one from that chosen result. -/
theorem exists_with
    (good : ∀ n, PlacedPack D (Port k P n) (width bits k n) K I (depth n) → Prop)
    (certificate : ∀ (i : Fin b) (c : Fin k → Prepared good i.val),
      PlacedStep m (B i) (depth (i.val+1)) (fun j => (c j).val) → Prop)
    (select : ∀ (i : Fin b) (c : Fin k → Prepared good i.val),
      ∃ s : PlacedStep m (B i) (depth (i.val+1)) (fun j => (c j).val), certificate i c s ∧
        ∀ q : s.Index e, good (i.val+1) (s.result e q)) :
    ∃ F : Program (B := B) e (fun n (p : Prepared good n) => p.val),
      (∀ i c, certificate i c (F.step i c)) ∧
      ∀ i c q, (F.advance i c q).val = (F.step i c).result e q := by
  choose step cert closed using select
  exact ⟨ofClosed e good step closed,cert,fun _ _ _ => rfl⟩

end Program

namespace StagePath

variable (path : StagePath b e I hCap hSaving ν) (last high : ℕ)

set_option maxHeartbeats 800000 in
/-- Select one program carrying both the analytic measurements and any
additional public or resource certificate for the very same stage choices.
The additional selection premise is on a single physical operation per
child tuple, before the profile is chosen. -/
theorem exists_program_with (hk : 0 < k)
    (extra : ∀ (i : Fin b) (c : Fin k → path.State P bits k last high i.val),
      PlacedStep m (path.pattern i).Bin (path.depths last high (i.val+1)) (fun j => (c j).val) → Prop)
    (select : ∀ (i : Fin b) (c : Fin k → path.State P bits k last high i.val),
      ∃ s : PlacedStep m (path.pattern i).Bin (path.depths last high (i.val+1)) (fun j => (c j).val),
        Nonempty (Measurements s hk hSaving ν (path.pattern i).meanFactor (path.pattern i).motionFactor) ∧
        extra i c s ∧ ∀ q : s.Index e, Catalog.PlacedAt (path.catalog (i.val+1)) hCap (s.result e q)) :
    ∃ F : Program (B := fun i => (path.pattern i).Bin) e (fun n (p : path.State P bits k last high n) => p.val),
      (∀ i c, Nonempty (Measurements (F.step i c) hk hSaving ν (path.pattern i).meanFactor
        (path.pattern i).motionFactor)) ∧ (∀ i c, extra i c (F.step i c)) ∧
      ∀ i c q, (F.advance i c q).val = (F.step i c).result e q := by
  let good := fun n (p : PlacedPack D (Port k P n) (width bits k n) K I (path.depths last high n)) =>
    Catalog.PlacedAt (path.catalog n) hCap p
  let cert := fun (i : Fin b) (c : Fin k → Program.Prepared good i.val)
      (s : PlacedStep m (path.pattern i).Bin (path.depths last high (i.val+1)) (fun j => (c j).val)) =>
    Nonempty (Measurements s hk hSaving ν (path.pattern i).meanFactor (path.pattern i).motionFactor) ∧ extra i c s
  have pick (i : Fin b) (c : Fin k → Program.Prepared good i.val) :=
    (select i c).imp fun s hs => show cert i c s ∧ ∀ q : s.Index e, good (i.val+1) (s.result e q) from
      ⟨⟨hs.1,hs.2.1⟩,hs.2.2⟩
  obtain ⟨F,hF,hstore⟩ := Program.exists_with (B := fun i => (path.pattern i).Bin) good cert pick
  exact ⟨F,fun i c => (hF i c).1,fun i c => (hF i c).2,hstore⟩

end StagePath
end Shortening.Adaptive

end BorderVNP
end Computability
end OAI
