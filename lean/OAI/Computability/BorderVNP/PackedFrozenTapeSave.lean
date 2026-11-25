import OAI.Computability.BorderVNP.PackedFrozenTapeNamed
import OAI.Computability.BorderVNP.PackedFrozenTapeSections
import OAI.Computability.BorderVNP.PackedHistoryPrivateNamedRows

/-! # Public row sections on the exact sparse name table of a named save -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape

open Crossing Cover Shortening Shortening.Adaptive Shortening.CombiningStep Shortening.StaticRows Shortening.PublicParallel
open PackedHistoryCircuit PackedHistoryCircuit.Normalized Epoch Epoch.Round Diagonal.ExternalSew Diagonal.CellEntries
open VPVNP.VerifierNetwork (Frame)
open private live_old from OAI.Computability.BorderVNP.PackedFrozenTapeNamed
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1800000

variable {D m b k : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
variable {e : PaidIdentity K D m} {h H ν : ℝ} {path : SourcePath b e h H ν} {last high : ℕ}
variable {V E cap : ℕ → ℕ} {w : ℕ} {Extra : ℕ → Type*}
variable {keep : ∀ t, path.NamedAt last high V E w P bits k Extra t → Prop} {hk : 0<k}
variable {nodes : ∀ i : Fin b, path.Node last high V E w k i}
variable (run : path.NamedRun last high V E w cap keep hk nodes) (i : Fin b)
variable (c : Fin k → NamedState.Admissible (path.NamedGood last high V E w cap keep) i.val)
variable (hist : (run.program.stage i c).Index e)
variable {R B : Type*} [Fintype R] [Fintype B] (S : Schema R B)
variable {d d' : ℕ} (oldRoom : V i.val ≤ 2^d) (newRoom : k*V i.val ≤ 2^d')
variable (f : Frame (Fin k × Pins R B d) (Fin k × Pins R B d'))
variable (carry : Carries (Fin.castLEEmb oldRoom) (Fin.castLEEmb newRoom) f) (x : Fin k × Pins R B d → Bool)
variable (states : ∀ j : Fin k, (c j).val.placed.pack.layout.Site → Site)
variable (image : ∀ j, S.Image (fun z => x (j,z)) ((c j).val.names.sites.trans Fin.valEmbedding) (states j))

local notation3 "dir" => run.directory i c hist

include carry image in
set_option maxHeartbeats 1800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The carried child tape is a complete old-row section in the very same
physical directory used to save the chosen histogram. -/
theorem carried_section :
    (S.parallel k).Section ((f.eval x) ∘ parallelPin) ((dir).sites.trans Fin.valEmbedding)
      (fun v => v.elim (fun z => (states z.1 z.2).rows) (fun _ => [])) := by
  have old := live_old i c S oldRoom x states image
  constructor
  · rintro ⟨j,a⟩ hrow alive
    have ha : a ∈ S.rows := by
      change (j,a) ∈ (List.finRange k).flatMap (fun t => S.rows.map (t,·)) at hrow
      obtain ⟨t,_,hm⟩ := List.mem_flatMap.mp hrow
      obtain ⟨u,ha,hz⟩ := List.mem_map.mp hm
      have hu : u = a := congrArg Prod.snd hz
      exact hu ▸ ha
    have present : x (j,.inl (a,.inl ())) = true := (carry.active x j a) ▸ alive
    obtain ⟨v,hv⟩ := (image j).owners a ha present
    have he := carry.owner x j a ((c j).val.names.sites v) hv
    exact ⟨.inl ⟨j,v⟩,he.trans (SourcePath.NamedRun.retained_sites path last high V E w cap keep hk run i c hist ⟨j,v⟩).symm⟩
  · rintro (⟨j,v⟩|⟨a,v⟩)
    · rw [S.parallel_at]
      change _ = ((states j v).rows.map marked)
      have key := SourcePath.NamedRun.retained_sites path last high V E w cap keep hk run i c hist ⟨j,v⟩
      change ((dir).sites (.inl ⟨j,v⟩)).val = ((Fin.castLEEmb newRoom) (flat j ((c j).val.names.sites v))).val at key
      rw [show ((dir).sites.trans Fin.valEmbedding) (.inl ⟨j,v⟩) = _ from key,
        parallel_rows S (Fin.castLEEmb oldRoom) (Fin.castLEEmb newRoom) f carry x old]
      exact (image j).records v
    · rw [S.parallel_at]
      change _ = []
      apply fresh_rows S (Fin.castLEEmb oldRoom) (Fin.castLEEmb newRoom) f carry x old
      obtain ⟨_,seed,names⟩ := run.site_numbers i c
      intro j u
      change (flat j u).val ≠ ((dir).sites (.inr ⟨a,v⟩)).val
      rw [names]
      have bound : k*V i.val ≤
          ((siteRows e (run.program.stage i c).input (parallelName fun j => (c j).val.names.sites)
            seed.toEmbedding) (.inr ⟨a,v⟩)).val := Nat.le_add_right _ _
      exact Nat.ne_of_lt ((flat j u).isLt.trans_le bound)

section Dense

variable {Q : Type} {widths : Q → ℕ} {D' lev nSite nEdge : ℕ} {K' : Type}
    {fin fin' : Fintype Q} {d₀ : ℕ} (before after : PlacedPack D' Q widths K' (Cube D') lev)
    (source : Directory before nSite nEdge) (saved : Directory after nSite nEdge)
    (st : after = before.dense source.cables) (names : HEq saved source.dense)
    (programs : @Site.Programs D' Q fin widths before.pack.layout) (bits₀ : Pins R B d₀ → Bool)

omit [Fintype R] [Fintype B] in
include names in
/-- After the stable cable sort, the saved host has the same public row fields and
the exact program transported by the concrete private history recursion. -/
theorem dense_image (h : S.Image bits₀ (source.sites.trans Fin.valEmbedding) (fun v => (programs v).program)) :
    S.Image bits₀ (saved.sites.trans Fin.valEmbedding)
      (fun v => (carryPrivatePrograms before after source.cables st (fin' := fin') programs v).program) := by
  subst after
  cases eq_of_heq names
  exact h

end Dense

end Packing.Inherited.FrozenTape

end BorderVNP
end Computability
end OAI
