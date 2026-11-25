import OAI.Computability.BorderVNP.PackedFrozenTapeAssembly
import OAI.Computability.BorderVNP.DiagonalEnrichedNamedRowStep

/-! # Immutable rows on the actual named histogram successor

The public slot of every retained site is its child slot plus the stride of the
child rectangle. The same integer is read from the true saved directory after
its edge-only dense reorder. Every inserted seed site lies beyond that retained
rectangle and begins with an empty inherited tape.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape

open Crossing Cover Shortening Shortening.Adaptive Shortening.CombiningStep Shortening.StaticRows Shortening.PublicParallel
open PackedHistoryCircuit PackedHistoryCircuit.Normalized Epoch Epoch.Round Diagonal.ExternalSew Diagonal.CellEntries
open VPVNP.VerifierNetwork (Frame)
open private storedSiteName from OAI.Computability.BorderVNP.DiagonalEnrichedNamedRowStep
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

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

omit [Fintype R] [Fintype B] in
include image in
private theorem live_old (j : Fin k) (a : R) (ha : a ∈ S.rows) (enabled : x (j,.inl (a,.inl ())) = true) :
    ∃ u, owner (fun z => x (j,z)) a = ((Fin.castLEEmb oldRoom) u).val := by
  obtain ⟨v,hv⟩ := (image j).owners a ha enabled
  exact ⟨(c j).val.names.sites v,hv⟩

set_option maxHeartbeats 1600000 in
include carry image in
/-- At a retained site of the saved named state, the actual carried public array
contains every old record once, in the same physical order. -/
theorem retained_named (j : Fin k) (v : (c j).val.placed.pack.layout.Site) :
    let a := run.program.advance i c hist
    let store := (normalizedStage e (run.program.stage i c) hist).trans
      (Retains.store (namesStorage run.program run.saveNames i c hist))
    (S.parallel k).atSite ((f.eval x) ∘ parallelPin) (a.val.names.sites (store.site ⟨j,v⟩)).val =
      (states j v).rows.map marked := by
  intro a store
  have names := RowTrace.namedSuccessor_site run i c hist j v
  have key : (a.val.names.sites (store.site ⟨j,v⟩)).val =
      ((Fin.castLEEmb newRoom) (flat j ((c j).val.names.sites v))).val := by
    rw [names]
    change j.val*V i.val + ((c j).val.names.sites v).val = ((c j).val.names.sites v).val + V i.val*j.val
    ac_rfl
  rw [key,S.parallel_at,parallel_rows S (Fin.castLEEmb oldRoom) (Fin.castLEEmb newRoom) f carry x
    (live_old i c S oldRoom x states image) j ((c j).val.names.sites v)]
  exact (image j).records v

set_option maxHeartbeats 1600000 in
include carry image in
/-- A seed-bank site in the saved dense result receives only newly emitted rows.
The carried old rectangles contain no live row with that site's key. -/
theorem seed_named (z : ((Cube D → Deck (path.asPath.depth last high (i.val+1)+1)) × (path.pattern i).bins.Bin))
    (v : TemplateSite e) :
    let a := run.program.advance i c hist
    let st := namesStorage run.program run.saveNames i c hist
    (S.parallel k).atSite ((f.eval x) ∘ parallelPin) (a.val.names.sites (st.site (.inr ⟨z,v⟩))).val = [] := by
  intro a st
  obtain ⟨_,seed,eqn⟩ := run.site_numbers i c
  have key := storedSiteName ((run.program.stage i c).result e hist) a.val.placed (run.directory i c hist)
    a.val.names (run.stored i c hist) (run.saved_names i c hist) (.inr ⟨z,v⟩)
  change (a.val.names.sites (st.site (.inr ⟨z,v⟩))).val = ((run.directory i c hist).sites (.inr ⟨z,v⟩)).val at key
  have bound : k*V i.val ≤ (a.val.names.sites (st.site (.inr ⟨z,v⟩))).val := by
    rw [key,eqn hist (.inr ⟨z,v⟩)]
    exact Nat.le_add_right _ _
  rw [S.parallel_at]
  apply fresh_rows S (Fin.castLEEmb oldRoom) (Fin.castLEEmb newRoom) f carry x
    (live_old i c S oldRoom x states image)
  intro j u
  have fit := (flat j u).isLt
  change (flat j u).val ≠ _
  omega

end Packing.Inherited.FrozenTape

end BorderVNP
end Computability
end OAI
