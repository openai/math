import OAI.Computability.BorderVNP.PackedBankPublicSubdivisionEpoch
import OAI.Computability.BorderVNP.PackedBankProgramCapacity

/-! # Actual private programs and both tile budgets at each selected inner stage -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.Program

open Cover Crossing Shortening Shortening.Adaptive Packing Packing.Inherited InheritedBank Epoch.Round
open scoped Classical
attribute [local instance] portFintype
set_option maxHeartbeats 1500000

variable {D m k b : ℕ} [NeZero D] {I P K : Type} [Fintype P] [Fintype I] [Field K] {bits : P → ℕ}
    {A : ℕ → Type*} {B : Fin b → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
    {e : PaidIdentity K D m} {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
    (F : Program (B := B) e view) (store : F.SaveNames) (rows : F.SiteRows) (number : e.Entry → ℕ)

/-- Both numerical caps hold for the actual stored programs at each inner depth
and on the original selected summand. -/
theorem replayPrivatePrograms_bankWithin (C : Fin b → ℕ) (cert : ∀ i c, (F.stage i c).RecordFactor e (C i))
    (ex : Bool) (T : ℕ) (hT : 0<T) (n : ℕ) (hn : n≤b) (flat : Fin (k^n) → A 0)
    (pr : ∀ i, Site.Programs (view 0 (flat i)).pack.layout)
    (old : ∀ i, RecordsWithin (view 0 (flat i)) (pr i).bankFields ex T) (q : F.FlatHist n hn flat) :
    let nested := nestedPrivatePrograms (fun x => (view 0 x).pack) n flat pr
    let current := F.replayPrivatePrograms store rows number n hn (leavesEquiv k _ n flat) nested q
    RecordsWithin (F.flatPack n hn flat q) current.bankFields ex ((1+∑ i, loadMultiplier e*C i*k)^n*T) := by
  intro nested current tile
  let data := fun i => (pr i).bankFields
  let saved := F.flatPack n hn flat q
  let fields := F.replayBankRecords store n hn flat data q
  have pub := F.replayPrivatePrograms_public_le store rows number n hn flat data pr (fun _ _ => le_rfl) q
  have pay := F.replayPrivatePrograms_expanded_le store rows number n hn flat data pr (fun _ _ => le_rfl) q
  have loaded := bankRecords_le saved.pack.layout current fields ex (fun v => ⟨pub v,pay v⟩)
    (fun v => Epoch.productTileName (depth n) (saved.site v) = tile)
  exact (Nat.add_le_add_left loaded 1).trans (F.replayBankRecords_bound store C cert ex T hT n hn flat data old q tile)

end PackedHistoryCircuit.Normalized.Program

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Epoch

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Packing Packing.Inherited
  InheritedBank PhysicalEpochs
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1800000

universe u

variable {D m : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ} {e : PaidIdentity K D m}
    {S : SiteSchedule e} {start T : ℕ} {shape : ℕ → PublicCapacity.Shape} {W : ℕ → Type} [∀ t, Fintype (W t)]
    {good : ∀ t, State S start P bits shape W t → Prop} {deep : S.floor+1+S.drop*T ≤ start}
    {t : ℕ} {ht : t<T} {V : ℕ → Type} [∀ i, Fintype (V i)] {w : ℕ → ℕ} (E : Epoch.{u} deep ht good V w)
    (rows : E.F.SiteRows) (number : e.Entry → ℕ) (c : Fin (fan S) → Admissible good t)
    (old : ∀ i, Site.Programs (c i).val.pack.layout)

/-- Actual private banks on an inner subhistory whose leaf occurrences are the
given original subdivided inputs of the outer epoch. -/
noncomputable def partialPrivatePrograms (n : ℕ) (hn : n≤S.rounds) (pick : Fin (S.fanIn^n) → Fin (fan S))
    (q : E.F.FlatHist n hn ((E.run c).flat ∘ pick)) :
    Site.Programs (E.F.flatPack n hn ((E.run c).flat ∘ pick) q).pack.layout :=
  let flat := (E.run c).flat ∘ pick
  let leaf := fun i => E.installedPrivatePrograms rows c old (pick i)
  let nested := nestedPrivatePrograms (fun x => (E.view 0 x).pack) n flat leaf
  E.F.replayPrivatePrograms E.saveNames rows number n hn (leavesEquiv S.fanIn _ n flat) nested q

/-- The attained intermediate programs fit the original child tile cap, times
the actual initial subdivision and one fixed bank factor per selected inner stage. -/
theorem partialPrivatePrograms_bankWithin (ex : Bool) (B : ℕ)
    (cap : ∀ i, SiteCap (c i).val.route (old i).bankFields ex B)
    (n : ℕ) (hn : n≤S.rounds) (pick : Fin (S.fanIn^n) → Fin (fan S)) (q : E.F.FlatHist n hn ((E.run c).flat ∘ pick)) :
    RecordsWithin (E.F.flatPack n hn ((E.run c).flat ∘ pick) q) (E.partialPrivatePrograms rows number c old n hn pick q).bankFields ex
      ((1+∑ i, loadMultiplier e*(S.source.pattern i).record*S.fanIn)^n*
        (1040*(1+3*Fintype.card (Option (allowedMoves (Cube D) S.budget) × Fin (hopCount S.budget S.radius)))*B)) := by
  have fanPos : 0 < fan S := pow_pos S.positiveFanIn _
  have hb : 0 < B := (Nat.add_pos_left (by decide : 0<1) _).trans_le (cap ⟨0,fanPos⟩ 1)
  exact E.F.replayPrivatePrograms_bankWithin E.saveNames rows number (fun i => (S.source.pattern i).record) E.records
    ex _ (by positivity) n hn ((E.run c).flat ∘ pick) (fun i => E.installedPrivatePrograms rows c old (pick i))
    (fun i => E.installedPrivatePrograms_bank_within rows c old ex B cap (pick i)) q

end PackedHistoryCircuit.Normalized.EnrichedOuter.Epoch

end BorderVNP
end Computability
end OAI
