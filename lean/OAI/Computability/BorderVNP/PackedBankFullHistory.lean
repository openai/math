import OAI.Computability.BorderVNP.PackedBankFullProgramFields
import OAI.Computability.BorderVNP.PackedBankFullSubdivisionEpoch
import OAI.Computability.BorderVNP.PackedBankWeightedHistory
import OAI.Computability.BorderVNP.PackedBankPublicHistory

/-! # The full stored compiler load on actual enriched terminal sites -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening

open Crossing Packing
open scoped Classical

private theorem tested_le {A : Type*} [Fintype A] {f g : A → ℕ} (h : ∀ v, f v ≤ g v) (test : A → Prop) :
    testedWidth f test ≤ testedWidth g test := by
  apply Finset.sum_le_sum
  intro v _
  by_cases hv : test v
  · simpa only [hv,ite_true] using h v
  · simp [hv]

/-- The expanded local compiler load bounds either mode on the identical stored fields. -/
theorem localRecords_le_true {D : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (ex : Bool) (prior payload : N.Site → ℕ) (test : N.Site → Prop) :
    localRecords N ex prior payload test ≤ localRecords N true prior payload test := by
  have c (n : ℕ) : recordCost ex n ≤ recordCost true n := by cases ex <;> simp [recordCost]
  unfold localRecords
  apply Nat.add_le_add _ (tested_le (fun v => c (bits v)) _)
  apply Nat.add_le_add _ (tested_le (fun v => c (N.width v)) _)
  exact Nat.add_le_add (tested_le (fun v => Nat.add_le_add_left (c (payload v)) (prior v)) _)
    (tested_le (fun v => c (N.width v)) _)

end Shortening

namespace PackedHistoryCircuit.Normalized

open Crossing Cover Epoch Epoch.Round Shortening Shortening.Adaptive Packing Packing.Inherited PhysicalEpochs
open scoped Classical BorderVNP.Epoch.Cube
open private cap_reindex from OAI.Computability.BorderVNP.PackedSiteRecords
attribute [local instance] portFintype
set_option maxHeartbeats 2400000
set_option maxRecDepth 3000

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)

namespace EnrichedOuter

universe u

variable {S} {P : Type} [Fintype P] {bits : P → ℕ} {start T : ℕ} {shape : ℕ → PublicCapacity.Shape}
    {W : ℕ → Type} [∀ j, Fintype (W j)] {good : ∀ t, State S start P bits shape W t → Prop}
    {deep : S.floor+1+S.drop*T ≤ start}

namespace Epoch

variable {t : ℕ} {ht : t<T} {V : ℕ → Type} [∀ j, Fintype (V j)] {w : ℕ → ℕ}
    (E : Epoch.{u} deep ht good V w) (rows : E.F.SiteRows) (number : e.Entry → ℕ)
    (c : Fin (fan S) → Admissible good t) (old : ∀ j, Site.Programs (c j).val.pack.layout)

/-- The genuine terminal programs charge every one-copy factor table and resolved sweep
to the larger bottom budget, through subdivision, both cable sorts and the final route. -/
theorem privatePrograms_fullCap (ex : Bool) (B : ℕ) (hchild : ∀ j, SiteCap (c j).val.route (old j).fullFields ex B)
    (q : E.F.Hist (E.run c).flat) :
    SiteCap (E.term c q).val.route (E.privatePrograms rows c old number q).fullFields ex (S.publicProgramFactor*B) := by
  let run := E.run c
  let leaf := E.installedPrivatePrograms rows c old
  let data := fun i => (leaf i).fullFields
  let init := 1040*(1+3*Fintype.card (Option (allowedMoves (Cube D) S.budget) × Fin (hopCount S.budget S.radius)))*B
  have hfan : 0 < fan S := pow_pos S.positiveFanIn _
  have hb : 0 < B := (Nat.add_pos_left (by decide : 0 < 1) _).trans_le (hchild ⟨0,hfan⟩ 1)
  have start := E.installedPrivatePrograms_full_within rows c old ex B hchild
  have raw := E.F.flatPrivatePrograms_fullRecords E.saveNames rows number (fun i => (S.source.pattern i).record)
    E.records ex init (by dsimp [init]; positivity) run.flat data leaf (fun _ _ => ⟨le_rfl,le_rfl⟩) start q (run.output.out q)
  let pr := E.privatePrograms rows c old number q
  let fields : RecordData (E.term c q).val.pack.layout := pr.fullFields
  let tested (f : Fintype (Port (fan S) P (t+1))) := @SiteCap D K _ _ f _ _ _ _ (E.term c q).val.pack
    (E.term c q).val.route fields ex (S.publicProgramFactor*B)
  apply (congrArg tested (Subsingleton.elim (portFintype (P := P) (k := fan S) (b := t+1))
    (instFintypeProd (Fin (fan S)) (Port (fan S) P t)))).mpr
  apply (cap_reindex (run.output.out q).routes.flatten (levels S deep ht).2.1 _ ex _).mpr
  intro tile
  exact (raw tile).trans_eq (by unfold SiteSchedule.publicProgramFactor SiteSchedule.bankRecordFactor epochRecordFactor; dsimp only [init]; ring)

end Epoch

namespace Machine

variable {V : ℕ → ℕ → Type} [∀ t i, Fintype (V t i)] {w : ℕ → ℕ → ℕ}
    (M : Machine.{0,u} deep good V w) (rows : ∀ n hn, (M n hn).F.SiteRows) (number : e.Entry → ℕ)

variable (bottom : Admissible good 0) (base : Site.Programs bottom.val.pack.layout)

private theorem stepCap (ex : Bool) : M.StepCapacity rows number Site.staticNodes S.publicProgramFactor ex :=
  fun n hn c old B cap => (M n hn).privatePrograms_fullCap (rows n hn) number c old ex B cap

/-- Each attained history fits the full stored bottom budget with the fixed complete
epoch multiplier, including every retained one-copy factor table. -/
theorem historyPrivatePrograms_fullCap (ex : Bool) (B : ℕ) (hbase : SiteCap bottom.val.route base.fullFields ex B)
    (n : ℕ) (hn : n≤T) (q : (packHistory bottom M.epoch n).Index) :
    SiteCap ((packHistory bottom M.epoch n).term q).val.route
      (M.historyPrivatePrograms rows number bottom base n hn q).fullFields ex (S.publicProgramFactor^n*B) :=
  M.historyPrivatePrograms_weightedCap rows number Site.staticNodes S.publicProgramFactor ex bottom base
    (M.stepCap rows number ex) B hbase n hn q

/-- Full stored and expanded data remain on the same physical site after flattening. -/
theorem terminalPrivatePrograms_fullCap (ex : Bool) (B : ℕ) (hbase : SiteCap bottom.val.route base.fullFields ex B)
    (q : (packHistory bottom M.epoch T).Index) :
    let state := ((packHistory bottom M.epoch T).term q).val
    let pr := M.terminalPrivatePrograms rows number bottom base q
    SiteCap state.route.flatten pr.fullFields ex (S.publicProgramFactor^T*B) :=
  M.terminalPrivatePrograms_weightedCap rows number Site.staticNodes S.publicProgramFactor ex bottom base
    (M.stepCap rows number ex) B hbase q

/-- The actual static and expanded compiler loads at any final coded tile, including
vacant tiles. The single starting budget is for the complete expanded bottom data. -/
theorem terminalPrivatePrograms_fullLoad (B : ℕ) (hbase : SiteCap bottom.val.route base.fullFields true B)
    (q : (packHistory bottom M.epoch T).Index) (code : (Cube D → Deck (depth S start T+1)) ↪ ℕ) (c : ℕ) (ex : Bool) :
    let state := ((packHistory bottom M.epoch T).term q).val
    let N := (flattenPack T state.pack).layout
    let pr := M.terminalPrivatePrograms rows number bottom base q
    let tile := fun v => reduceMove (depth S start T) (state.route.origin v)
    1+localRecords N ex (fun v => (pr v).program.staticNodes) (fun v => (pr v).program.expandedLoad)
      (fun v => code (tile v) = c) ≤ S.publicProgramFactor^T*B := by
  intro state N pr tile
  have bound := M.terminalPrivatePrograms_fullCap rows number bottom base true B hbase q
  have hx := localRecords_le_true N ex pr.fullFields.prior pr.fullFields.payload (fun v => code (tile v) = c)
  apply (Nat.add_le_add_left hx 1).trans
  by_cases h : ∃ t, code t = c
  · obtain ⟨t,rfl⟩ := h
    simp only [Function.Embedding.apply_eq_iff_eq]
    exact bound t
  · have empty (v : N.Site) : code (tile v) ≠ c := fun eq => h ⟨_,eq⟩
    simp only [localRecords,testedWidth,empty,ite_false,Finset.sum_const_zero,Nat.add_zero]
    exact (Nat.le_add_right 1 _).trans (bound 1)

end Machine
end EnrichedOuter
end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
