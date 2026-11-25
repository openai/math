import OAI.Computability.BorderVNP.PackedBankWeightedHistory
import OAI.Computability.BorderVNP.PackedBankPublicSubdivisionEpoch
import OAI.Computability.BorderVNP.PackedBankEpochFactors
import OAI.Computability.BorderVNP.PackedBankPublicCell

/-! # Public descriptor capacity through the actual enriched outer history

The genuine subdivided site programs pay for their newly installed ties and
relay rows. The normalized replay then follows the machine's original branch
ordinals, its chosen cable sorts, and its final routing. Only public fields,
guards, and references enter the resulting routed descriptor cap.
-/

namespace OAI
namespace Computability
namespace BorderVNP

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

/-- The actual enriched terminal programs are bounded from their original child programs
in descriptor mode, including subdivision, both cable orders, and the final route. -/
theorem privatePrograms_bankCap (ex : Bool) (B : ℕ) (hchild : ∀ j, SiteCap (c j).val.route (old j).bankFields ex B)
    (q : E.F.Hist (E.run c).flat) :
    SiteCap (E.term c q).val.route (E.privatePrograms rows c old number q).bankFields ex (S.publicProgramFactor*B) := by
  let run := E.run c
  let leaf := E.installedPrivatePrograms rows c old
  let data := fun i => (leaf i).bankFields
  let init := 1040*(1+3*Fintype.card (Option (allowedMoves (Cube D) S.budget) × Fin (hopCount S.budget S.radius)))*B
  have hfan : 0 < fan S := pow_pos S.positiveFanIn _
  have hb : 0 < B := (Nat.add_pos_left (by decide : 0 < 1) _).trans_le (hchild ⟨0,hfan⟩ 1)
  have start := E.installedPrivatePrograms_bank_within rows c old ex B hchild
  have raw := E.F.flatPrivatePrograms_bankRecords E.saveNames rows number (fun i => (S.source.pattern i).record)
    E.records ex init (by dsimp [init]; positivity) run.flat data leaf (fun _ _ => ⟨le_rfl,le_rfl⟩) start q (run.output.out q)
  let pr := E.privatePrograms rows c old number q
  let fields : RecordData (E.term c q).val.pack.layout := pr.bankFields
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

private theorem stepCapacity (ex : Bool) : M.StepCapacity rows number Site.publicNodes S.publicProgramFactor ex :=
  fun n hn c old B cap => (M n hn).privatePrograms_bankCap (rows n hn) number c old ex B cap

variable (bottom : Admissible good 0) (base : Site.Programs bottom.val.pack.layout)

/-- Both the descriptor and expanded modes have a fixed per-epoch multiplier
on the attained program, starting from its actual bottom public fields and work. -/
theorem historyPrivatePrograms_bankCap (ex : Bool) (B : ℕ) (hbase : SiteCap bottom.val.route base.bankFields ex B)
    (n : ℕ) (hn : n ≤ T) (q : (packHistory bottom M.epoch n).Index) :
    SiteCap ((packHistory bottom M.epoch n).term q).val.route
      (M.historyPrivatePrograms rows number bottom base n hn q).bankFields ex (S.publicProgramFactor^n*B) :=
  M.historyPrivatePrograms_weightedCap rows number Site.publicNodes S.publicProgramFactor ex bottom base
    (M.stepCapacity rows number ex) B hbase n hn q

/-- Descriptor-mode cap on each actual selected outer program. Its prior counts the
public row words, guard words, and references printed by that program. -/
theorem historyPrivatePrograms_publicCap (B : ℕ) (hbase : SiteCap bottom.val.route base.bankFields false B)
    (n : ℕ) (hn : n ≤ T) (q : (packHistory bottom M.epoch n).Index) :
    SiteCap ((packHistory bottom M.epoch n).term q).val.route
      (M.historyPrivatePrograms rows number bottom base n hn q).bankFields false (S.publicProgramFactor^n*B) :=
  M.historyPrivatePrograms_bankCap rows number bottom base false B hbase n hn q

/-- Sum of the genuinely printed public row words in an actual routed tile of the
terminal history, with the same original profile ordinal and bottom public budget. -/
theorem historyPrivatePrograms_publicWords (B : ℕ) (hbase : SiteCap bottom.val.route base.bankFields false B)
    (n : ℕ) (hn : n ≤ T) (q : (packHistory bottom M.epoch n).Index) (tile) :
    let state := ((packHistory bottom M.epoch n).term q).val
    let pr := M.historyPrivatePrograms rows number bottom base n hn q
    1+testedWidth (fun v => (CellSparse.Packet.fieldList CellSparse.Packet.record (pr v).program.rows).length)
      (fun v => reduceMove (depth S start n) (state.route.origin v) = tile) ≤ S.publicProgramFactor^n*B := by
  intro state pr
  have fields := publicWords_le_localRecords state.pack.layout (fun v => (pr v).program) pr.bankFields.prior
    pr.bankFields.payload (fun _ => le_rfl) (fun v => reduceMove (depth S start n) (state.route.origin v) = tile)
  exact (Nat.add_le_add_left fields 1).trans (M.historyPrivatePrograms_publicCap rows number bottom base B hbase n hn q tile)

/-- Both budgets survive the genuine final flattening from nested copy ports to
their row-major flat numbers, for the returned physical programs. -/
theorem terminalPrivatePrograms_bankCap (ex : Bool) (B : ℕ) (hbase : SiteCap bottom.val.route base.bankFields ex B)
    (q : (packHistory bottom M.epoch T).Index) :
    let state := ((packHistory bottom M.epoch T).term q).val
    let pr := M.terminalPrivatePrograms rows number bottom base q
    SiteCap state.route.flatten pr.bankFields ex (S.publicProgramFactor^T*B) :=
  M.terminalPrivatePrograms_weightedCap rows number Site.publicNodes S.publicProgramFactor ex bottom base
    (M.stepCapacity rows number ex) B hbase q

/-- The final cell's exact public directory load is bounded for any injective
integer numbering of the actual rounded host tiles, including vacant cells. -/
theorem terminalPrivatePrograms_publicLoad (B : ℕ) (hbase : SiteCap bottom.val.route base.bankFields false B)
    (q : (packHistory bottom M.epoch T).Index) (code : (Cube D → Deck (depth S start T+1)) ↪ ℕ) (c : ℕ) :
    let state := ((packHistory bottom M.epoch T).term q).val
    let N := (flattenPack T state.pack).layout
    let pr := M.terminalPrivatePrograms rows number bottom base q
    let tile := fun v => reduceMove (depth S start T) (state.route.origin v)
    1+FinalCell.publicLoad N (fun v => code (tile v)) (fun v => (pr v).program) c ≤ S.publicProgramFactor^T*B := by
  intro state N pr tile
  have bound := M.terminalPrivatePrograms_bankCap rows number bottom base false B hbase q
  by_cases h : ∃ t, code t = c
  · obtain ⟨t,rfl⟩ := h
    simp only [FinalCell.publicLoad,Function.Embedding.apply_eq_iff_eq]
    have zeroPayload : localRecords N false (fun v => (pr v).program.publicNodes) (fun _ => 0) (fun v => tile v = t) =
        localRecords N false pr.bankFields.prior pr.bankFields.payload (fun v => tile v = t) := rfl
    rw [zeroPayload]
    exact bound t
  · have empty (v : N.Site) : code (tile v) ≠ c := fun eq => h ⟨_,eq⟩
    have hz : FinalCell.publicLoad N (fun v => code (tile v)) (fun v => (pr v).program) c = 0 := by
      simp [FinalCell.publicLoad,localRecords,testedWidth,empty]
    rw [hz,Nat.add_zero]
    exact (Nat.le_add_right 1 _).trans (bound 1)

end Machine
end EnrichedOuter
end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
