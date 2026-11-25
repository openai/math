import OAI.Computability.BorderVNP.PackedBankPrivateScalarReplay
import OAI.Computability.BorderVNP.PackedBankLocalPopulation
import OAI.Computability.BorderVNP.PackedBankPrivateSubdivisionScalars
import OAI.Computability.BorderVNP.PackedBankPublicHistory
import OAI.Computability.BorderVNP.PackedFlatCompilerRows

/-! # Scalar fields on every attained outer site program

A fixed cover-neighborhood bound controls the old bin population even on empty
hooks. Every birth fits the current expanded tile budget and every retention
fits its site's new extent. The site extent is also charged to the expanded
tile of the actual returned route.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized

open Crossing Cover Epoch Epoch.Round Shortening Shortening.Adaptive Shortening.SeedIntervals Packing Packing.Inherited
  InheritedProfile InheritedBank PhysicalEpochs
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2400000

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)

/-- The number of nearby tile names needed by any one inner stage, fixed by the schedule. -/
noncomputable def SiteSchedule.populationFactor : ℕ :=
  ∑ i : Fin S.rounds, (measured_population_cap (I := Cube D) (B := (S.source.pattern i).bins.Bin) e S.saving).choose

private theorem programFactor_pos : 0 < S.publicProgramFactor := by
  unfold SiteSchedule.publicProgramFactor SiteSchedule.bankRecordFactor epochRecordFactor
  positivity

namespace EnrichedOuter

universe u

variable {S} {P : Type} [Fintype P] {bits : P → ℕ} {start T : ℕ} {shape : ℕ → PublicCapacity.Shape}
    {W : ℕ → Type} [∀ j, Fintype (W j)] {good : ∀ t, State S start P bits shape W t → Prop}
    {deep : S.floor+1+S.drop*T ≤ start}

namespace Epoch

variable {t : ℕ} {ht : t<T} {V : ℕ → Type} [∀ j, Fintype (V j)] {w : ℕ → ℕ}
    (E : Epoch.{u} deep ht good V w)

/-- The geometry certificate on the installed crossing stages of an enriched epoch. -/
abbrev Measures : Prop := ∀ i c, Nonempty ((E.F.stage i c).Measurements S.positiveFanIn S.saving S.tolerance
  (S.source.pattern i).mean (S.source.pattern i).motion)

variable (rows : E.F.SiteRows) (number : e.Entry → ℕ)
    (c : Fin (fan S) → Admissible good t) (old : ∀ j, Site.Programs (c j).val.pack.layout)

/-- All records in the actual program returned by this epoch meet the scalar invariant.
The bound L covers the full expanded epoch starting from the supplied child cap. -/
theorem privatePrograms_scalarBound (hm : 0 < m) (measured : E.Measures) (B L U : ℕ)
    (large : S.publicProgramFactor*B ≤ L) (limit : birthScalarLimit e L (S.populationFactor*L) ≤ U)
    (hchild : ∀ j, SiteCap (c j).val.route (old j).bankFields true B)
    (hscalar : ∀ j v, let s := (old j v).program
      s.ScalarBound (max U (max 1 s.size))) (q : E.F.Hist (E.run c).flat) :
    ∀ v, let s := (E.privatePrograms rows c old number q v).program
         s.ScalarBound (max U (max 1 s.size)) := by
  let run := E.run c
  let leaf := E.installedPrivatePrograms rows c old
  let data := fun i => (leaf i).bankFields
  let subdiv := 1+3*Fintype.card (Option (allowedMoves (Cube D) S.budget) × Fin (hopCount S.budget S.radius))
  let init := 1040*subdiv*B
  let C := fun i => (S.source.pattern i).record
  let stages := (1+∑ i, loadMultiplier e*C i*S.fanIn)^S.rounds
  let f := stages*init
  have fanPos : 0 < fan S := pow_pos S.positiveFanIn _
  have hb : 0 < B := (Nat.add_pos_left (by decide : 0<1) _).trans_le (hchild ⟨0,fanPos⟩ 1)
  have hi : 0 < init := by dsimp [init,subdiv]; positivity
  have eq : (1+S.finalCap)*f = S.publicProgramFactor*B := by
    change (1+S.finalCap)*(stages*(1040*subdiv*B)) = 1040*((1+S.finalCap)*stages*subdiv)*B
    ring
  have hbig : f ≤ L := ((Nat.le_mul_of_pos_left f (show 0 < 1+S.finalCap by omega)).trans_eq eq).trans large
  have leafCap := E.installedPrivatePrograms_bank_within rows c old true B hchild
  have initial := nestedPrivatePrograms_forall (fun x => (E.view 0 x).pack) (fun s => s.ScalarBound (max U (max 1 s.size)))
    _ run.flat leaf (E.installedPrivatePrograms_scalarBound rows c old U hscalar)
  apply E.F.replayPrivatePrograms_scalarBound E.saveNames rows number hm C E.records init hi L S.populationFactor U hbig
    ?_ limit S.rounds le_rfl run.flat data leafCap _ initial q
  intro i states hist prior payload s cap a
  have N := measured_population_cap (I := Cube D) (B := (S.source.pattern i).bins.Bin) e S.saving
  have found := N.choose_spec S.positiveFanIn (fun j => E.view i.val (states j)) s (measured i states).some hist prior payload L cap a
  have card : N.choose ≤ S.populationFactor := Finset.single_le_sum
    (f := fun j => (measured_population_cap (I := Cube D) (B := (S.source.pattern j).bins.Bin) e S.saving).choose)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  exact found.trans (Nat.mul_le_mul_right L card)

end Epoch

namespace Machine

variable {V : ℕ → ℕ → Type} [∀ t i, Fintype (V t i)] {w : ℕ → ℕ → ℕ}
    (M : Machine.{0,u} deep good V w) (rows : ∀ n hn, (M n hn).F.SiteRows) (number : e.Entry → ℕ)

private theorem step_scalarBound (hm : 0 < m) {n : ℕ} (hn : n<T) (measured : (M n hn).Measures)
    (c : Fin (fan S) → Admissible good n) (old : ∀ j, Site.Programs (c j).val.pack.layout) (B L U : ℕ)
    (large : S.publicProgramFactor*B ≤ L) (limit : birthScalarLimit e L (S.populationFactor*L) ≤ U)
    (hchild : ∀ j, SiteCap (c j).val.route (old j).bankFields true B)
    (hscalar : ∀ j v, let s := (old j v).program
      s.ScalarBound (max U (max 1 s.size))) (q : (M.epoch n c).Index) :
    ∀ v, let s := (M.stepPrivatePrograms rows number hn c old q v).program
         s.ScalarBound (max U (max 1 s.size)) := by
  let family (z : ProfileSum (Admissible good (n+1))) := (j : z.Index) → Site.Programs (z.term j).val.pack.layout
  let Q := fun s : Site => s.ScalarBound (max U (max 1 s.size))
  have carry {z y : ProfileSum (Admissible good (n+1))} (he : z = y) (f : family y) (h : ∀ j v, Q (f j v).program) :
      ∀ j : z.Index, ∀ v, Q (((Eq.mpr (congrArg family he) f) j) v).program := by
    subst y
    exact h
  have he : M.epoch n c = (M n hn).choice c := dite_eq_left hn
  exact carry he ((M n hn).privatePrograms (rows n hn) c old number)
    ((M n hn).privatePrograms_scalarBound (rows n hn) number c old hm measured B L U large limit hchild hscalar) q

variable (bottom : Admissible good 0) (base : Site.Programs bottom.val.pack.layout)

/-- Uniform raw scalar bound through every attained outer epoch. The sole numerical
growth in the tile budget is the schedule's fixed exponential factor. -/
theorem historyPrivatePrograms_scalarBound (hm : 0 < m) (measured : ∀ n hn, (M n hn).Measures) (B U : ℕ)
    (hcap : SiteCap bottom.val.route base.bankFields true B)
    (limit : let L := S.publicProgramFactor^T*B
      birthScalarLimit e L (S.populationFactor*L) ≤ U)
    (hbase : ∀ v, let s := (base v).program
      s.ScalarBound (max U (max 1 s.size))) (n : ℕ) (hn : n≤T) (q : (packHistory bottom M.epoch n).Index) :
    ∀ v, let s := (M.historyPrivatePrograms rows number bottom base n hn q v).program
         s.ScalarBound (max U (max 1 s.size)) := by
  induction n with
  | zero => exact hbase
  | succ n ih =>
    let hn' := Nat.le_of_succ_le hn
    let child := fun j => (packHistory bottom M.epoch n).term (q.1 j)
    let old := fun j => M.historyPrivatePrograms rows number bottom base n hn' (q.1 j)
    have large : S.publicProgramFactor*(S.publicProgramFactor^n*B) ≤ S.publicProgramFactor^T*B := by
      rw [←Nat.mul_assoc,←pow_succ']
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (programFactor_pos S) hn)
    exact M.step_scalarBound rows number hm (Nat.lt_of_succ_le hn) (measured _ _) child old (S.publicProgramFactor^n*B)
      (S.publicProgramFactor^T*B) U large limit
      (fun j => M.historyPrivatePrograms_bankCap rows number bottom base true B hcap n hn' (q.1 j)) (fun j => ih hn' (q.1 j)) q.2

/-- Every numerical word actually printed by a terminal program fits the maximum
of the scalar limit and its final expanded tile budget, before final cell relocation. -/
theorem terminalPrivatePrograms_scalarBound (hm : 0 < m) (measured : ∀ n hn, (M n hn).Measures) (B U : ℕ)
    (hcap : SiteCap bottom.val.route base.bankFields true B)
    (limit : let L := S.publicProgramFactor^T*B
      birthScalarLimit e L (S.populationFactor*L) ≤ U)
    (hbase : ∀ v, let s := (base v).program
      s.ScalarBound (max U (max 1 s.size))) (q : (packHistory bottom M.epoch T).Index) (v) :
    (M.terminalPrivatePrograms rows number bottom base q v).program.ScalarBound (max U (S.publicProgramFactor^T*B)) := by
  let state := ((packHistory bottom M.epoch T).term q).val
  let pr := M.historyPrivatePrograms rows number bottom base T le_rfl q
  let tile := fun u => reduceMove (depth S start T) (state.route.origin u)
  have h := M.historyPrivatePrograms_scalarBound rows number bottom base hm measured B U hcap limit hbase T le_rfl q v
  have cap := M.historyPrivatePrograms_bankCap rows number bottom base true B hcap T le_rfl q (tile v)
  have loaded := payload_incoming_le state.pack.layout pr.bankFields.prior pr.bankFields.payload v (fun u => tile u = tile v) rfl
  have extent : (pr v).program.size ≤ pr.bankFields.payload v+incoming state.pack.layout v :=
    Nat.add_le_add (Nat.le_add_right _ _) (pr v).size.le
  have bound : max 1 (pr v).program.size ≤ S.publicProgramFactor^T*B :=
    max_le ((Nat.le_add_right 1 _).trans cap) (extent.trans (loaded.trans ((Nat.le_add_left _ 1).trans cap)))
  exact fun a ha => (h a ha).trans (max_le_max_left _ bound)

/-- A closed local scalar limit from the physical bottom word limit and the routed
expanded budget. Its coefficient is fixed before the number of outer epochs. -/
theorem terminalPrivatePrograms_localScalars_of_extent (hm : 0 < m) (measured : ∀ n hn, (M n hn).Measures) (B U₀ : ℕ)
    (hcap : SiteCap bottom.val.route base.bankFields true B) (hbase : ∀ v, let s := (base v).program
      s.ScalarBound (max U₀ (max 1 s.size)))
    (q : (packHistory bottom M.epoch T).Index) (v) :
    let L := S.publicProgramFactor^T*B
    let C := (birthWordCoefficient e+8)*(BankCharges.bound e+1)*(S.populationFactor+2)
    (M.terminalPrivatePrograms rows number bottom base q v).program.ScalarBound (max U₀ (C*(L+1))) := by
  intro L C
  let U := max U₀ (C*(L+1))
  have budget : L+S.populationFactor*L+1 ≤ (S.populationFactor+2)*(L+1) := by ring_nf; omega
  have scaled : birthScalarLimit e L (S.populationFactor*L) ≤ C*(L+1) :=
    (birthScalarLimit_le e L (S.populationFactor*L)).trans
      ((Nat.mul_le_mul_left _ budget).trans_eq (by dsimp [C]; ring))
  have bound : L ≤ C*(L+1) := (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (by dsimp [C]; positivity))
  have h := M.terminalPrivatePrograms_scalarBound rows number bottom base hm measured B U hcap
    (scaled.trans (le_max_right ..)) (fun v a ha => (hbase v a ha).trans (max_le_max_right _ (le_max_left ..))) q v
  exact fun a ha => (h a ha).trans (max_le le_rfl (bound.trans (le_max_right ..)))

/-- A uniform scalar bound on the bottom itself suffices for the same terminal word limit. -/
theorem terminalPrivatePrograms_localScalars (hm : 0 < m) (measured : ∀ n hn, (M n hn).Measures) (B U₀ : ℕ)
    (hcap : SiteCap bottom.val.route base.bankFields true B) (hbase : ∀ v, (base v).program.ScalarBound U₀)
    (q : (packHistory bottom M.epoch T).Index) (v) :
    let L := S.publicProgramFactor^T*B
    let C := (birthWordCoefficient e+8)*(BankCharges.bound e+1)*(S.populationFactor+2)
    (M.terminalPrivatePrograms rows number bottom base q v).program.ScalarBound (max U₀ (C*(L+1))) :=
  M.terminalPrivatePrograms_localScalars_of_extent rows number bottom base hm measured B U₀ hcap
    (fun v a ha => (hbase v a ha).trans (le_max_left ..)) q v

end Machine
end EnrichedOuter
end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
