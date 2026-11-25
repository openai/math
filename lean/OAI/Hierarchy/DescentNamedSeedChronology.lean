import OAI.Hierarchy.DescentNamedOriginalArchive
import OAI.Hierarchy.DescentNamedSeedOrigin
import OAI.Hierarchy.DescentCanonicalSeedHistory
import OAI.Hierarchy.DescentWholeEpochs
import OAI.Hierarchy.DescentSeedProjection

namespace OAI
/-! # The initialized physical tape and archive of the named trajectory -/

namespace Hierarchy.DescentSixParty.SeedNamed

open DescentInitialHost DescentCompiler DescentKernelHistory DescentPacking DescentStageEdgeReceipt
open DescentColonies Catalyst
open scoped Classical BigOperators
noncomputable section

variable {F : Type} [Field F]

private theorem schedule_trunk {P : Type} {d : ℕ} {bits : P→ℕ} (G : PoweredGadget F)
    {u ε : ℝ} (he : 0 ≤ ε) {t : ℕ} {H : Histories F d P bits} (run : Schedule G (u:=u) he t H)
    (c : (Schedule.finish G he run).Choice) :
    Chronology.sourceChoice he run c=Schedule.seedChoice G he run c := by
  induction t generalizing H with
  | zero=>rfl
  | succ t ih=>
    obtain ⟨stage,tail⟩:=run
    exact congrArg Sigma.fst (ih tail c)

theorem seedTrunk {P : Type} {d : ℕ} {bits : P→ℕ} (G : PoweredGadget F)
    {u ε : ℝ} (hu : 0 ≤ u) (he : 0 ≤ ε) {J h C ht t : ℕ} {H : Histories F d P bits}
    (run : Epochs G hu he (h:=h) (C:=C) (Ht:=ht) (t:=t) J H) (c : (Epochs.finish G hu he run).Choice) :
    Chronology.epochsSource G run c=Epochs.seedChoice G hu he run c := by
  induction J generalizing H with
  | zero=>rfl
  | succ J ih=>
    let later := run.1.finish G hu he
    have tailEq := ih (H := later) run.2 c
    exact (schedule_trunk G he run.1.subrounds
      (Chronology.epochsSource G (J := J) (H := later) run.2 c)).trans
      (congrArg (Schedule.seedChoice G he run.1.subrounds) tailEq)

variable {cp pins : ℕ} (X : Approximation F cp pins) {G : PoweredGadget F} {S : AtomSchedule}
    {q fee : ℝ} {k z wire s : ℕ}

theorem weight_source {G : PoweredGadget F} {u ε : ℝ} (hu : 0 ≤ u) (he : 0 ≤ ε)
    (R size groups k : ℕ) (digits : Fin R≃Fin groups×Block k) {J h C ht t : ℕ}
    (run : Epochs G hu he (h:=h) (C:=C) (Ht:=ht) (t:=t) J (initial X R size groups k digits))
    (c : (Epochs.finish G hu he run).Choice) :
    (Epochs.finish G hu he run).weight c=(initialGroup X R size).weight
      (Chronology.epochsSource G (hq := hu) (hf := he) (J := J) (h := h) (C := C)
        (ht := ht) (t := t) (H := initial X R size groups k digits) run c) := by
  exact (Epochs.weight_initial G hu he (initial X R size groups k digits) run c).trans
    (congrArg (initialGroup X R size).weight (seedTrunk G hu he run c).symm)

namespace Origin
variable {X} {c : (initialGroup X S.copies s).Choice}
    {digits : Fin S.copies ≃ Fin (S.groupCount 0) × Block k}
    (o : Origin (S:=S) (G:=G) (q:=q) (fee:=fee) (z:=z) (wire:=wire) X c digits)

private abbrev HasPhysicalNames {P : Type} {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {age z' D' : ℕ} (t : Reached W G q fee S k age z' D' wire s) : Prop :=
  letI : Fintype t.V := t.finite
  letI : DecidableEq t.V := t.eqV
  t.placement.SiteNamed (groupRank Fin.valEmbedding (t.vertex.trans Fin.valEmbedding)) ∧
    ∀ e f : W.graph.Edge, (t.order e).val < (t.order f).val ↔
      originalId W.graph.Edge e < originalId W.graph.Edge f

private abbrev physicalCapacity {P : Type} {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {age z' D' : ℕ} (t : Reached W G q fee S k age z' D' wire s) : ℕ :=
  letI : Fintype t.V := t.finite
  letI : DecidableEq t.V := t.eqV
  t.placement.cap

private theorem carried {P : Type} {d : ℕ} {bits : P→ℕ} {W W' : MarkedWorld F d P bits}
    (raw : Reached W G q fee S k 0 z 3 wire s) (eqn : world raw = W') :
    HasPhysicalNames (transport raw eqn) := by
  cases eqn
  exact named raw

private theorem carried_cap {P : Type} {d : ℕ} {bits : P→ℕ} {W W' : MarkedWorld F d P bits}
    (raw : Reached W G q fee S k 0 z 3 wire s) (eqn : world raw = W') :
    physicalCapacity (transport raw eqn) = physicalCapacity raw := by
  cases eqn
  rfl

private abbrev NamingAlongPaths {P : Type} {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    (start : Reached W G q fee S k 0 z 3 wire s) : Prop :=
  ∀ {W' : MarkedWorld F d P bits} {j z' D' : ℕ} {last : Reached W' G q fee S k j z' D' wire s},
    Chronology.Path start last → HasPhysicalNames last

private theorem carryAlongPaths {P : Type} {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    (start : Reached W G q fee S k 0 z 3 wire s) (names : HasPhysicalNames start) :
    NamingAlongPaths start := by
  intro W' j z' D' last path
  cases path with
  | here => exact names
  | ordinary prev step => exact Reached.donor_names _ (Nat.zero_lt_succ _)
  | reset prev step => exact step.next.donor_names (Nat.zero_lt_succ _)

private structure OriginFacts where
  siteAndEdgeNames : Prop
  namesProof : siteAndEdgeNames
  capacityValue : ℕ
  capacityProof : capacityValue = 256
  pathNames : Prop
  pathNamesProof : pathNames

private def transportFacts {P : Type} {d : ℕ} {bits : P→ℕ} {W W' : MarkedWorld F d P bits}
    (r : Reached W G q fee S k 0 z 3 wire s) (eqn : world r = W')
    (bound : physicalCapacity r = 256) : OriginFacts where
  siteAndEdgeNames := HasPhysicalNames (transport r eqn)
  namesProof := carried r eqn
  capacityValue := physicalCapacity (transport r eqn)
  capacityProof := (carried_cap r eqn).trans bound
  pathNames := NamingAlongPaths (transport r eqn)
  pathNamesProof := carryAlongPaths (transport r eqn) (carried r eqn)

include o in
private def factsFor : OriginFacts := by
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let origin ← Lean.Meta.getFVarFromUserName `o
      let source ← Lean.instantiateMVars (← Lean.Meta.mkAppM ``Origin.source #[origin])
      let sa := source.getAppArgs
      unless sa.size == 16 do throwError "unexpected Origin.source arguments"
      let decl ← Lean.getConstInfo ``Origin.source
      let val ← Lean.Core.instantiateValueLevelParams decl source.getAppFn.constLevels!
      let body := (val.beta sa).consumeMData
      unless body.isAppOf ``transport && body.getAppArgs.size == 17 do
        throwError "Origin.source is not a fully applied transport"
      let ta := body.getAppArgs
      -- Infer the generic proof arguments on the original transport telescope.
      let td ← Lean.getConstInfo ``transport
      let template ← Lean.Meta.forallTelescope td.type fun xs _ => do
        unless xs.size == 17 do throwError "unexpected transport telescope"
        let facts ← Lean.Meta.mkAppM ``transportFacts #[xs[15]!, xs[16]!]
        Lean.Meta.mkLambdaFVars xs (← Lean.instantiateMVars facts)
      -- The existing SeedLink from this particular Origin supplies the capacity bound.
      let seed := Lean.mkAppN (Lean.mkConst ``Origin.seed) sa
      let capArgs := #[sa[0]!, sa[1]!, sa[5]!, sa[7]!, sa[8]!, sa[6]!, sa[9]!,
        sa[2]!, sa[3]!, sa[4]!, sa[11]!, sa[12]!, sa[10]!, sa[13]!, ta[15]!, sa[14]!, seed]
      let capProof := Lean.mkAppN (Lean.mkConst ``Chronology.SeedLink.capacity) capArgs
      goal.assign (Lean.mkApp (template.beta ta) capProof)

theorem names : (factsFor o).siteAndEdgeNames := (factsFor o).namesProof

theorem capacity : (factsFor o).capacityValue = 256 := (factsFor o).capacityProof

/-- Every prefix of this actual branch has the order used by the measured donor
decoder, including the prefix before the first nonlinear stage. -/
theorem names_on_path : (factsFor o).pathNames := (factsFor o).pathNamesProof

end Origin

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
