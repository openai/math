import OAI.Computability.VPVNP.CompressorLevelCounts
import OAI.Computability.VPVNP.CompressorTermRecordScan

/-!
# Native term rows for the selected shrinking and refresh levels

Both kinds of level run a fixed demand/supply grid. The finite row family
below uses the original pass's choice at the actual motif or port block.
Consequently a successful scan writes the demand grid point, repetition
count and supply coordinates for that same branch. Its charged probes
depend on the number of motifs and fixed grid, while the local arithmetic
also depends on the word width.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

open scoped Classical

namespace CompressorRecords.SelectedTerms

open Compression PairSimulation.LocalHistory MotifGrid MotifBlocks MotifSelector MotifConversion BurstRAM

/-- A single fixed grid, with the physical order of its demand and supply columns. -/
structure Grid (k : Type*) [_root_.Field k] where
  /-- Vertex set shared by the demand and supply graphs of this motif. -/
  J : Type
  /-- Index set for the motif's demand edges. -/
  D : Type
  /-- Index set for the motif's supply edges. -/
  E : Type
  [jFinite : Fintype J]
  [dFinite : Fintype D]
  [eFinite : Fintype E]
  /-- Source vertex of each demand edge. -/
  src : D → J
  /-- Target vertex of each demand edge. -/
  dst : D → J
  /-- Supply graph on the motif vertices with edges indexed by `E`. -/
  graph : Supply J E
  /-- Positive rational weight used to measure the demand on each demand edge. -/
  p : D → ℚ
  /-- Positive rational weight used to measure the payload on each supply edge. -/
  q : E → ℚ
  /-- Demand-to-supply energy comparison constant used to construct the strict grid. -/
  comparison : ℝ
  /-- Coefficient of the squared demand norm in the padded supply-energy bound. -/
  relaxed : ℝ
  /-- Fixed motif identities and width bounds for these edges, weights, and comparison
  constants. -/
  block : FixedBlock k src dst graph (realWidths p) (realWidths q) comparison relaxed
  pPos : ∀ i, 0 < p i
  qPos : ∀ i, 0 < q i
  /-- Physical order of the demand columns in each motif row. -/
  demandOrder : Order D
  /-- Physical order of the supply columns in each selected term record. -/
  supplyOrder : Order E

attribute [instance] Grid.jFinite Grid.dFinite Grid.eFinite

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
variable {R : Type*} [CommRing R] {f : B.Entry → R} {hf : B.IsSolution f}

/-- Grid for the six-vertex shrinking motif, with two demand columns and eight supply columns. -/
def shrinkGrid (B : S.Templates) : Grid k where
  J := Fin 6
  D := Bool
  E := Bool × Fin 4
  src := ShrinkMotif.demandSource
  dst := ShrinkMotif.demandTarget
  graph := ShrinkMotif.supply
  p := ShrinkMotif.demandMass
  q := ShrinkMotif.supplyMass
  comparison := 31/16
  relaxed := shrinkComparison
  block := B.shrink
  pPos := ShrinkMotif.demandMass_pos
  qPos := ShrinkMotif.supplyMass_pos
  demandOrder := ⟨2,finTwoEquiv⟩
  supplyOrder := Order.prod ⟨2,finTwoEquiv⟩ (Order.fin 4)

/-- Grid for a refresh block, with tie demands and supply edges indexed by port and expander
slot. -/
def refreshGrid (B : S.Templates) : Grid k where
  J := Fin (2^S.portExponent)
  D := DegreeRefresh.Tie (2^S.portExponent)
  E := Fin (2^S.portExponent) × Fin (2^S.expanderExponent)
  src := Refresh.tieSource
  dst := Refresh.tieTarget
  graph := S.portSupply
  p := Refresh.tieMass
  q := Refresh.expanderMass S.baseDegree
  comparison := S.portComparison
  relaxed := S.portComparison+1
  block := B.refresh
  pPos _ := zero_lt_one
  qPos _ := by unfold Refresh.expanderMass BlockSchedule.baseDegree; positivity
  demandOrder := ⟨_, (Fintype.equivFin _).symm⟩
  supplyOrder := (Order.fin (2 ^ S.portExponent)).prod (Order.fin (2 ^ S.expanderExponent))

variable {a g b n : ℕ} {X : State a g} {p : StatePass R X b n}

/-- Select the shrinking or refresh grid according to the pass origin. -/
def grid : (o : PassOrigin B f hf p) → Grid k
  | .shrink .. => shrinkGrid B
  | .refresh .. => refreshGrid B

/-- Actual input and selected output rows of the grid, in the same motif order
as the compression pass. -/
structure Batch (G : Grid k) (m M : ℕ) where
  /-- Width requested on each demand edge at each physical motif ordinal. -/
  demand : Fin m → G.D → ℕ
  bound : ∀ i e, demand i e ≤ M
  /-- Selected admissible term for the demand row at each motif ordinal. -/
  choice : TermRecordScan.Choices G.block demand

set_option maxHeartbeats 1800000 in
/-- Arrange the actual pass demands and selected terms in physical motif order. -/
def batch (o : PassOrigin B f hf p) (c : p.step.Choice) :
    Batch (grid o) o.motifCount X.maxWireWidth := by
  cases o with
  | shrink i h X =>
    subst h
    let ids := shrinkMotifOrder X
    refine ⟨fun j ↦ X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth (ids.entries j),
      fun j e ↦ ?_,fun j ↦ c (ids.entries j)⟩
    exact X.packingData.shrinkDemandWidths_le (State.two_le_packingColors _) (Nat.two_pow_pos _)
      X.shrinkNumber X.packingWidth (fun _ ↦ X.width_le_maxWireWidth _) _ e
  | refresh X =>
    let ids := (Order.prod ⟨_,X.baseIndex.symm⟩ ⟨_,(bitWordFinEquiv n).symm⟩)
    refine ⟨fun j ↦ Refresh.blockDemandWidths (Refresh.splitSlots X) (bitWordFinEquiv _)
      (Refresh.splitWidths X) (ids.entries j),fun j e ↦ ?_,fun j ↦ c (ids.entries j)⟩
    change Refresh.internalWidth _ _ (ids.entries j) e ≤ X.maxWireWidth
    unfold Refresh.internalWidth
    split <;> exact X.width_le_maxWireWidth _

namespace Grid

variable (G : Grid k)

/-- Number of demand columns scanned in one motif row. -/
abbrev d := G.demandOrder.length
/-- Number of supply columns written in one motif row. -/
abbrev e := G.supplyOrder.length

/-- Fixed contribution to the word width required by this grid's term-record scan. -/
def fitConstant : ℕ := (TermRecordScan.run_spec G.block G.demandOrder.entries G.supplyOrder.entries G.pPos G.qPos).choose

/-- Upper bound on the cost of scanning one motif, counting the five native calls and the probe
bound for one term row. -/
def charge : ℕ := 5 + TermRecordScan.probesPerRow G.block G.d G.e

/-- Grid-dependent coefficient in the event bound for one row as a function of word width and
log demand width. -/
def stepConstant : ℕ :=
  6*G.d + (11*G.d+4)*G.block.grid.demands.toList.length + 8 +
    6*G.d + 7*(∑ i, MotifAdmission.weight G.p i).size + 10 + 8 +
    12*G.e + 2*(G.block.scale*G.block.radius.num.natAbs).size +
    4*(MotifAdmission.denominator G.q).size + 20 + 14 + 4*G.e

theorem steps_le (w M : ℕ) : TermRecordScan.eventsPerRow G.block G.d G.e w M ≤
    G.stepConstant * (w + Nat.clog 2 (M+1) + 1) := by
  have hp := PayloadWrite.storedFuel_le G.block G.e w
  let l := Nat.clog 2 (M+1)
  have hsteps : TermRecordScan.eventsPerRow G.block G.d G.e w M ≤ G.stepConstant + 14*l + (4*G.e)*w := by
    dsimp only [TermRecordScan.eventsPerRow,TermRecordScan.prepFuel,stepConstant,l]
    ring_nf at hp ⊢
    omega
  have h14 : 14 ≤ G.stepConstant := by unfold stepConstant; omega
  have h4e : 4*G.e ≤ G.stepConstant := by unfold stepConstant; omega
  calc
    _ ≤ G.stepConstant + 14*l + (4*G.e)*w := hsteps
    _ ≤ G.stepConstant + G.stepConstant*l + G.stepConstant*w := Nat.add_le_add
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ h14) _) (Nat.mul_le_mul_right _ h4e)
    _ = _ := by dsimp only [l]; ring

end Grid

/-- Common per-row call and probe charge for the two pass grids. -/
def phaseConstant (B : S.Templates) : ℕ := max (shrinkGrid B).charge (refreshGrid B).charge

/-- Maximum fixed word-width allowance for the shrinking and refresh term-record scans. -/
def fitConstant (B : S.Templates) : ℕ := max (shrinkGrid B).fitConstant (refreshGrid B).fitConstant

/-- Common coefficient in the per-row event bound for the shrinking and refresh grids. -/
def stepConstant (B : S.Templates) : ℕ := max (shrinkGrid B).stepConstant (refreshGrid B).stepConstant

private theorem grid_bounds (o : PassOrigin B f hf p) : (grid o).charge ≤ phaseConstant B ∧
    (grid o).fitConstant ≤ fitConstant B ∧ (grid o).stepConstant ≤ stepConstant B := by
  cases o with
  | shrink => exact ⟨le_max_left ..,le_max_left ..,le_max_left ..⟩
  | refresh => exact ⟨le_max_right ..,le_max_right ..,le_max_right ..⟩

private theorem count_log {w : ℕ} (rs : List (Report w)) :
    RAMBuckets.probeCount Report.probes rs = countProbes (eventLog rs) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [RAMBuckets.probeCount,eventLog,List.flatMap_cons,DemandPreparation.probes_append]
    rw [ih]
    rfl

/-- The real five-call scans for all terms of one selected level. The
input is the physical demand array, including its disjoint term-row arena. -/
theorem run (v : SelectedLevel B f hf) {w : ℕ}
    (hw : fitConstant B + 4*Nat.clog 2 (v.input.maxWireWidth+1) ≤ w)
    (layout : TermRecordScan.Layout v.origin.motifCount (grid v.origin).d (grid v.origin).e w)
    (mem : Memory w) (hin : TermRecordScan.Inputs (grid v.origin).demandOrder.entries layout
      (batch v.origin v.term).demand mem) :
    let G := grid v.origin
    let V := batch v.origin v.term
    let tape := fun j ↦ TermRecordScan.tape G.block G.supplyOrder.entries (V.demand j) w (V.choice j).val
    ∃ rs : List (Report w),
      TermRecordScan.walk G.block G.demandOrder.entries G.supplyOrder.entries layout
        (TermRecordScan.prepFuel (p := G.p) G.d v.input.maxWireWidth) tape
        (List.finRange v.origin.motifCount) mem = some rs ∧
      (∀ j, TermRecordScan.Fields G.block G.supplyOrder.entries G.pPos (V.demand j)
        (V.choice j).val (layout.base j) (after mem (eventLog rs))) ∧
      (∀ x, (∀ j, layout.Outside j x) → after mem (eventLog rs) x = mem x) ∧
      rs.length = 5*v.origin.motifCount ∧
      branchPaths rs = (List.finRange v.origin.motifCount).flatMap (fun j ↦ [[],[],[],[],tape j]) ∧
      RAMBuckets.cost Report.probes rs ≤ phaseConstant B * v.oldSlots ∧
      (eventLog rs).length ≤ v.oldSlots * (stepConstant B * (w+Nat.clog 2 (v.input.maxWireWidth+1)+1)) := by
  intro G V tape
  obtain ⟨hc,hfit,hstep⟩ := grid_bounds v.origin
  have hcap : G.fitConstant + 4*Nat.clog 2 (v.input.maxWireWidth+1) ≤ w := (Nat.add_le_add_right hfit _).trans hw
  have hrun := (TermRecordScan.run_spec G.block G.demandOrder.entries G.supplyOrder.entries G.pPos G.qPos).choose_spec
    v.origin.motifCount v.input.maxWireWidth w hcap layout V.demand V.bound mem hin
  obtain ⟨rs,hr,fields,frame,hlen,hbits,hprobes,hticks⟩ := hrun.2 V.choice
  refine ⟨rs,hr,fields,frame,by simpa [Nat.mul_comm] using hlen,hbits,?_,?_⟩
  · rw [RAMBuckets.cost_eq_length_add_probes,count_log,hlen]
    calc
      _ ≤ v.origin.motifCount * G.charge := by
        unfold Grid.charge; rw [Nat.mul_add]; exact Nat.add_le_add_left hprobes _
      _ ≤ v.oldSlots * phaseConstant B := Nat.mul_le_mul v.origin.motifCount_le hc
      _ = _ := Nat.mul_comm ..
  · exact hticks.trans (Nat.mul_le_mul v.origin.motifCount_le
      ((G.steps_le _ _).trans (Nat.mul_le_mul_right _ hstep)))

end CompressorRecords.SelectedTerms

end

end VPVNP
end Computability
end OAI
