import OAI.Computability.VPVNP.CompressorExecutionLevels

/-!
# Sizes of the actual arrays scanned at a selected compressor level

Shrinking indexes motifs by old arcs and refresh indexes motifs by port blocks.
The bounds here follow the chosen term through its original state pass. They
control the base, site, arc, motif and resulting slot scans uniformly along
the execution, as well as the largest input field of every intermediate level.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords

open Compression PairSimulation.LocalHistory
open private shrinkMotif_count refreshMotif_count castAllRecordsLe from OAI.Computability.VPVNP.PairSimulationSelectorBounds
open private collectLevels from OAI.Computability.VPVNP.CompressorExecutionLevels

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
variable {R : Type*} [CommRing R] {f : B.Entry → R} {hf : B.IsSolution f}

namespace PassOrigin

variable {a g b n : ℕ} {X : State a g} {p : StatePass R X b n}

/-- Number of physically distinct demand vectors for this pass. -/
def motifCount (o : PassOrigin B f hf p) : ℕ := match o with
  | .shrink _ h X => (shrinkMotifOrder (h ▸ X)).length
  | .refresh (g := g) X => Fintype.card X.Base * 2 ^ g

theorem motifCount_le (o : PassOrigin B f hf p) : o.motifCount ≤ X.positions * 2^a := by
  cases o with
  | shrink i h X => subst h; exact shrinkMotif_count X
  | refresh X => exact (refreshMotif_count X).trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))

theorem next_positions_le (o : PassOrigin B f hf p) (c : p.step.Choice) :
    (p.next c).positions ≤ X.positions := by
  cases o with
  | shrink i h X =>
    exact (Nat.le_mul_of_pos_left _ ((two_lt_packingFactor _).trans' (by decide))).trans_eq
      (B.shrinkPassAt_positions f hf i h X c).symm
  | refresh X =>
    exact (Refresh.dyadicRefreshNext_positions X S.graph (Nat.two_pow_pos _) _ B.refresh _ _ c).le

end PassOrigin

/-- All degree exponents occur in a single fixed finite schedule. -/
def slotDegree (S : BlockSchedule k) : ℕ :=
  max (2 ^ S.portExponent) (Finset.univ.sup (fun i : Fin (S.steps+1) ↦ 2 ^ S.degreeExponent i))

namespace SelectedLevel

variable (v : SelectedLevel B f hf)

/-- Number of input incidence slots, counting each incident port at every input position. -/
def oldSlots : ℕ := v.input.positions * 2^v.inputExponent

/-- Number of positions in the successor state produced by the selected term. -/
def outputSites : ℕ := (v.pass.next v.term).positions

/-- Number of successor incidence slots, obtained by multiplying output positions by output
degree. -/
def outputSlots : ℕ := v.outputSites * 2^v.outputExponent

theorem oldDegree_le : 2^v.inputExponent ≤ slotDegree S := by
  obtain ⟨a,g,b,n,X,p,o,c,sel⟩ := v
  cases o with
  | shrink i _ _ => exact (Finset.le_sup (f := fun j : Fin (S.steps+1) ↦ 2 ^ S.degreeExponent j)
      (Finset.mem_univ i.castSucc)).trans (le_max_right _ _)
  | refresh _ => exact le_max_left _ _

theorem outputDegree_le : 2^v.outputExponent ≤ slotDegree S := by
  obtain ⟨a,g,b,n,X,p,o,c,sel⟩ := v
  cases o with
  | shrink i _ _ => exact (Finset.le_sup (f := fun j : Fin (S.steps+1) ↦ 2 ^ S.degreeExponent j)
      (Finset.mem_univ i.succ)).trans (le_max_right _ _)
  | refresh _ => exact (Finset.le_sup (f := fun j : Fin (S.steps+1) ↦ 2 ^ S.degreeExponent j)
      (Finset.mem_univ 0)).trans (le_max_right _ _)

theorem outputSites_le : v.outputSites ≤ v.input.positions := v.origin.next_positions_le v.term

theorem outputSlots_le : v.outputSlots ≤ v.input.positions * slotDegree S :=
  Nat.mul_le_mul v.outputSites_le v.outputDegree_le

theorem oldSlots_le_units : v.oldSlots ≤ v.units := by
  dsimp [oldSlots,units]; rw [Nat.mul_add]; omega

theorem baseSites_le : Fintype.card v.input.Base ≤ v.input.positions := by
  rw [State.positions,Fintype.card_prod]
  exact Nat.le_mul_of_pos_right _ Fintype.card_pos

end SelectedLevel

variable (B f hf)

private theorem collect_count {a g b n : ℕ} {X : State a g} (E : StateExecution R b n X)
    (W : E.MapWitnesses f) (r : ExecutionReaders E W) (o : PassOrigins B f hf E)
    (rec : E.Records) (z : E.Choices) :
    (collectLevels B f hf E W r o z).length = (E.termChain rec z).length := by
  induction E with
  | done => rfl
  | more p tail ih =>
    rw [StateExecution.length_more]
    exact congrArg Nat.succ (ih z.1 (W.2 z.1) (r.2 z.1) (o.2 z.1) (rec.2 z.1) z.2)

private theorem collect_limits {a g b n C : ℕ} {X : State a g} (E : StateExecution R b n X)
    (W : E.MapWitnesses f) (r : ExecutionReaders E W) (o : PassOrigins B f hf E)
    (rec : E.Records) (z : E.Choices) (width : ℕ) (hb : E.Bounded C rec)
    (hw : X.maxWireWidth ≤ width) (hr : (E.termChain rec z).AllRecordsLe width) :
    ∀ v ∈ collectLevels B f hf E W r o z, v.input.positions ≤ X.positions ∧ v.input.maxWireWidth ≤ width := by
  induction E with
  | done => simp [collectLevels]
  | more p tail ih =>
    obtain ⟨fields,maps,hrest⟩ := hr
    have hnext := o.1.next_positions_le z.1
    have hwidth : (p.next z.1).maxWireWidth ≤ width := by
      refine (hb.1 z.1).2.2.trans (Finset.sup_le fun v _ => max_le ?_ ?_)
      · exact Finset.sup_le fun j _ => fields v j
      · exact Finset.sup_le fun j _ => maps v j
    intro v hv
    rcases List.mem_cons.mp hv with rfl | htail
    · exact ⟨le_rfl,hw⟩
    · obtain ⟨hp,hm⟩ := ih z.1 (W.2 z.1) (r.2 z.1) (o.2 z.1) (rec.2 z.1) z.2
        (hb.2 z.1) hwidth (castAllRecordsLe (p.output_eq z.1).symm _ width hrest) v htail
      exact ⟨hp.trans hnext,hm⟩

/-- The level directory needs one header for each elementary substep on this branch. -/
theorem executeLevels_length {n : ℕ} (T : ℕ) (h : T * S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
    (z : (B.execute f hf T h X).Choices) :
    (executeLevels B f hf T h X z).length ≤ (S.steps+1)*T :=
  (collect_count B f hf _ _ _ _ (B.records f hf T h X) z).le.trans
    ((Procedure.repeat_recordBounds (B.recordBounds f hf) _ T n (Nat.add_sub_of_le h).symm X).2 z)

/-- Every site and field in every intermediate input stays within the branch envelope. -/
theorem executeLevels_limits {n : ℕ} (T : ℕ) (h : T * S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
    (z : (B.execute f hf T h X).Choices) :
    ∀ v ∈ executeLevels B f hf T h X z, v.input.positions ≤ X.positions ∧
      v.input.maxWireWidth ≤ B.growthConstant ^ T * (X.maxWireWidth+1) := by
  have hb := (Procedure.repeat_recordBounds (B.recordBounds f hf) _ T n (Nat.add_sub_of_le h).symm X).1
  have hw := B.growthConstant_ge_two
  exact collect_limits B f hf _ _ _ _ (B.records f hf T h X) z _ hb
    ((Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega))))
    (B.branch_bounds f hf T h X z).2.2.2.2.1

end CompressorRecords

end

end VPVNP
end Computability
end OAI
