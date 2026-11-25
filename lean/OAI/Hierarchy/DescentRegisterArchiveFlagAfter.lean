import OAI.Hierarchy.DescentArchiveRegisterFlag
import OAI.Hierarchy.DescentReachedCensusCount

namespace OAI
/-! # The stored paid count at each noninitial archive checkpoint -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentColonies DescentCompiler DescentKernelHistory DescentLocalArchiveOrder DescentSIMDLookup
open DescentPacking.PackedMatch.Local.Stage
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P→ℕ} {d k wire hist i z D H w : ℕ} {q ε : ℝ} {W : MarkedWorld F d P bits}
    (r : Reached W G q ε S k i z D wire hist)
local notation "A" => r.placement

omit [Fintype P] in
theorem archive_mass (v : Fin (S.groupCount i)×r.V) (x : Block k) :
    PackedCensus.histories W (A).pos (A).block (A).records v x≤(A).wire*((A).z*G.b)*(A).cap:=by
  apply le_trans _ ((A).small v x)
  unfold PackedCensus.histories StarKeys.blockMass
  apply Finset.sum_le_sum
  intro u _
  by_cases here:(A).pos u=v ∧ (A).block u=x
  · simp only [here]
    exact (Nat.le_mul_of_pos_left ((A).records u).length r.valid.atom).trans (Nat.le_add_left _ _)
  · simp only [here,ite_false,le_refl]

omit [Fintype P] in
theorem archiveFlag_after (positive : 0< i) (B : BitDescription W) (rank : Local B) (ports : DatePorts)
    (room : DatePorts.RangeRoom ports r B) (wide : Fintype.card r.V≤H) (precision : ℕ)
    (fit : (A).wire*((A).z*G.b)*(A).cap<2^precision) (x : Fin (2^ports.venue.k)) (n : Fin ports.nodes)
    (h : Fin ports.operandHosts) (g : Fin ports.venue.groups) (row : Fin H) (same : row.val=h.val) :
    archiveFlag r B rank ports room x n h g =
      if n.val<(Census.count A (Equiv.refl _) (r.vertex.trans (Fin.castLEEmb wide)) precision row
        (g.cast room.groups.symm) (x.cast (congrArg (2^·) room.radix.symm))).val then 1 else 0:=by
  classical
  let host:=r.vertex.trans (Fin.castLEEmb wide)
  have atRow (u:r.V) : host u=row ↔ (r.vertex u).val=h.val:=by
    rw [Fin.ext_iff]
    change (r.vertex u).val=row.val ↔ _
    rw [same]
  unfold archiveFlag
  rw [ite_eq_right (Nat.ne_of_gt positive)]
  change _ = if n.val<(Census.count A (Equiv.refl _) host precision row _ _).val then 1 else 0
  by_cases actor:∃u:r.V,(r.vertex u).val=h.val
  · have live:∃u,host u=row:=⟨actor.choose,(atRow _).mpr actor.choose_spec⟩
    have iden:live.choose=actor.choose:=by
      apply r.vertex.injective
      apply Fin.ext
      exact ((atRow _).mp live.choose_spec).trans actor.choose_spec.symm
    simp only [dite_eq_left actor,Census.count,dite_eq_left live,Equiv.refl_symm,Equiv.refl_apply,iden]
    rw [Fin.val_cast_of_lt ((archive_mass r _ _).trans_lt fit)]
  · have empty:¬∃u,host u=row:=fun h'=>actor ⟨h'.choose,(atRow _).mp h'.choose_spec⟩
    simp [actor,Census.count,empty]

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
