import OAI.Computability.BorderVNP.RoutingISAScheduleClock
import OAI.Computability.BorderVNP.CubeTeamOwnedRun
import OAI.Computability.BorderVNP.CubeTeamRowClockStages
import OAI.Computability.BorderVNP.CubeHostScatterTeamClock
import OAI.Computability.BorderVNP.CubeScatterPaddingCost
import OAI.Computability.BorderVNP.DiagonalTallyAlign

/-! # Charging the local cube passes and the packet ID loop

The number of local gadget queries is the vertex count written by the
owned-group traversal. Each strict row emits at most one vertex per trial
scanned by that role. The sum over the executing team's owner fiber bounds
all ID, reference, and five-word increment writes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open BorderVNP.Cube Physical TeamRowClock Finset

private theorem strictVertices_le_trials (n d blocks : ℕ) :
    TeamRows.strictVertices n d blocks ≤ Physical.Owned.packetTrials n d blocks := by
  have bin : d.choose 2 * 2 ≤ d*d := by
    rw [Nat.choose_two_right]
    exact (Nat.div_mul_le_self ..).trans (Nat.mul_le_mul_left _ (Nat.sub_le ..))
  calc
    TeamRows.strictVertices n d blocks = (d.choose 2*2)^n*2*blocks := by
      unfold TeamRows.strictVertices
      rw [mul_pow]
      ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right 2 (Nat.pow_le_pow_left bin n))

private theorem trials_le_scan (n d blocks cb : ℕ) :
    Physical.Owned.packetTrials n d blocks ≤ packetScan n d blocks cb := by
  unfold packetScan
  have h := sum_le_sum (s := (univ : Finset (Fin (Physical.Owned.packetTrials n d blocks))))
    (fun i _ => show 1 ≤ 6*n+22+(if Physical.Owned.packetTrialValid i then cb else 1) by omega)
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at h
  exact h.trans (Nat.le_succ _)

/-- Number of physical triples emitted up to the end of the row scan. Its
local cost bound includes precisely the rows owned by the given team. -/
theorem vertexPrefix_le_roleTicks (dispatch : TeamRowPrepare.Layout) (owner : ℕ → ℕ)
    (n blocks b h K s : ℕ) {d : ℕ} (hd : dispatch.d=d) (axis : Fin (n+1)) :
    TeamRows.vertexPrefix dispatch owner n blocks (dispatch.d*dispatch.d) ≤
      TeamRows.ticks dispatch owner (roleAt
        (physicalRoleTicks blocks b h K s axis : Fin d → Fin d → ℕ)) := by
  subst d
  let role : Fin dispatch.d → Fin dispatch.d → ℕ := physicalRoleTicks blocks b h K s axis
  unfold TeamRows.vertexPrefix TeamRows.ticks
  apply le_trans _ (Nat.le_succ _)
  apply le_trans _ (Nat.le_add_left ..)
  apply sum_le_sum
  intro q hq
  by_cases own : owner (q/dispatch.d)=dispatch.teamID
  · by_cases eq : q/dispatch.d=q%dispatch.d
    · simp [eq]
    · simp only [own,true_and,ite_true,ite_eq_left eq]
      apply le_trans _ (Nat.le_add_left ..)
      let k : Fin (dispatch.d*dispatch.d) := ⟨q,mem_range.mp hq⟩
      have unequal : k.divNat ≠ k.modNat := by
        intro h
        exact eq (congrArg Fin.val h)
      change TeamRows.strictVertices n dispatch.d blocks ≤ roleAt role q
      simp only [roleAt,dite_eq_left (mem_range.mp hq),finProdFinEquiv_symm_apply,role,physicalRoleTicks,checkedRoleTicks]
      apply le_trans _ (Nat.le_add_left ..)
      change TeamRows.strictVertices n dispatch.d blocks ≤ vertexTicks n dispatch.d blocks K h k.divNat k.modNat
      rw [vertexTicks,ite_eq_right unequal]
      exact (strictVertices_le_trials ..).trans (trials_le_scan ..)
  · simp [own]

/-- Charges of the physical reference emitter, selected ID lookup and cube
suffix appender for the number of triples in the actual directory. -/
def packetIDTicks (count width : ℕ) :=
  (DiagonalTallyPacketEmit.setup.slots+DiagonalTallyPacket.setup.slots+4+
    count*(2*(DiagonalTallyPacketEmit.descStep.slots+1)+11)+(count*width)*(DiagonalTallyPacketEmit.refStep.slots+1+8)) +
  (DiagonalTallyCubeSuffix.setup.slots+count*(DiagonalTallyCubeSuffix.step.slots+1)+1+(writeFrame 15 62 63 35).slots)

/-- Numeric packet charges include every traversed binary input address. -/
theorem packetIDTicks_eq (count width : ℕ) : packetIDTicks count width = 109+(43+33*width)*count := by
  change (43+19+4+count*(2*(8+1)+11)+(count*width)*(24+1+8))+
    (38+count*(13+1)+1+4) = _
  ring

/-- Constant for a fixed packet format and argument width, uniform in all
alphabet, ownership, packet, and cable counts. -/
def cubeCoefficient (n b h K s width : ℕ) :=
  (44+33*width)*physicalCoefficient n b h K s+100000000

/-- Costs of owned row roles, padding, host scatter and the actual gadget-ID
and tally suffix loops, including the scalar instructions that align the residue
arena. Only the single scan of the public cable list is outside the team
raw volume and the square product-alphabet term. -/
theorem cubeTicks_le {g : GroupWeights.Layout} {t : TeamNative.Layout} {orig mem : ℕ → ℕ}
    {n blocks b K h : ℕ} {D : LengthDeclaration n g.groups}
    {A : Type*} [Fintype A] {label : Fin g.cells → Label (n+1) g.groups}
    {recv : A → Fin g.cells} {incoming : A → ℕ}
    (result : GroupWeights.ScheduleResult g t orig mem)
    (image : GroupWeights.PhysicalImage g orig blocks b K h D label recv incoming)
    (team : Fin (t.r+1)) (dispatch : TeamRowPrepare.Layout) (hd : dispatch.d=g.groups)
    (ht : dispatch.teamID=team.val) (X s width : ℕ) (positive : 0 < h*b) (alphabet : 0 < g.groups)
    (pass : (TeamBudget.Layout.mk (t.r+1) X t.totals).Passes mem)
    (pad : Padding.Layout) (padMem used : ℕ → ℕ)
    (tail : Padding.TailHeader D.1 (fun u : Fin g.groups => mem (t.owners+u.val))
      (Function.Embedding.refl ℕ) team.val pad padMem used blocks b h K s)
    (host : HostScatter.Layout) (hostMem : ℕ → ℕ) (hostTeam : host.team=team.val)
    (hostRows : host.ScheduledCables hostMem (blocks*(h*b)) D.1 (fun u : Fin g.groups => mem (t.owners+u.val))) :
    let owner (u : ℕ) := mem (t.owners+u)
    let count := TeamRows.vertexPrefix dispatch owner n blocks (dispatch.d*dispatch.d)
    let visits := TeamRows.ticks dispatch owner (roleAt (physicalRoleTicks blocks b h K s D.1 :
      Fin g.groups → Fin g.groups → ℕ))
    4+(visits+11)+pad.budget padMem+
      (HostScatter.setup.slots+HostScatter.traversalTicks host hostMem)+packetIDTicks count width+DiagonalTallyRAM.alignTallies.slots ≤
      82*host.count+cubeCoefficient n b h K s width*((g.groups^(n+1))^2+X+1) := by
  intro owner count visits
  let Z := (g.groups^(n+1))^2
  let C := physicalCoefficient n b h K s
  have rows : visits ≤ C*(Z+X) := checkedTeamTicks_le_sq result image team dispatch hd ht X s positive alphabet pass
  have vc : count ≤ visits := by
    exact vertexPrefix_le_roleTicks dispatch owner n blocks b h K s hd D.1
  have cap := (TeamBudget.Layout.le_teamLimit ⟨t.r+1,X,t.totals⟩ _).mp (pass.1 team.val team.isLt)
  have endpoints := host.incident_le_teamLimit hostMem result image team hostTeam hostRows X cap
  have raw := (ownedRaw_le_stored result image team).trans (pass.1 team.val team.isLt)
  have padBits := tail.assigned_le_raw
  have pt : pad.team = team.val := tail.site
  have bt : ∑ k ∈ range pad.count,(pad.assigned padMem k false+pad.assigned padMem k true) ≤
      2*(1000000*X/256) := by
    apply padBits.trans
    simpa only [Function.Embedding.refl_apply,pt,ownedRaw,TeamBudget.Layout.teamLimit,Nat.mul_comm X 1000000] using Nat.mul_le_mul_left 2 raw
  have pcount : pad.count = Z := by
    simp only [Padding.Layout.count,tail.alphabet.1,Z,pow_two]
  have fit : 1000000*X/256 ≤ 1000000*X := Nat.div_le_self ..
  have hpad : pad.budget padMem ≤ 66+130*Z+46000000*X := by
    change 64+2+pad.count*(2*64+2)+23*(∑ k ∈ range pad.count, _) ≤ _
    rw [← pcount]
    omega
  have hhost : HostScatter.setup.slots+HostScatter.traversalTicks host hostMem ≤
      68+82*host.count+44000000*X := by rw [HostScatter.program_ticks]; omega
  have vv := Nat.mul_le_mul_left (43+33*width) (vc.trans rows)
  rw [packetIDTicks_eq]
  have align : DiagonalTallyRAM.alignTallies.slots ≤ 32 := by decide
  change _ ≤ 82*host.count+((44+33*width)*C+100000000)*(Z+X+1)
  calc
    _ ≤ 4+(C*(Z+X)+11)+(66+130*Z+46000000*X)+(68+82*host.count+44000000*X)+
        (109+(43+33*width)*(C*(Z+X)))+32 := by gcongr
    _ ≤ _ := by ring_nf; omega

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
