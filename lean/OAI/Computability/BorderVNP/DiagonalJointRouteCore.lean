import OAI.Computability.BorderVNP.DiagonalJointProfileRouteClock
import OAI.Computability.BorderVNP.RoutingISAScheduleClockFiniteIncidence
import OAI.Computability.BorderVNP.CubeScatterTransmissionRealization

/-! # Actual core charge from the endpoint counts of the physically written route table -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM TeamScales Transmission TeamContraction ProcessorSlots Filter Finset
open scoped BigOperators

/-- On a real native scheduler image, charge the actual active role (including a
co-located row) using the two physical endpoints read at that row. The source bound
uses the sent original bits and the per-team receiving and shared reservation. -/
theorem eventually_core_of_scheduled_endpoints {α ξ : ℝ} (gap : ξ < α/3) :
    ∀ᶠ n : ℕ in atTop, ∀ {w : ℕ} (base count : ℕ) (f : BroadcastFrame) (l : TableLayout) (row : ℕ → TableRow)
      (orig : ℕ → ℕ) (m : Memory w) (self : Word w) (u : Fin l.teams),
      l.Image row orig (readings m) → l.Allocated w → l.recordsMatch row orig →
      (∀ i < l.count, (row i).first<l.teams ∧ (row i).second<l.teams) →
      self.val=u.val → f.Fits w base → f.teams=l.teams → f.link=TeamScales.link ξ f.teams n →
      f.literal ≤ literal α n → w≤count → count≤f.processors →
      (∀ v : Fin l.teams, (∑ i ∈ range l.count, endpointWidth (row i) v.val) ≤
        3*f.processors*literal α n+exterior ξ f.processors n/256) →
      coreTicks count f l row (tableRange l m) self ≤ 2048*(exterior ξ f.processors n+(l.teams+1)^3+l.count+f.processors+1) := by
  filter_upwards [TeamScales.eventually_literals_le gap 768] with n small
  intro w base count f l row orig m self u image al initial labels same fit teams link lit wc cr ends
  let X := exterior ξ f.processors n
  let actual := tableRange l m
  have send : 768*f.processors*literal α n ≤ X := by simpa only [Nat.mul_assoc] using small f.processors
  have traffic (v : Fin l.teams) : ∑ j, Routing.demand (l.widthMatrix row) v j ≤ X/64 := by
    rw [l.demand_sum_eq row labels]
    have cut : (∑ i ∈ range l.count, (row i).exteriorWidth v.val) ≤ ∑ i ∈ range l.count, endpointWidth (row i) v.val := by
      apply sum_le_sum
      intro i _
      unfold TableRow.exteriorWidth endpointWidth
      split_ifs <;> omega
    have cap := ends v
    change _ ≤ 3*f.processors*literal α n+X/256 at cap
    rw [show 768*f.processors*literal α n = 256*(3*f.processors*literal α n) by ring] at send
    omega
  have cost : (∑ i ∈ range l.count, (actual i).teamCost self) ≤ 107*∑ i ∈ range l.count, endpointWidth (row i) u.val := by
    rw [Finset.mul_sum]
    apply sum_le_sum
    intro i hi
    obtain ⟨_,first,second,wd,_⟩ := tableRange_fields image al initial (mem_range.mp hi)
    have charge := (actual i).teamCost_le_roleBits self
    simpa only [actual,←Fin.val_inj,same,first,second,wd,endpointWidth,eq_comm] using charge
  have router := routingCheckTicks_le f l row fit teams ξ n link traffic
  have recv := ends u
  change _ ≤ 3*f.processors*literal α n+X/256 at recv
  have initialWork : 17*(f.processors*f.literal) ≤ 17*(f.processors*literal α n) :=
    Nat.mul_le_mul_left 17 (Nat.mul_le_mul_left _ lit)
  have sumCap : 256*(3*f.processors*literal α n) ≤ X := by
    rw [←show 768*f.processors*literal α n = 256*(3*f.processors*literal α n) by ring]
    exact send
  rw [Nat.mul_assoc] at send sumCap recv
  change routingCheckTicks f l row ≤ 768*(X+(l.teams+1)^3+l.count+1) at router
  unfold coreTicks jointBudget
  change 126+(41+count*10+1)+(19+8*81*(w+1)+8)+2+(44+17*(f.processors*f.literal)+1)+
    routingCheckTicks f l row+(19+24*l.count+(∑ i ∈ range l.count, (actual i).teamCost self)+1) ≤
      2048*(X+(l.teams+1)^3+l.count+f.processors+1)
  omega

end RoutingISA.Evaluator.ScheduleClock

namespace Cube.RouteRecords

open VPVNP.BurstRAM Physical RoutingISA RoutingISA.Evaluator.ScheduleClock TeamScales Finset

variable {l : GroupWeights.Layout} {teams : TeamNative.Layout} {orig : ℕ → ℕ}
    {a blocks b K h : ℕ} {decl : LengthDeclaration a l.groups}
    {A : Type*} [Fintype A] {label : Fin l.cells → Label (a+1) l.groups} {recv : A → Fin l.cells} {width : A → ℕ}

/-- A true returning team-budget guard bounds the data and shared work of the native
route on every participating team, including rows whose endpoints coincide. -/
theorem clock_endpoints_of_budget {n w : ℕ} {α ξ : ℝ}
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (bank : Bank w) (m : Memory w)
    (sched : GroupWeights.ScheduleResult l teams orig (readings m))
    (image : GroupWeights.PhysicalImage l orig blocks b K h decl label recv width)
    (dir : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ) (order : Fin (dir.directory pp lp).length ≃ A)
    (sizes : ∀ j : Fin (dir.directory pp lp).length, (dir.directory pp lp)[j.val].width=width (order j))
    (owner : ℕ → Fin (teams.r+1)) (group : Fin l.groups → Fin (teams.r+1))
    (cells : ∀ j : Fin (dir.directory pp lp).length, owner (dir.directory pp lp)[j.val].cell=group (label (recv (order j)) decl.1))
    (owners : ∀ x : Fin l.groups, readings m (teams.owners+x.val)=(group x).val)
    (procs : 0<dir.processors) (fields : 0<dir.fields) (two : dir.fields≤2) (block : 0<dir.block)
    (lit : dir.literal ≤ literal α n) :
    let X := exterior ξ dir.processors n
    let budget : TeamBudget.Layout := ⟨teams.r+1,X,teams.totals⟩
    budget.Fields (readings pub 0) (readings m) → budget.Fits (readings pub 0) w →
    ∀ {es z mt}, Runs pub mac TeamBudget.check bank m es z mt →
    ∀ u : Fin (teams.r+1),
      (∑ i ∈ range ((dir.directory pp lp).length+l.groups.choose 2),
        endpointWidth (combinedRow (dir.directory pp lp) owner blocks K h decl group i) u.val) ≤
        3*dir.processors*literal α n+X/256 := by
  intro X budget loaded fit es z mt run u
  have cap := HostScatter.teamCap_of_budget_run pub mac budget bank m loaded fit run u
  have bounds := scheduled_endpointWidths sched image dir pp lp order sizes owner group cells owners procs fields block X u cap
  have out : (dir.fields+1)*(dir.processors*dir.literal) ≤ 3*dir.processors*literal α n := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ lit)
  exact bounds.trans (Nat.add_le_add_right out _)

end Cube.RouteRecords

namespace TeamContraction

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.Evaluator.ScheduleClock RoutingISA.Transmission
open Routing TeamScales Filter Finset ProcessorSlots

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
    {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
    {tab : TableLayout} {row : ℕ → TableRow} {pub : Fin (R+1) → Arg → Word w} {before : Fin (R+1) → Memory w}
    {dst ib hb sb : Fin (R+1) → ℕ} {guess : Fin (R+1) → ℕ → Bool}

/-- On the actual jointly prepared exterior, the scheduler's returned RAM has the
literal team at frame zero. This supplies the time bound on the same image used to
realize the native routing trace. -/
theorem SharedRoutePrepared.eventually_core {α ξ : ℝ} (gap : ξ < α/3) :
    ∀ᶠ length : ℕ in atTop, ∀ (_ready : SharedRoutePrepared G pin ext L D pp lp owner origin stride tab row pub before
      dst ib hb sb guess) (u : Fin (R+1)) (count : ℕ) (mt : Memory w),
      tab.Image row (readings (before u)) (readings mt) → link=TeamScales.link ξ (R+1) length →
      G.program.length+t ≤ literal α length → w≤count → count≤r →
      (∀ v : Fin (R+1), (∑ i ∈ range tab.count, endpointWidth (row i) v.val) ≤
        3*r*literal α length+exterior ξ r length/256) →
      coreTicks count (G.transferFrame u L.header (dst u)) tab row (tableRange tab mt) (directoryFrame (pub u) mt 0) ≤
        2048*(exterior ξ r length+(R+1+1)^3+tab.count+r+1) := by
  filter_upwards [eventually_core_of_scheduled_endpoints gap] with length fit
  intro ready u count mt image linkEq lit wc cr load
  let frame := G.transferFrame u L.header (dst u)
  let team : Fin tab.teams := Fin.cast ready.teams u
  have state := image.broadcast_of_ordered ready.ordered (ready.base u) (ready.frame u)
  have teamNum : (directoryFrame (pub u) mt 0).val=team.val := by
    simpa [directoryFrame,frameField,team,readings,Wiring.transferFrame] using state.1
  have bounds := fit (pub u 0).val count frame tab row (readings (before u)) mt (directoryFrame (pub u) mt 0) team
    image ready.allocated (ready.records u) (fun i hi => (ready.rowFit.labels i hi).2) teamNum
    (ready.fit u) ready.teams linkEq lit wc cr (fun v => load (Fin.cast ready.teams.symm v))
  simpa only [frame,Wiring.transferFrame,←ready.teams] using bounds

end TeamContraction

end BorderVNP
end Computability
end OAI
