import OAI.Computability.BorderVNP.RoutingISACellBankProof
import OAI.Computability.BorderVNP.CubeGroupWeightPhysicalSchedule

/-! # The two-word receiving-cell directory realizes the physical team assignment -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellBanks

open VPVNP.BurstRAM BorderVNP.Cube
open BorderVNP.Cube.GroupWeights

variable {l : Layout} {g : GroupWeights.Layout} {teams : TeamNative.Layout}
variable {old after : ℕ → ℕ} {n blocks b K h : ℕ} {D : Physical.LengthDeclaration n g.groups}
variable {label : Fin g.cells → Cube.Label (n+1) g.groups}
variable {A : Type*} [Fintype A] {recv : A → Fin g.cells} {width : A → ℕ}

/-- The bank installer consumes the actual label and owner arrays. The
three output banks of the preceding team schedule lie after the label array. -/
structure ScheduleLayout (l : Layout) (g : GroupWeights.Layout) (teams : TeamNative.Layout) : Prop where
  /-- Both passes enumerate exactly the same cells. -/
  cells : l.cells=g.cells
  /-- Both use the same coordinate alphabet. -/
  groups : l.groups=g.groups
  /-- The label word addresses agree. -/
  labels : l.labels=g.labels
  /-- The chosen positional factor agrees. -/
  place : l.place=g.place
  /-- The group-owner address is the schedule's actual output. -/
  owners : l.owners=teams.owners
  /-- All computed group weights follow the immutable labels. -/
  weightSep : g.labels+g.cells ≤ g.weights
  /-- The team totals follow the immutable labels. -/
  totalSep : g.labels+g.cells ≤ teams.totals
  /-- The emitted owners follow the immutable labels. -/
  ownerSep : g.labels+g.cells ≤ teams.owners

/-- The owner lookup in the new directory is the greedy owner of the actual
chosen digit of this cell's geometric label. -/
theorem ScheduleLayout.cell_owner (layout : ScheduleLayout l g teams)
    (res : ScheduleResult g teams old after) (image : PhysicalImage g old blocks b K h D label recv width)
    (c : Fin g.cells) :
    l.owner after c.val = (TeamNative.owner teams.r (g.weight old) (label c D.1).val).val := by
  have preserve : after (g.labels+c.val) = old (g.labels+c.val) := by
    apply res.other
    · intro t _; have := layout.weightSep; have := c.isLt; omega
    · intro t; have := layout.totalSep; have := c.isLt; omega
    · intro t _; have := layout.ownerSep; have := c.isLt; omega
  have digit : l.group after c.val = (label c D.1).val := by
    rw [Layout.group,layout.labels,layout.groups,layout.place,preserve]
    exact image.symbol_eq c
  rw [Layout.owner,layout.owners,digit]
  exact res.owners _ (label c D.1).isLt

/-- In rational units this is the first least-loaded team after all symbols
preceding the cell's chosen symbol have been assigned. -/
theorem ScheduleLayout.rational_owner (layout : ScheduleLayout l g teams)
    (res : ScheduleResult g teams old after) (image : PhysicalImage g old blocks b K h D label recv width)
    (c : Fin g.cells) :
    let t := label c D.1
    let prior := (List.finRange t.val).map (fun j ↦ jointCost blocks b K h D label recv width
      ⟨j.val, j.isLt.trans t.isLt⟩)
    l.owner after c.val = (firstMinimum (assignGroups prior (fun _ : Fin (teams.r+1) ↦ 0))).val := by
  intro t prior
  have he : ((List.range t.val).map (fun j ↦ TeamNative.unscale (g.weight old j))) = prior := by
    apply List.ext_getElem (by simp [prior])
    intro j hj hj'
    have hjt : j<t.val := by simpa using hj
    have h : TeamNative.unscale (g.weight old j) = jointCost blocks b K h D label recv width
        ⟨j,hjt.trans t.isLt⟩ := by
      rw [← res.weights j (hjt.trans t.isLt)]
      exact res.weight_physical image ⟨j,hjt.trans t.isLt⟩
    simpa only [prior,List.getElem_map,List.getElem_range,List.getElem_finRange,Fin.val_cast] using h
  rw [layout.cell_owner res image c, TeamNative.owner,← he,← TeamNative.loads_unscale,
    TeamNative.firstMinimum_unscale]

/-- The actual register-machine loop publishes the correct first-minimum
owner and the true absolute input-bank address for every cell. -/
theorem install_physical {W : ℕ} (pub : Arg → Word W) (mac : TeamOpcode.Macros W 8)
    (s : Bank W) (m : Memory W) (frame : readings pub 0 = l.frame)
    (fields : l.Fields (readings m)) (fit : l.Fits W) (layout : ScheduleLayout l g teams)
    (res : ScheduleResult g teams old (readings m)) (image : PhysicalImage g old blocks b K h D label recv width) :
    BoundedRun pub mac install s m (setup.slots+l.cells*15+1) (fun z ↦
      z.mem=l.written (readings m) l.cells ∧ ∀ c : Fin g.cells,
        z.mem (l.dest+2*c.val)=(TeamNative.owner teams.r (g.weight old) (label c D.1).val).val ∧
        z.mem (l.dest+2*c.val+1)=l.bank c.val) := by
  apply (install_run pub mac l s m frame fields fit).mono le_rfl
  intro z hz
  refine ⟨hz,?_⟩
  intro c
  rw [hz]
  have r := l.written_at (readings m) (i:=l.cells) (c:=c.val) (by rw [layout.cells]; exact c.isLt)
  exact ⟨r.1.trans (layout.cell_owner res image c),r.2⟩

end RoutingISA.CellBanks

end BorderVNP
end Computability
end OAI
