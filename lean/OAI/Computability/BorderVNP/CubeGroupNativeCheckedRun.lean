import OAI.Computability.BorderVNP.CubeGroupNativeEventually

/-! # Clocked accepting execution of the native group allocation and capacity check -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.GroupWeights

open Physical RoutingISA TeamScales Filter VPVNP.BurstRAM

/-- The word and frame premises of the actual three passes: histogram, greedy
assignment, and the guard over the resulting team totals. -/
structure CheckedFrame (l : Layout) (t : TeamNative.Layout) (orig : ℕ → ℕ) (wordWidth X : ℕ) : Prop where
  /-- The histogram reads its real frame and does representable arithmetic. -/
  fields : l.Fields orig
  setup : l.SetupRoom wordWidth
  fits : l.Fits wordWidth orig
  /-- Allocation and frame read by the greedy traversal. -/
  allocated : t.Allocated wordWidth
  frameFit : l.frame+77 < 2^wordWidth
  frame : t.Frame l.frame orig
  groups : t.groups = l.groups
  weights : t.weights = l.weights
  keepAssign : ∀ f ∈ ([1,74,75,76,77] : List ℕ), ∀ i < l.groups, l.frame+f ≠ l.weights+i
  /-- Native budget fields and limit calculations fit before scanning the totals. -/
  budgetFields : (⟨t.r+1,X,t.totals⟩ : TeamBudget.Layout).Fields l.frame orig
  budgetFits : (⟨t.r+1,X,t.totals⟩ : TeamBudget.Layout).Fits l.frame wordWidth
  keepBudget : ∀ f ∈ ([1,31,76] : List ℕ),
    (∀ i < l.groups, l.frame+f ≠ l.weights+i) ∧
    (∀ j : Fin (t.r+1), l.frame+f ≠ t.totals+j.val) ∧
    (∀ i < l.groups, l.frame+f ≠ t.owners+i)

/-- The rational total bound implies word-safety of the aggregate histogram.
The guard's own scalar product must be representable before its division. -/
theorem histogram_sum_fits {l : Layout} {t : TeamNative.Layout} {orig : ℕ → ℕ} {wordWidth X : ℕ}
    {n blocks b K h : ℕ} {D : LengthDeclaration n l.groups} {A : Type*} [Fintype A]
    {label : Fin l.cells → Label (n+1) l.groups} {recv : A → Fin l.cells} {w : A → ℕ}
    (image : PhysicalImage l orig blocks b K h D label recv w)
    (total : (∑ s, jointCost blocks b K h D label recv w s) ≤ ((X*(t.r+1) : ℕ) : ℚ)/1024)
    (fit : (⟨t.r+1,X,t.totals⟩ : TeamBudget.Layout).Fits l.frame wordWidth) :
    ∑ i ∈ Finset.range l.groups, l.weight orig i < 2^wordWidth := by
  let cap : TeamBudget.Layout := ⟨t.r+1,X,t.totals⟩
  let mass := ∑ i ∈ Finset.range l.groups, l.weight orig i
  have eq : TeamNative.unscale mass = ∑ s, jointCost blocks b K h D label recv w s := by
    simp only [mass,← Fin.sum_univ_eq_sum_range,TeamNative.unscale,Nat.cast_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro s _
    change TeamNative.unscale (l.weight orig s.val) = _
    rw [image.weight_eq,TeamNative.unscale_scaledWeight]
    rfl
  have bounded : mass ≤ cap.totalLimit := (cap.le_totalLimit mass).mpr (by
    rw [eq]
    simpa only [cap,Nat.cast_mul] using total)
  exact bounded.trans_lt ((Nat.div_le_self ..).trans_lt fit.allScaled)

/-- End-to-end positive execution, with all writes and the cost of the final
memory-preserving test. -/
theorem checked_run_of_capacity {wordWidth : ℕ} (pub : Arg → Word wordWidth)
    (mac : TeamOpcode.Macros wordWidth 8) (regs : Bank wordWidth) (m : Memory wordWidth)
    (l : Layout) (t : TeamNative.Layout) (X : ℕ) (base : readings pub 0 = l.frame)
    (setup : CheckedFrame l t (readings m) wordWidth X)
    (sumFits : ∑ i ∈ Finset.range l.groups, l.weight (readings m) i < 2^wordWidth)
    (capacity : ∀ next, ScheduleResult l t (readings m) next →
      (⟨t.r+1,X,t.totals⟩ : TeamBudget.Layout).Passes next) :
    BoundedRun pub mac checkedSchedule regs m
      (ticks l+TeamNative.assignmentTicks t + (TeamBudget.setup.slots+(t.r+1)*(TeamBudget.row.slots+1)+1))
      (fun z => ScheduleResult l t (readings m) z.mem) := by
  let budget : TeamBudget.Layout := ⟨t.r+1,X,t.totals⟩
  have first := run_schedule pub mac l t regs m base setup.fields setup.setup setup.fits setup.allocated
    setup.frameFit setup.frame setup.groups setup.weights setup.keepAssign sumFits
  have test := checked_test pub mac l t regs m X first budget rfl
    (base ▸ setup.budgetFields) (base ▸ setup.budgetFits) (base ▸ setup.keepBudget)
  obtain ⟨_,_,mt,_,_,result⟩ := first
  exact test.complete ((result.passes_iff X).mp (capacity (readings mt) result))

universe u v

/-- Fix a genuine cube format. On each passing declaration at every sufficiently
large processor length, the actual public group schedule executes and accepts.
The threshold precedes the choice of team size, delivery type, layout and state. -/
theorem PacketFormat.eventually_checked_run {F : Type u} [Field F] {n : ℕ} {η α ξ : ℝ}
    (p : PacketFormat F n η) (hη : 0 < η) (fixed : 100*(2/Real.sqrt (n+1)+η) < 1/10^6)
    (hα : 0 < α) (hξ : ξ < α/3) (hgap : 8*α*(n+1) < 1-ξ) :
    ∀ᶠ k : ℕ in atTop, ∀ (r wordWidth : ℕ) (l : Layout) (t : TeamNative.Layout) (blocks : ℕ)
      (pub : Arg → Word wordWidth) (mac : TeamOpcode.Macros wordWidth 8) (regs : Bank wordWidth) (m : Memory wordWidth)
      (A : Type v) [Fintype A] (D : LengthDeclaration n l.groups) (select : Packet n l.groups blocks → Selector n p.K p.h)
      (label : Fin l.cells → Label (n+1) l.groups) (recv : A → Fin l.cells) (w : A → ℕ),
      1 ≤ r → (t.r+1 : ℝ) ≤ (k : ℝ)^(2*α) → l.groups = alphabet α k →
      blocks = blocksFor (exterior ξ r k*(t.r+1) : ℕ) (p.h*p.b) (l.groups^(n+1)) →
      readings pub 0 = l.frame → CheckedFrame l t (readings m) wordWidth (exterior ξ r k) →
      PhysicalImage l (readings m) blocks p.b p.K p.h D label recv w → passesLengths p.b p.s select D →
      (∀ u, Balancing.load (Balancing.datum (fun j : Balancing.Bits w => recv j.1) u) label ≤
        4*((exterior ξ r k*(t.r+1) : ℕ) : ℝ)/((l.groups^(n+1) : ℕ) : ℝ)) →
      (∑ a, w a) ≤ 3*(t.r+1)*r*literal α k →
      BoundedRun pub mac checkedSchedule regs m
        (ticks l+TeamNative.assignmentTicks t + (TeamBudget.setup.slots+(t.r+1)*(TeamBudget.row.slots+1)+1))
        (fun z => ScheduleResult l t (readings m) z.mem) := by
  have gap : 8*α*((n+1 : ℕ) : ℝ) < 1-ξ := by simpa only [Nat.cast_add,Nat.cast_one] using hgap
  filter_upwards [p.eventually_budget_passes hη fixed hα hξ hgap,
    eventually_group_charge_room hα hξ (n+1) (p.h*p.b) p.expansion p.blockPositive gap] with k cap room
  intro r wordWidth l t blocks pub mac regs m A _ D select label recv w hr hR groups blockCount base frame
    image pass balanced volume
  obtain ⟨small,_,pad,data⟩ := room r (t.r+1) hr (by omega) (by exact_mod_cast hR)
  rw [← groups] at small pad
  rw [← blockCount] at pad
  have total := sum_jointCost_le_volume (label := label) (recv := recv) p.s select pass
    (exterior ξ r k*(t.r+1)) frame.fits.positive η hη.le fixed p.width p.selector
    (by simpa only [Nat.cast_add,Nat.cast_one] using small) pad (data _ volume)
  apply checked_run_of_capacity pub mac regs m l t (exterior ξ r k) base frame
    (histogram_sum_fits image total frame.budgetFits)
  exact fun next result => cap r l t blocks (readings m) next A D select label recv w hr hR groups blockCount
    result image pass balanced volume

end Cube.GroupWeights

end BorderVNP
end Computability
end OAI
