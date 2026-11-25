import OAI.Hierarchy.TaggedWideWindowProgramLayout
import OAI.Hierarchy.TaggedWideWindowCounting
import OAI.Hierarchy.ProtocolRAMFrozenWindowCost

namespace OAI
/-! # Mutable volume and clock of the actual shorter-call windows -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard HistoryRoles ReportSockets Tagged TaggedShorterBudget
open ProtocolRAMFrozenWindow ProtocolRAMPackedRanked Real Tagged.WindowCounting
open ThreeFlat Routing CallPool
open scoped Classical BigOperators

private theorem frozen_window_bound (f : ProtocolRAMFrozenWindow.Format) (budget : ℕ) (one : 1≤ budget)
    (rows : f.N≤ budget) (bins : f.window.bins≤ budget)
    (cells : f.window.C*f.D≤ budget) (Dpos : 0<f.D)
    (widths : f.groups*f.D≤ budget) (records : f.N*f.cap≤ budget) :
    f.window.stop 0≤ 22000*budget ∧ ∀ (r : ℕ) (a : ProtocolRAMFrozenWindow.Inputs),a.owner.work=17→f.clock r a≤ 22000*budget := by
  have copies : f.window.C≤ budget:= (Nat.le_mul_of_pos_right _ Dpos).trans cells
  have space:=f.window.stop_le 0
  change _≤ 0+36*f.N+f.window.bins+f.window.C+4*(f.window.C*f.D)+2*(f.groups*f.D)+20*(f.N*f.cap)+19 at space
  refine ⟨by omega,?_⟩
  intro r a owner
  have mask : f.window.maskWords=f.window.C+4*(f.window.C*f.D):=by unfold Size.maskWords; change _=f.window.C+4*(f.window.C*f.window.D);ring
  have width : f.window.widthWords=2*(f.groups*f.D):=by change 2*f.groups*f.D=2*(f.groups*f.D);ring
  rw [ProtocolRAMFrozenWindow.Format.clock_eq,owner,mask,width]
  omega

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    {κ A s : ℝ} (m ell short : ℕ) {u : ℝ→ℝ} (hu : TaggedWidthProfile.Admissible s u) (δ ξ : ℝ)

private theorem parent_fraction_bound (lo hi : ℝ) (i : ℕ × ℕ)
    (profile : TaggedWidthProfile.Admissible s u) :
    ∃ U : ℝ, 0 < U ∧ ∀ a ∈ Set.Icc lo hi, typeFraction u δ ξ a i ≤ U := by
  have der := profile.smooth.continuous_deriv (by simp)
  have e : Continuous (fun a => u a + a * (-deriv u a) - δ) :=
    (profile.smooth.continuous.add (continuous_id.mul der.neg)).sub continuous_const
  have f : Continuous (fun a => 1 - (-deriv u a) - δ) :=
    (continuous_const.sub der.neg).sub continuous_const
  have he := (continuous_const_rpow (dyadic_pos i.1).ne').comp e
  have hf := (continuous_const_rpow (dyadic_pos i.2).ne').comp f
  have cont : Continuous (fun a => typeFraction u δ ξ a i) :=
    continuous_const.div (he.mul hf) (fun a => mul_ne_zero (rpow_pos_of_pos (dyadic_pos _) _).ne'
      (rpow_pos_of_pos (dyadic_pos _) _).ne')
  obtain ⟨K,bound⟩ := (isCompact_Icc (a:=lo) (b:=hi)).bddAbove_image cont.continuousOn
  exact ⟨max 1 K,zero_lt_one.trans_le (le_max_left _ _),fun a ha =>
    (bound (Set.mem_image_of_mem _ ha)).trans (le_max_right _ _)⟩

include hu in
/-- One coefficient pays every original width-class state, including the padded group
batches and all rounded idle module rows. It is independent of the parent and both bases. -/
theorem wideWindowVolume (cap : ℕ) :
    ∃ K : ℕ,∀ (x : WideParent κ A) (rom : ℕ) (i : Fin (m+1)),
    let f:=v.wideWindow x m ell short u δ ξ cap rom i
    f.window.stop 0≤ K*2^x.h ∧ ∀ (r : ℕ) (a : ProtocolRAMFrozenWindow.Inputs),a.owner.work=17→f.clock r a≤ K*2^x.h := by
  choose up upPos fits using fun i : Fin (m+1)=>parent_fraction_bound δ ξ (1+κ) A (v.W,i.val) hu
  let U:=⌈∑i,up i⌉₊
  let L:=2^(short+ell)
  let space:=v.widePackedFactor*2^ell
  let cells:=(6*U+space)*L+2*L*space
  let binCost:=2*space*(m+1)
  let charge:=1+v.rowFactor+binCost+cells+space+v.rowFactor*cap
  refine ⟨22000*charge,?_⟩
  intro x rom i f
  let n:=2^x.h
  let key:=typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)
  let g:=key.supergroup (key.index i) x
  let c:=typeFraction u δ ξ (logb x.h x.w) (v.W,i.val)
  have cu : c≤ U:=by
    apply (fits i (logb x.h x.w) x.formats.2.2).trans
    exact (Finset.single_le_sum (fun j _=>(upPos j).le) (Finset.mem_univ i)).trans (Nat.le_ceil _)
  have address : f.D=2^g:=(type_address v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell) x i).symm
  have height : f.n=g-(short+ell):=rfl
  have Dpos : 0<f.D:=by rw [address];exact Nat.two_pow_pos _
  have pool : (f.groups+1)*f.D≤ space*n:=by
    have atSlots:=Nat.mul_le_mul_right (2^ell) (v.wide_group_space x.h)
    change ((WideMemory.dir x.h v.W k v.wideJobs).groups+1)*
      (WideMemory.H x.h v.W k v.wideJobs*2^ell)≤ (v.widePackedFactor*2^ell)*2^x.h
    simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using atSlots
  have Gmax : f.groups*f.D≤ space*n:=by nlinarith only [pool,Nat.zero_le f.D]
  have allCells : f.window.C*f.D≤ cells*n:=candidate_volume cu address height pool
  have groups : f.groups+1≤ space*n:=(Nat.le_mul_of_pos_right _ Dpos).trans pool
  have binRows : f.window.bins≤ binCost*n := by
    change 2^groupBits f.groups*(m+1)≤ _
    calc
      _ ≤ (2*(f.groups+1))*(m+1):=Nat.mul_le_mul_right _ (bias_words _)
      _ ≤ (2*(space*n))*(m+1):=Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ groups)
      _ = _:=by dsimp [binCost];ring
  have rows : f.N≤ v.rowFactor*n:=v.wideCatalogueRows x.h x.w
  have tape : f.N*f.cap≤ (v.rowFactor*cap)*n:=(Nat.mul_le_mul_right cap rows).trans_eq (by ring)
  have base : 1≤ n:=Nat.two_pow_pos _
  have cost (j : ℕ) (h : j≤ charge) : j*n≤ charge*n:=Nat.mul_le_mul_right _ h
  have unit : 1≤ charge*n:=base.trans (by simpa using cost 1 (by dsimp [charge];omega))
  have out:=frozen_window_bound f (charge*n) unit (rows.trans (cost _ (by dsimp [charge];omega)))
    (binRows.trans (cost _ (by dsimp [charge];omega))) (allCells.trans (cost _ (by dsimp [charge];omega)))
    Dpos (Gmax.trans (cost _ (by dsimp [charge];omega))) (tape.trans (cost _ (by dsimp [charge];omega)))
  simpa only [Nat.mul_assoc] using out

theorem wideWindow_owner (x : WideParent κ A) (cap : ℕ) (dated : WideCPU.Dated (events v.mesh).length)
    (bits rom : ℕ) (i : Fin (m+1)) :
    ((v.wideWindowProgramLayout x m ell short u δ ξ cap dated bits rom).inputs i).owner.work=17 := by
  rfl

include hu in
/-- Sum of the actual window clocks followed by the exact prune procedure that the
layout charges. The coefficient includes the bounded multiplication in the prune term. -/
theorem wide_format_runtime (cap : ℕ) :
    ∃ K : ℕ,∀ (x : WideParent κ A) (dated : WideCPU.Dated (events v.mesh).length) (bits rom : ℕ),
    let l:=v.wideWindowProgramLayout x m ell short u δ ξ cap dated bits rom
    (∑i,l.windowTicks i)+(4+(l.pruneRows+1)*(42+2*l.prune.work))≤ K*2^x.h := by
  obtain ⟨K,volume⟩:=v.wideWindowVolume (κ:=κ) (A:=A) m ell short hu δ ξ cap
  let b:=BoughtSockets.Public.maxMetric v.radius
  let cost:=42+2*(47+20*b+9*b*(b+1))
  refine ⟨(m+1)*K+4+(v.rowFactor+1)*cost,?_⟩
  intro x dated bits rom l
  let n:=2^x.h
  have clocks (i) : l.windowTicks i≤ K*n :=
    (volume x (v.wideFormatROM x dated bits rom) i).2 (l.windowBase i) (l.inputs i)
      (v.wideWindow_owner (m:=m) (ell:=ell) (short:=short) (u:=u) (δ:=δ) (ξ:=ξ)
        x cap dated bits rom i)
  have total:=window_sum_le l.windowTicks clocks
  have rows : l.pruneRows≤ v.rowFactor*n:=v.wideCatalogueRows x.h x.w
  have pos : 1≤ n:=Nat.two_pow_pos x.h
  have rowCap : l.pruneRows+1≤ (v.rowFactor+1)*n := by nlinarith only [rows,pos]
  have prune : l.prune.work=47+20*b+9*b*(b+1) := PruneFlag.term_work ..
  rw [prune]
  change (∑i,l.windowTicks i)+(4+(l.pruneRows+1)*cost)≤ _*n
  have paid:=Nat.mul_le_mul_right cost rowCap
  nlinarith only [total,paid,pos]

include hu in
/-- Every class reserves the sum of the class volumes as its stride. The extra row
area of the original catalogue and its final accumulated flag both fit above that stride. -/
theorem wide_window_workspace_extent (cap : ℕ) :
    ∃ K : ℕ,∀ (x : WideParent κ A) (dated : WideCPU.Dated (events v.mesh).length) (bits rom : ℕ),
    let l:=v.wideWindowProgramLayout x m ell short u δ ξ cap dated bits rom
    l.pruneScratch+l.pruneRows+1≤ l.floor+K*2^x.h := by
  obtain ⟨K,volume⟩:=v.wideWindowVolume (κ:=κ) (A:=A) m ell short hu δ ξ cap
  refine ⟨(m+1)*((m+1)*K)+v.rowFactor+1,?_⟩
  intro x dated bits rom l
  let n:=2^x.h
  have need (i) : l.need i≤ K*n:=(volume x (v.wideFormatROM x dated bits rom) i).1
  have stride:=window_sum_le l.need need
  have occupied:=Nat.mul_le_mul_left (m+1) stride
  have rows : l.pruneRows≤ v.rowFactor*n:=v.wideCatalogueRows x.h x.w
  have scratch : l.pruneScratch=l.floor+(m+1)*(∑i,l.need i):=rfl
  have pos : 1≤ n:=Nat.two_pow_pos x.h
  rw [scratch]
  change _≤ l.floor+_*n
  nlinarith only [rows,occupied,pos]

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
