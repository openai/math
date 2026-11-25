import OAI.Hierarchy.DescentTerminalCalibratedRowArithmetic
import OAI.Hierarchy.DescentNormalizedEpochs
import OAI.Hierarchy.DescentTerminalGraphPurchase

namespace OAI
/-! # A branch-independent row pool from the normalized run's actual terminal bound -/

namespace Hierarchy.DescentSixParty
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open DescentTerminalGraphPositions DescentTerminalGraphVolume DescentTerminalBinPack CorrectionBatch
open scoped Classical BigOperators
noncomputable section

theorem integralFrontier_bound {T m copies pins rate live tethers : ℕ} (pos : 0<T) (K : ℝ) (rounded : K≤rate)
    (core : (live:ℝ)≤(copies:ℝ)*((m:ℝ)/T+2*K*((pins:ℝ)+(m:ℝ)/T)))
    (outside : tethers≤copies*pins) : live+tethers≤ integralFrontier T m copies pins rate := by
  have ht : (0:ℝ)<T:=by exact_mod_cast pos
  have ext : (tethers:ℝ)≤(copies:ℝ)*pins := by exact_mod_cast outside
  have rr : (live:ℝ)+tethers≤(1+2*(rate:ℝ))*copies*((m:ℝ)/T+pins) := calc
    _ ≤ (copies:ℝ)*((m:ℝ)/T+2*K*((pins:ℝ)+(m:ℝ)/T))+(copies:ℝ)*pins := add_le_add core ext
    _ ≤ (copies:ℝ)*((m:ℝ)/T+2*(rate:ℝ)*((pins:ℝ)+(m:ℝ)/T))+(copies:ℝ)*pins := by gcongr
    _ = _ := by ring
  have full : ((live:ℝ)+tethers)*T ≤ (1+2*(rate:ℝ))*copies*(m+(T:ℝ)*pins) := calc
    _ ≤ (1+2*(rate:ℝ))*copies*((m:ℝ)/T+pins)*T := mul_le_mul_of_nonneg_right rr ht.le
    _ = _ := by field_simp
  apply (Nat.le_div_iff_mul_le pos).2
  exact_mod_cast full

variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
local notation "wire" => S.epochPower^S.priceExponent
local notation "s" => S.firstWidth G.b p
local notation "price" => (1/((s:ℝ)*(wire:ℝ)):ℝ)
local notation "ε" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "u" => price*(wire:ℝ)
local notation "resetDepth" => GroupStage.depthBound (atRound S.rounds) n f g
local notation "start" => initialGroup X S.copies s
local notation "E" => Fintype.card (Port P X.width)
local notation "d" => S.copies*s
local notation "K" => 258*reentryRate h C+reentryExteriorRate h C 256 resetDepth
local notation "T" => S.epochPower
local notation "total" => integralFrontier T S.initialSites d E ⌈K⌉₊
local notation "homes" => S.hostSize S.length

/-- The two numerical hypotheses are precisely the last two projections of
the same normalized choice that supplies b and the terminal native row order. -/
theorem NativeBranch.bought_bins {he : 0≤ε} {hu : 0≤u} {radix : S.radix=2^k}
    {r : Epochs G hu he (h:=h) (C:=C) (Ht:=resetDepth) (t:=S.rounds) S.height start}
    {c : (Epochs.finish G hu he r).Choice}
    (b : NativeBranch X G S (p := p) (n := n) (h := h) (C := C) (f := f) (g := g) radix R r c)
    (q width : ℕ) (hq : 0<q) (hp : 0<p) (hw : 0<width)
    (order : Order ((Epochs.finish G hu he r).state c).graph homes p) (home : order.home=b.target.home)
    (outside : ((Epochs.finish G hu he r).state c).tetherWidth≤d*E)
    (live : (((Epochs.finish G hu he r).state c).liveWidth:ℝ)≤
      (d:ℝ)*((S.initialSites:ℝ)/T+2*K*((E:ℝ)+(S.initialSites:ℝ)/T))) :
    bins width (fun i=>(order.site i).rows q)≤rowBudget p q width total (d*E) homes 3/width := by
  let world := (Epochs.finish G hu he r).state c
  have pos : 0<T:=Nat.two_pow_pos _
  have paid : world.liveWidth + world.tetherWidth ≤ total := by
    exact integralFrontier_bound (copies := d) pos K (Nat.le_ceil K)
      (by simpa only [Nat.cast_mul] using live) outside
  have split:=Finset.sum_add_sum_compl world.core world.graph.width
  change world.liveWidth+world.tetherWidth=∑e,world.graph.width e at split
  have stored : p∣s := by
    unfold AtomSchedule.firstWidth AtomSchedule.grainAt
    exact ⟨G.b^(S.rounds*S.height-S.ordinaryDone 0)*G.b,by ac_rfl⟩
  have bits (z : (Σ _ : Fin S.copies,Fin E)) : p∣(fun _ : (Σ _ : Fin S.copies,Fin E)=>s*1) z := by
    simpa using stored
  have outer : (∑_ : (Σ _ : Fin S.copies,Fin E),s*1)≤d*E := by
    simp [Fintype.card_sigma,Nat.mul_assoc,Nat.mul_comm]
  have neighbor:=b.target.terminal_groups order home
  rw [b.target.branch] at neighbor
  apply fixed_bins order q width 3 total (d*E) hp hq hw _ bits (split ▸ paid) outer neighbor
  intro e
  have input:=b.target.valid.divides e
  rw [b.target.grain] at input
  exact dvd_trans (dvd_mul_right p G.b) input

end
end Hierarchy.DescentSixParty

end OAI
