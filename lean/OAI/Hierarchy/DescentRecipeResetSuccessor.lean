import OAI.Hierarchy.DescentRecipeGroupStage
import OAI.Hierarchy.DescentResetSuccessor
import OAI.Hierarchy.DescentFixedMenu
import OAI.Hierarchy.DescentOccurrenceAllowance

namespace OAI
/-! # The scheduled reset carries its issued recipe occurrences into the next subround -/

namespace Hierarchy.DescentSixParty.GroupStage
open DescentCompiler DescentColonies DescentHostDegree DescentMixedRouter DescentRotor DescentResetTrunks
open DescentKernelHistory DescentNetworkSubstitution
open scoped Classical BigOperators
noncomputable section

variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
  {d k i : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {q ε : ℝ} {G : PoweredGadget F}
  (A : GroupStage W G q ε J V k) (S : AtomSchedule) (ready : A.StateBounds S i)
local notation "grain" => A.z*G.b
local notation "full" => A.wire*grain*A.cap
variable {h C Ht f g cut : ℕ}
  (Z : ResetInput (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)) (q*A.wire) ε h C Ht)
  (T : Z.Terminals)
local notation "hg" => ResetInput.resetHostGain h (2^Z.n) Ht
local notation "J₁" => Fin (S.groupCount (i+1))

/-- Install each actual lane operation at its published site. The inherited
exterior operations have their own port indices and do not consume a second
retained token. The retained sum and new capacity use the same chosen gain. -/
theorem recipe_reset_successor {L p : ℕ}
    (key : (W.granular A.grainCount grain (A.grainCount_fit S ready)).graph.Edge ↪ Fin L)
    (digits : Block T.commonDepth ≃ J₁×Block k)
    (budget : ε=((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
    (positive : 0<S.height) (age : i<S.length) (radix : S.radix=2^k)
    (fixed : k=groupBits S.rounds S.height S.hostGain S.capGain cut)
    (pos : Fintype.card Z.V=Fintype.card V)
    (unit : Z.unit=grain) (atHub : ∀u,Z.hub u=A.hub (A.pos u).2)
    (bill : Z.ActorBudget T A.records A.wire A.hist f g full)
    (gainDef : g=reserveGain h C f) (range : Z.k-T.commonDepth≤k)
    (gain : hg≤S.hostGain) (rate : g≤S.capGain) (fineRate : g≤S.capGain-(G.b+3)) (cut₀ : packExponent 20 3≤cut)
    (hp : 0<p) (grainAt : A.z=S.grainAt G.b p (i+1)) (base : G.b≤2^S.capGain)
    (wire : A.wire=S.epochPower^S.priceExponent) (hist : A.hist=S.firstWidth G.b p) :
    let m:=ResetInput.calendarLanes S G.b (i+1)
    let fit:=ResetInput.calendar_fit Z S G.b p (i+1) (unit.trans (congrArg (·*G.b) grainAt))
    ∃N : GroupStage (Z.orderedOrdinary T key) G q ε J₁ ↥(Z.commonNames T) k,
      N.StateBounds S (i+1) ∧ N.z=A.z ∧ N.wire=A.wire ∧ N.hist=A.hist ∧
      N.degree=3 ∧ N.cap=2^g*A.cap ∧ N.pos=Z.groupPosition T digits ∧ N.block=Z.groupBlock T digits ∧ N.hub=Z.commonTag T ∧
      N.near=Z.emittedNear T ∧ (∀u,N.hub (N.pos u).2=Z.reentryTag T u) ∧
      HEq N.records (Z.recipeRecords T A.records (Z.laneRecipe key m p hp fit)) ∧
      ∀u,(N.records u).length=(Z.recipeRecords T A.records (Z.laneRecipe key m p hp fit) u).length := by
  let m:=ResetInput.calendarLanes S G.b (i+1)
  have fit : Z.unit=m*p:=ResetInput.calendar_fit Z S G.b p (i+1) (unit.trans (congrArg (·*G.b) grainAt))
  let prog:=Z.laneRecipe key m p hp fit
  have hw : 0< m := by dsimp [m,ResetInput.calendarLanes,AtomSchedule.grainAt];have hb:=G.base_pos;positivity
  have unitWidth : p≤Z.unit := by rw [fit];exact Nat.le_mul_of_pos_left p hw
  have limit : m≤G.b^(S.rounds*S.height+1) := by
    simpa only [one_mul,m,ResetInput.calendarLanes] using S.normalized_grain_le G.b 1 (i+1) G.base_pos
  have affordable : 6*A.hist≤A.wire*p := by
    rw [wire,hist]
    exact S.lane_token_price positive base p
  have cheap : A.hist≤full := calc
    A.hist ≤ A.wire*p := by omega
    _ ≤ A.wire*grain := Nat.mul_le_mul_left _ (unitWidth.trans unit.le)
    _ ≤ _ := Nat.le_mul_of_pos_right _ A.capPos
  have reserve:=reset_allocations h C f full A.hist cheap
  have extra:=reset_recipe_allocations h C f full A.hist cheap
  rw [←gainDef] at reserve extra
  let newCap := 2^g*A.cap
  have hc : 0<newCap := Nat.mul_pos (Nat.two_pow_pos _) A.capPos
  have kept : ∀u,Z.hub u=true→A.records u=[] := fun u eq=>A.noHubAtoms u ((atHub u).symm.trans eq)
  have positions : Fintype.card Z.V≤S.hostSize i := pos ▸ ready.host
  have groups := Z.reset_digit_population T S digits (by simp : Fintype.card J₁≤S.groupCount (i+1)) radix.ge
  have actual : Fintype.card Z.V*(2^hg*2^k)≤S.hostSize (i+1) :=
    S.host_step positions (Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) gain) radix.ge))
  have nextHost := (Z.placed_growth T range).trans actual
  have cap : newCap≤2^(8+S.capGain*(i+1)) := calc
    _ ≤ 2^S.capGain*2^(8+S.capGain*i) := Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) rate) ready.capacity
    _ = _ := by rw [←pow_add];congr 1;ring
  have fineCap : newCap≤2^(8+(S.capGain-(G.b+3))*(i+1)) := calc
    _ ≤ 2^(S.capGain-(G.b+3))*2^(8+(S.capGain-(G.b+3))*i) :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) fineRate) ready.bundleCapacity
    _ = _ := by rw [←pow_add];congr 1;ring
  have charged : q*((2^g*full:ℕ):ℝ)≤(2:ℝ)^(8+S.capGain*(i+1)) := calc
    _ = (q*((A.wire*grain:ℕ):ℝ))*(newCap:ℝ) := by dsimp [newCap];push_cast;ring
    _ ≤ newCap := by simpa using mul_le_mul_of_nonneg_right ready.paidUnit (Nat.cast_nonneg newCap)
    _ ≤ _ := by exact_mod_cast cap
  have counted : Fintype.card Z.V*(2^hg*2^k) ≤ S.initialSites *
      (2^S.hostGain*2^groupBits S.rounds S.height S.hostGain S.capGain cut)^(i+1) := by
    simpa only [AtomSchedule.hostSize,radix,fixed] using actual
  have roots := point_root_real (R:=S.baseGroups) (Nat.succ_le_of_lt age) counted cut₀ charged
  have scale : A.wire*grain*newCap=2^g*full := by dsimp [newCap];ring
  have amount:=ResetInput.physical_birth_count Z T A.records A.wire A.hist f g full bill
    (by exact_mod_cast reserve.2.1) (by exact_mod_cast reserve.2.2.1) (by exact_mod_cast reserve.2.2.2)
    prog A.wirePos hp unitWidth
    (show 2^g*full=A.wire*(p*m)*newCap by rw [←scale,←unit,fit,Nat.mul_comm p m])
    (Z.lane_count_mul_le key m p hp fit)
  have growth : 0<g := by
    by_contra! zero
    have step:=(reset_recipe_allocations h C f 1 0 (Nat.zero_le _)).2.2.1
    rw [←gainDef,Nat.eq_zero_of_le_zero zero] at step
    norm_num at step
    have one : 1≤(2:ℝ)^f:=one_le_pow₀ (by norm_num)
    linarith only [step,one]
  have fresh:=amount.trans ((Nat.mul_le_mul_right _ (Nat.mul_le_mul nextHost groups)).trans
    (S.lane_batch positive age (Nat.lt_two_pow_self (n:=G.b)).le limit fineCap (by omega : G.b+(S.capGain-(G.b+3))≤S.capGain)))
  have entered:=S.advance ready.history fresh
  have pay:=S.paid positive ready.atom age entered
  rw [←ready.valuation,←budget] at pay
  let N := Z.recipe_group_stage T A.records prog A.wire A.hist f g full bill key digits G q ε A.z newCap
    A.fieldBits A.pricePos A.wirePos A.unitPos hc unit scale unitWidth (by omega) (Z.lane_count_mul_le key m p hp fit)
    (by exact_mod_cast ((le_add_of_nonneg_right (Nat.cast_nonneg A.hist)).trans extra.2.1))
    (by exact_mod_cast ((le_add_of_nonneg_right (Nat.cast_nonneg A.hist)).trans extra.2.2.1))
    kept (by
      rw [Nat.add_assoc]
      with_unfolding_all exact pay) range
    (by simpa only [budget,Fintype.card_fin,AtomSchedule.copies,AtomSchedule.groupCount,AtomSchedule.epochPower,
      AtomSchedule.length,radix,fixed,DescentCompiler.residual,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using roots)
  refine ⟨N,⟨Z.group_coordinates T digits,nextHost,cap,fineCap,?_,ready.atom,ready.valuation,ready.paidUnit,?_⟩,
    rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,Z.placed_tag T,HEq.rfl,fun _=>rfl⟩
  · change S.Within (i+1) (∑u,(Z.recipeRecords T A.records prog u).length)
    have within := (congrArg (S.Within (i+1)) (Z.recipeRecords_count T A.records prog)).mpr
      (by rw [Nat.add_assoc]; with_unfolding_all exact entered)
    with_unfolding_all exact within
  · intro e
    change grain∣(Z.orderedOrdinary T key).graph.width e
    apply (congrArg (fun u : ℕ => u ∣ (Z.orderedOrdinary T key).graph.width e) unit).mp
    rcases e with old|part
    · exact Z.reentry_divides T old.val
    · exact dvd_refl _

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
