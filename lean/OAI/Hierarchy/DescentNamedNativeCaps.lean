import OAI.Hierarchy.DescentTerminalNativeLimits
import OAI.Hierarchy.DescentNamedCohortMemory
import OAI.Hierarchy.DescentTerminalLocalGrain
import OAI.Hierarchy.DescentTerminalFrozenRosterRAM
import OAI.Hierarchy.DescentNamedSiteBill

namespace OAI
/-! # Fixed scalar row, site and frozen-roster capacities on the actual terminal epoch -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch DescentKernelHistory
open scoped Classical
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p R : ℕ}
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
  {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
    (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix = 2^k}
variable {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
  (t := S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
variable {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c) (hp : 0 < p)


local notation "s" => S.firstWidth G.b p
open DescentGL DescentColonies DescentExterior PinCohorts
local notation "SeedPin" => Σ _ : Fin S.copies, Fin (Fintype.card (Port P X.width))


namespace Branch
variable {tail : ℕ} (base : S.baseGroups=2^tail)
local notation "trace" => pinSpine X G S b hp base
local notation "E" => Fintype.card (Port P X.width)
local notation "H" => S.hostSize S.length
local notation "a" => S.groupWidth k tail S.length+k
local notation "N" => ((Epochs.finish G hu he r).state c).graph
local notation "A" => b.target.placement
local notation "f" => b.path.frozen
local notation "Cohort" => Fin (E*2^f)


local notation "W" => (Epochs.finish G hu he r).state c
local notation "cap_" => 2^(8+S.capGain*S.length)
local notation "homes" => cohortHome X G S b hp base

include b hp in
theorem final_slots (v:(N).Site) : DescentTerminalGraphRows.arity N p v ≤ NativeBranch.localLimit G S := by
  have particles:=site_particles X G S b hp
  have stored : p∣s := by
    unfold AtomSchedule.firstWidth AtomSchedule.grainAt
    exact ⟨G.b^(S.rounds*S.height-S.ordinaryDone 0)*G.b,by ac_rfl⟩
  have peers (e : (N).Edge) : p∣(N).width e := by
    have h:=b.target.valid.divides e
    rw [b.target.grain] at h
    exact dvd_trans (dvd_mul_right p G.b) h
  have cap:=b.target.valid.capacity
  have room:=(W).local_grain A b.target.grain hp peers (fun _=>by simpa using stored) particles.balance particles.attached v
  exact room.trans (by unfold NativeBranch.localLimit;rw [Nat.mul_assoc];gcongr)

include hp in
theorem final_rows {q:ℕ} (enough:NativeBranch.localLimit G S ≤ q) (positive:0<q)
    (order:DescentTerminalGraphPositions.Order N H p) (where_:order.home=b.target.home) (i:Fin H) :
    (order.site i).rows q ≤ NativeBranch.binLimit (k:=k) S := by
  apply DescentTerminalGraphVolume.home_rows order q (S.groupCount S.length*2^k) 3 positive
    (fun v=>(final_slots X G S b hp v).trans enough)
  · intro i
    change Fintype.card {v:(N).Site // order.home v=i} ≤ _
    rw [where_];exact b.target.occurrence_bound i
  · intro j
    have edges : ∀e,order.home ((N).dst e)∈b.target.neighbors (order.home ((N).src e)) ∧
        order.home ((N).src e)∈b.target.neighbors (order.home ((N).dst e)) := by rw [where_];exact b.target.near_edge
    have groups:=(order.group_count b.target.neighbors edges j).trans (Nat.add_le_add_right (b.target.neighbor_count j) 1)
    simpa only [b.target.branch] using groups

theorem cohort_separate (v:Fin H) (i j:Cohort) (hi:homes i=v) (hj:homes j=v)
    (same:(finProdFinEquiv.symm i : Fin E×Fin (2^f)).2=(finProdFinEquiv.symm j : Fin E×Fin (2^f)).2) : i=j := by
  have old:=originalSlab_eq X G S b hp (b.target.home_eq.mp (hi.trans hj.symm))
  apply finProdFinEquiv.symm.injective
  apply Prod.ext _ same
  have slab (x : Cohort) :
      (atCohort X G S b hp base 0 x).2 = (finProdFinEquiv.symm x : Fin E × Fin (2^f)).1 := by
    unfold atCohort originalPin
    rfl
  exact (slab i).symm.trans (old.trans (slab j))

theorem cohort_cap (v:Fin H) : Computability.BorderVNP.FragmentBucket.count homes v ≤ cap_ := by
  classical
  by_cases used:∃t:Cohort,homes t=v
  · obtain ⟨t,atHome⟩:=used
    let z:=atCohort X G S b hp base 0 t
    let site:=(N).attach z
    have loc : b.target.home site=v:=atHome
    have size : Fintype.card (Attached N site)=Computability.BorderVNP.FragmentBucket.count homes (b.target.home site) := by
      simpa using Fintype.card_congr (densePinEquiv X G S b hp base site)
    have particles:=site_particles X G S b hp
    have hb : 0<G.b:=by have:=G.paid;omega
    have grain : (A).z*G.b ≤ s:=by
      rw [b.target.grain]
      unfold AtomSchedule.firstWidth AtomSchedule.grainAt
      exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (pow_pos hb _))
    have positive:0 < s:=(Nat.mul_pos (by simpa only [b.target.grain] using hp : 0<(A).z) hb).trans_le grain
    have paid:=(W).hub_token_room A particles.balance s (fun _=>by simp) positive grain site (particles.attached z)
    rw [(W).exterior_token_card,size,loc] at paid
    have cap:=b.target.valid.capacity
    omega
  · change (Finset.univ.filter (fun i=>homes i=v)).card ≤ _
    have eqn : Finset.univ.filter (fun i=>homes i=v)=∅:=by
      ext i;simp;exact fun h=>used ⟨i,h⟩
    rw [eqn,Finset.card_empty]
    exact Nat.zero_le _

attribute [local irreducible] Branch.cohortHome Branch.densePin Branch.cohort Branch.attachedCohorts
  Branch.atCohort DescentTerminalFrozenRoster.book
theorem pinOrdinalFromCopy (v:(N).Site) (z:Attached N v) :
    let addr:=b.target.home v
    let n:=Computability.BorderVNP.FragmentBucket.count homes addr
    let frozen:=fun t:Cohort=>(finProdFinEquiv.symm t : Fin E×Fin (2^f)).2
    DescentTerminalFrozenRoster.lookup f n (DescentTerminalFrozenRoster.book homes frozen addr).val
      (address f ((trace).cut (active b.origin.source base radix z.val)).2).val=densePin X G S b hp base v z := by
  let id_ := cohort X G S b hp base z.val
  let frozen := fun t : Cohort => (finProdFinEquiv.symm t : Fin E × Fin (2^f)).2
  have here : homes id_ = b.target.home v := by
    unfold id_
    have h := ((attachedCohorts X G S b hp base v) z).2
    simpa only [attachedCohorts, Equiv.coe_fn_mk] using h
  have low : frozen id_ = address f ((trace).cut (active b.origin.source base radix z.val)).2 := by
    unfold id_ frozen cohort
    exact congrArg Prod.snd (finProdFinEquiv.symm_apply_apply _)
  have value := DescentTerminalFrozenRoster.lookup_read homes frozen (b.target.home v) (cohort_separate X G S b hp base _) id_ here
  rw [low] at value
  unfold densePin
  exact value

end Branch
end
end Hierarchy.DescentSixParty.SeedNamed
end OAI

open OAI.Hierarchy.DescentSixParty.SeedNamed
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin
