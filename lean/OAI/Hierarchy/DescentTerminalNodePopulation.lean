import OAI.Hierarchy.DescentTerminalNativeCaps
import OAI.Hierarchy.DescentPackedCensusFromSigned
import OAI.Hierarchy.DescentTerminalPopulationDigits

namespace OAI
/-! # Charged recipe records and attached pins give all terminal nodes -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch DescentKernelHistory
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p : ℕ}
variable {he : 0 ≤ ((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower}
    {hu : 0 ≤ 1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower ^ S.priceExponent : ℝ)) *
      (S.epochPower ^ S.priceExponent : ℝ)}
    {radix : S.radix = 2 ^ k} {R : ℕ}
    {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
      (t := S.rounds) S.height (initialGroup X S.copies (S.firstWidth G.b p))}
    {c : (Epochs.finish G hu he r).Choice} (b : NativeBranch X G S radix R r c) (hp : 0<p)

open DescentGL DescentColonies DescentExterior PinCohorts
local notation "SeedPin" => Σ _ : Fin S.copies, Fin (Fintype.card (Port P X.width))


namespace NativeBranch
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

open DescentPacking.PackedMatch.Local.Stage DescentSIMDLookup
local notation "gs" => S.groupCount S.length
local notation "hosts" => b.target.vertex.trans (Fin.castLEEmb b.target.valid.host)
local notation "paid" bits_ => Census.count A (Equiv.refl (Fin gs)) hosts bits_
local notation "exteriorCount" => Computability.BorderVNP.FragmentBucket.count homes
local notation "arch" => NativeBranch.archive X G S b hp

theorem node_population (v : (N).Site) :
    Fintype.card ((arch).bit.recipe v).Node=((A).records v).length+exteriorCount (b.target.home v) := by
  have live:=(site_particles X G S b hp).nodes v
  have attached : (W).exteriorTokens v=exteriorCount (b.target.home v) := by
    rw [(W).exterior_token_card]
    simpa using Fintype.card_congr (densePinEquiv X G S b hp base v)
  exact live.trans (congrArg (((A).records v).length+·) attached)

theorem invoice_lane {paidBits : ℕ} (v : (N).Site) (fits : ((A).records v).length<2^paidBits) :
    ((paid paidBits) (b.target.home v) ((A).pos v).1 ((A).block v)).val=((A).records v).length := by
  have witness : ∃h,hosts h=b.target.home v := ⟨((A).pos v).2,rfl⟩
  have name : witness.choose=((A).pos v).2 := (hosts).injective witness.choose_spec
  rw [Census.count,dite_eq_left witness,name]
  have mass : PackedCensus.histories W (A).pos (A).block (A).records ((A).pos v) ((A).block v)=((A).records v).length := by
    unfold PackedCensus.histories StarKeys.blockMass
    rw [Finset.sum_eq_single v]
    · simp
    · intro u _ neq
      apply ite_eq_right
      exact fun h=>neq (b.target.valid.coordinates (Prod.ext h.1 h.2))
    · simp
  change ((PackedCensus.histories W (A).pos (A).block (A).records ((A).pos v) ((A).block v) : ℕ):Cell paidBits).val=_
  rw [mass,Fin.val_cast_of_lt fits]

/-- A nonempty frozen home has an actual site. A vacant block at that
same host therefore still has a bounded common exterior digit. -/
theorem all_exterior_lanes (nodeBits : ℕ) (all : ∀v : (N).Site,Fintype.card ((arch).bit.recipe v).Node<2^nodeBits)
    (h : Fin H) : exteriorCount h<2^nodeBits := by
  classical
  by_cases head : ∃t:Cohort,homes t=h
  · obtain ⟨t,rfl⟩:=head
    let v:=(N).attach (atCohort X G S b hp base 0 t)
    have named : b.target.home v=homes t := rfl
    have count:=node_population X G S b hp base v
    have room:=all v
    rw [named] at count
    omega
  · have blank : exteriorCount h=0 := by
      change (Finset.univ.filter (fun j=>homes j=h)).card=0
      have empty : Finset.univ.filter (fun j=>homes j=h)=∅ := by ext j;simp;exact fun belongs=>head ⟨j,belongs⟩
      simp [empty]
    rw [blank];exact Nat.two_pow_pos _

theorem all_node_lanes (paidBits nodeBits : ℕ)
    (all : ∀v : (N).Site,Fintype.card ((arch).bit.recipe v).Node<2^nodeBits)
    (x : Block k) (h : Fin H) (j : Fin gs) :
    ((paid paidBits) h j x).val+exteriorCount h<2^nodeBits := by
  have extFit:=all_exterior_lanes X G S b hp base nodeBits all h
  by_cases hasHost : ∃v,hosts v=h
  · obtain ⟨y,rfl⟩:=hasHost
    have named : ∃z,hosts z=hosts y:=⟨y,rfl⟩
    have same_:named.choose=y:=(hosts).injective named.choose_spec
    by_cases live : ∃v:(N).Site,(A).pos v=(j,y) ∧ (A).block v=x
    · obtain ⟨v,hv,bv⟩:=live
      have small_:=(all v)
      have node:=node_population X G S b hp base v
      have home_v : b.target.home v=hosts y:=by change hosts ((A).pos v).2=hosts y;rw [hv]
      rw [home_v] at node
      rw [Census.count,dite_eq_left named,same_]
      have mass : PackedCensus.histories W (A).pos (A).block (A).records (j,y) x=((A).records v).length:=by
        unfold PackedCensus.histories StarKeys.blockMass
        rw [Finset.sum_eq_single v]
        · simp [hv,bv]
        · intro u _ neq
          exact ite_eq_right (fun h=>neq (b.target.valid.coordinates (Prod.ext (h.1.trans hv.symm) (h.2.trans bv.symm))))
        · simp
      change ((PackedCensus.histories W (A).pos (A).block (A).records (j,y) x : ℕ):Cell paidBits).val+_ < _
      rw [mass]
      exact (Nat.add_le_add_right (Nat.mod_le _ _) _).trans_lt (node ▸ small_)
    · have blank : PackedCensus.histories W (A).pos (A).block (A).records (j,y) x=0:=by
        unfold PackedCensus.histories StarKeys.blockMass
        apply Finset.sum_eq_zero;intro u _;exact ite_eq_right (fun both=>live ⟨u,both⟩)
      simpa [Census.count,named,same_,blank] using extFit
  · rw [Census.count, dite_eq_right hasHost]
    simpa using extFit

theorem true_population_word {paidBits nodeBits w M : ℕ} (hm : 0<M) (wide : nodeBits*gs≤w)
    (recordFit : ∀v : (N).Site,((A).records v).length<2^paidBits)
    (nodeFit : ∀v : (N).Site,Fintype.card ((arch).bit.recipe v).Node<2^nodeBits)
    (v : (N).Site) :
    digit nodeBits ((A).pos v).1.val ((DescentTerminalPopulation.words (M:=M) nodeBits
      (fun h j=>(paid paidBits) h j ((A).block v)) exteriorCount (b.target.home v):Fin (2^w)).val)=
      Fintype.card ((arch).bit.recipe v).Node := by
  rw [DescentTerminalPopulation.digit_word _ _ _ _ hm wide (all_node_lanes X G S b hp base paidBits nodeBits nodeFit _),
    invoice_lane X G S b (v:=v) (recordFit v),node_population X G S b hp base]

end NativeBranch
end
end Hierarchy.DescentSixParty

end OAI
