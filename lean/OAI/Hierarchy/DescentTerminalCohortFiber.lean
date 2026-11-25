import OAI.Hierarchy.DescentNativeExteriorRows
import OAI.Hierarchy.DescentTerminalPacketSlotRAM

namespace OAI
/-! # Genuine attached pins are a complete active fiber over each surviving frozen cohort -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch DescentKernelHistory
open scoped Classical
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

def cohort (pin : SeedPin) : Cohort :=
  finProdFinEquiv (pin.2,address f ((trace).cut (active b.source base radix pin)).2)

def activeAt (v : (N).Site) : Bits a :=
  (address _).symm ((S.resetInputDigits base radix S.length).symm (((A).pos v).1,(A).block v))

def atCohort (x : Bits a) (j : Cohort) : SeedPin :=
  originalPin X G S b hp base x ((address f).symm (finProdFinEquiv.symm j).2) (finProdFinEquiv.symm j).1

theorem cohort_at (x : Bits a) (j : Cohort) :
    cohort X G S b hp base (atCohort X G S b hp base x j)=j := by
  unfold cohort atCohort
  rw [pinCoordinates]
  simp [originalPin]
  exact finProdFinEquiv.apply_symm_apply j

theorem at_cohort (z : SeedPin) :
    atCohort X G S b hp base (active b.target base radix z) (cohort X G S b hp base z)=z := by
  apply Sigma.ext
  · apply (copyBits S base radix).injective
    apply (trace).cut.injective
    change (trace).cut (copyBits S base radix ((atCohort X G S b hp base _ _).1))=(trace).cut (copyBits S base radix z.1)
    simp only [atCohort,cohort,Equiv.symm_apply_apply]
    change (trace).cut (copyBits S base radix ((copyBits S base radix).symm _))=_
    rw [Equiv.apply_symm_apply,LinearEquiv.apply_symm_apply,←source_bits X G S b base z]
    exact Prod.ext ((trace).active_eq z).symm rfl
  · simp [atCohort,cohort,originalPin]

def cohortHome (j : Cohort) : Fin H :=
  b.target.home ((N).attach (atCohort X G S b hp base 0 j))

theorem home_cohort (x : Bits a) (j : Cohort) :
    b.target.home ((N).attach (atCohort X G S b hp base x j))=cohortHome X G S b hp base j := by
  apply b.target.home_eq.mpr
  exact terminal_host X G S b hp base x 0 _ _

local notation "id_" => cohort X G S b hp base
local notation "name_" => cohortHome X G S b hp base
local notation "seat" => activeAt X G S b base

theorem attach_at (v : (N).Site) (j : Cohort) (here : name_ j=b.target.home v) :
    (N).attach (atCohort X G S b hp base (seat v) j)=v := by
  let z:=atCohort X G S b hp base (seat v) j
  have loc : ((A).pos ((N).attach z)).2=((A).pos v).2 :=
    b.target.home_eq.mp ((home_cohort X G S b hp base _ j).trans here)
  have live : active b.target base radix z=seat v := terminal_active X G S b hp base _ _ _
  have coords:=congrArg (fun x:Bits a=>(S.resetInputDigits base radix S.length) (address _ x)) live
  simp only [active,activeAt,Equiv.apply_symm_apply] at coords
  have groupEq := congrArg (fun p : Fin (S.groupCount S.length) × Block k => p.1) coords
  have blockEq := congrArg (fun p : Fin (S.groupCount S.length) × Block k => p.2) coords
  exact b.target.valid.coordinates (Prod.ext (Prod.ext groupEq loc) blockEq)

/-- This chart removes both repeated packet lanes and padding. It is independent of how
the original scalar operand was moved through any intermediate edge reordering. -/
def attachedCohorts (v : (N).Site) : Attached N v ≃ {j:Cohort // name_ j=b.target.home v} where
  toFun z:=⟨id_ z.1,by rw [←home_cohort X G S b hp base (active b.target base radix z.1),at_cohort,z.2]⟩
  invFun j:=⟨atCohort X G S b hp base (seat v) j.1,attach_at X G S b hp base v j.1 j.2⟩
  left_inv z:=by
    apply Subtype.ext
    have live : seat v=active b.target base radix z.1 := by simp only [active,activeAt,z.2]
    change atCohort X G S b hp base (seat v) (id_ z.1)=z.1
    rw [live,at_cohort]
  right_inv j:=Subtype.ext (cohort_at X G S b hp base _ _)

/-- The published prefix on one row per cohort is an injective small local port name. -/
def densePin (v : (N).Site) : Attached N v↪ℕ where
  toFun z:=Computability.BorderVNP.FragmentBucket.prior name_ (id_ z.1).val (b.target.home v)
  inj' := by
    intro z z' rank
    apply (attachedCohorts X G S b hp base v).injective
    apply Subtype.ext
    change id_ z.1=id_ z'.1
    apply (Computability.BorderVNP.FragmentBucket.dest name_).injective
    apply Fin.ext
    have zHome : name_ (id_ z.1)=b.target.home v := ((attachedCohorts X G S b hp base v) z).2
    have zHome' : name_ (id_ z'.1)=b.target.home v := ((attachedCohorts X G S b hp base v) z').2
    rw [Computability.BorderVNP.FragmentBucket.dest_val,Computability.BorderVNP.FragmentBucket.dest_val,zHome,zHome']
    exact congrArg (Computability.BorderVNP.FragmentBucket.start name_ (b.target.home v).val + ·) rank

end NativeBranch
end
end Hierarchy.DescentSixParty

end OAI
