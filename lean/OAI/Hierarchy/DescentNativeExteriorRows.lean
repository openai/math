import OAI.Hierarchy.DescentTerminalCohortOrder
import OAI.Hierarchy.DescentTerminalReachedOrder
import OAI.Hierarchy.DescentTerminalPortChart
import OAI.Hierarchy.DescentNativePinSpine
import OAI.Hierarchy.DescentNormalizedEpochs

namespace OAI
/-! # Whole physical exterior rows from a reached branch of the original host -/

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
open DescentTerminalExteriorPackets
variable {tail j rest : ℕ} (base : S.baseGroups=2^tail)
local notation "initialBits" => S.groupWidth k tail 0+k
local notation "retained" => S.groupWidth k tail S.length+k
local notation "shape" => j+(j+rest)
local notation "E" => Fintype.card (Port P X.width)
local notation "Public" => Σ _:Fin (2^shape),Fin E
variable (width : S.groupWidth k tail 0 + k = j + (j + rest))

include base radix width in
theorem copy_power : S.copies=2^shape := by
  rw [←width]
  simp [AtomSchedule.copies,AtomSchedule.groupWidth,base,radix,pow_add,pow_mul,pow_succ,
    Nat.mul_left_comm,Nat.mul_comm]

def rawPin : Public ≃ SeedPin :=
  { toFun:=fun u=>⟨Fin.cast (copy_power S (radix:=radix) base width).symm u.1,u.2⟩
    invFun:=fun u=>⟨Fin.cast (copy_power S (radix:=radix) base width) u.1,u.2⟩
    left_inv:=fun ⟨_,_⟩=>by simp
    right_inv:=fun ⟨_,_⟩=>by simp }

local notation "pin" => rawPin S (X:=X) (radix:=radix) base width
local notation "old" => fun u:Public=>(address shape).symm u.1
local notation "last" => fun u:Public=>active b.target base radix (pin u)
local notation "came" => fun u:Public=>host b.source (pin u)
local notation "whereAt" => fun u:Public=>host b.target (pin u)

include hp in
def publicSpine : Spine old last came whereAt b.path.frozen := by
  let trace:=NativeBranch.pinSpine X G S b hp base
  have eqn (u:Public) : castBits width.symm ((address shape).symm u.1)=active b.source base radix (pin u) := by
    apply (address initialBits).injective
    apply Fin.ext
    rw [address_cast,Equiv.apply_symm_apply]
    exact (NativeBranch.pinInput X G S b base (pin u)).symm
  refine ⟨(castBits width.symm).trans trace.cut,?_,?_⟩
  · intro u
    change (trace.cut (castBits width.symm _)).1=_
    rw [eqn];exact trace.active_eq (pin u)
  · intro u v same eq
    apply trace.host_eq (pin u) (pin v) same
    change (trace.cut (castBits width.symm _)).2=(trace.cut (castBits width.symm _)).2 at eq
    simpa only [eqn] using eq

local notation "track" => publicSpine X G S b hp base width
local notation "idLayout" => fun _:Fin E=>LinearEquiv.refl (ZMod 2) (Bits shape)
def publicLayout : Fin E→Layout shape := rotor track idLayout

def publicHost (u:Fin (E*2^(j+rest))) : Fin (S.hostSize S.length) :=
  (b.target.vertex (owner track idLayout u)).castLE b.target.valid.host

theorem public_host_read (room : j≤retained) (u : Public) :
    b.target.home (((Epochs.finish G hu he r).state c).graph.attach (pin u))=
      publicHost X G S b hp base width (chart (j:=j) (r:=rest) (publicLayout X G S b hp base width) u).1 := by
  have actual:=owner_at track idLayout room (fun _=>rfl)
    (fun u v eqn=>NativeBranch.pinHost X G S b (a:=pin u) (b':=pin v) eqn) u
  exact congrArg (fun a=>(b.target.vertex a).castLE b.target.valid.host) actual

local notation "N" => ((Epochs.finish G hu he r).state c).graph
local notation "rows" => chart (j:=j) (r:=rest) (publicLayout X G S b hp base width)
local notation "homeRow" => publicHost X G S b hp base width

/-- Genuine output row of the physical common-home sort, restricted to the
pins attached to one vertex. A cohort has at most one lane at that vertex. -/
def exteriorSlot (room : j≤retained) (v : (N).Site) : DescentKernelHistory.Attached N v ↪ ℕ where
  toFun a:=let i:=(rows ((pin).symm a.val)).1
           Computability.BorderVNP.FragmentBucket.prior homeRow i.val (homeRow i)
  inj' := by
    intro a b' score
    let u:=(pin).symm a.val
    let v':=(pin).symm b'.val
    have here : homeRow (rows u).1=homeRow (rows v').1 := by
      rw [←public_host_read X G S b hp base width room u,←public_host_read X G S b hp base width room v']
      simp only [u,v',Equiv.apply_symm_apply,a.property,b'.property]
    have sameRow : (rows u).1=(rows v').1 := by
      apply (Computability.BorderVNP.FragmentBucket.dest homeRow).injective
      apply Fin.ext
      rw [Computability.BorderVNP.FragmentBucket.dest_val,Computability.BorderVNP.FragmentBucket.dest_val]
      change Computability.BorderVNP.FragmentBucket.prior homeRow (rows u).1.val (homeRow (rows u).1)=
        Computability.BorderVNP.FragmentBucket.prior homeRow (rows v').1.val (homeRow (rows v').1) at score
      rw [score,here]
    apply Subtype.ext
    apply (pin).symm.injective
    apply separate track idLayout room (fun _=>rfl) u v' sameRow
    simp only [u,v',Equiv.apply_symm_apply,active,a.property,b'.property]

theorem exterior_slot_read (room : j≤retained) (v : (N).Site) (a : DescentKernelHistory.Attached N v) :
    exteriorSlot X G S b hp base width room v a=
      let i:=(rows ((pin).symm a.val)).1
      Computability.BorderVNP.FragmentBucket.prior homeRow i.val (homeRow i) := rfl

end NativeBranch
end
end Hierarchy.DescentSixParty

end OAI
