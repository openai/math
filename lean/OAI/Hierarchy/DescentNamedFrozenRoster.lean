import OAI.Hierarchy.DescentNamedCohortMemory
import OAI.Hierarchy.DescentNamedTerminalPointerPins
import OAI.Hierarchy.DescentNamedNativeCaps
import OAI.Hierarchy.DescentTerminalCohortRun

namespace OAI
/-! # The reached named pin spine produces its physically ranked frozen roster -/

namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentTerminalFrozenRoster Computability.BorderVNP.FragmentBucket ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

attribute [local irreducible] DescentTerminalCohortArena.machine DescentTerminalCohortArena.shelf
  DescentTerminalCohortArena.order DescentTerminalCohortArena.indexBase DescentTerminalCohortArena.ticks
  DescentTerminalCohortArena.stop
set_option maxHeartbeats 1000000 in
private theorem measured_cohort_rows {bw n H f k : ℕ} (first : ℕ)
    (room : DescentTerminalCohortArena.stop first f k n H < 2^bw) (source : Bank)
    (m : Memory bw) (alive : 0 < H) (fits : source.Fits bw first) (home : Fin n → Fin H)
    (keys : ∀ u, source.read m (u.val : Computability.VPVNP.BurstRAM.Word bw) = ((home u).val : Computability.VPVNP.BurstRAM.Word bw))
    (bound : ∀ v, count home v ≤ 2^k) (payload : (f+1)*2^k ≤ bw) :
    let bins := DescentTerminalCohortArena.shelf first f k n H room
    let ord := DescentTerminalCohortArena.order first f k n H
    let rank := DescentTerminalCohortArena.indexBase first f k n H
    let frozen := fun u : Fin n => (u.val : Fin (2^f))
    ∃ o : Memory bw, (DescentTerminalCohortArena.machine first f k n H room source).Exec m o
        (DescentTerminalCohortArena.ticks first f k n H room source) ∧
      CheapCode (DescentTerminalCohortArena.machine first f k n H room source) ∧
      (∀ v, (o (bins.bins + (v : Fin H).val)).val = (book home frozen v).val ∧
        (o (ord.counts + v.val)).val = count home v) ∧
      (∀ u, o (rank + (dest home u).val) = (prior home u.val (home u) : Computability.VPVNP.BurstRAM.Word bw)) ∧
      ∀ t < first, o t = m t := by
  intro bins ord rank frozen
  obtain ⟨o, ran, cheap, read, slots, frame⟩ :=
    DescentTerminalCohortArena.produced first f k n H room source m alive fits home keys bound
  refine ⟨o, ran, cheap, ?_, ?_, frame⟩
  · intro v
    have hbits : (f+1)*count home v ≤ bw := (Nat.mul_le_mul_left _ (bound v)).trans payload
    have smallBook : (book home frozen v).val < 2^bw :=
      (book home frozen v).isLt.trans_le (by rw [←pow_mul]; exact Nat.pow_le_pow_right (by decide) hbits)
    have smallCount : count home v < 2^bw :=
      ((bound v).trans ((Nat.le_mul_of_pos_left _ (Nat.succ_pos f)).trans payload)).trans_lt
        (Nat.lt_pow_self (by decide))
    obtain ⟨num, len⟩ := read v
    exact ⟨(congrArg Fin.val num).trans (Fin.val_cast_of_lt smallBook),
      (congrArg Fin.val len).trans (Fin.val_cast_of_lt smallCount)⟩
  · intro u
    simpa only [Equiv.symm_apply_apply] using slots (dest home u)

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch DescentKernelHistory
open scoped Classical
open scoped Fin.CommRing
noncomputable section
attribute [local irreducible] Origin.source Origin.archivePackage Branch.publicSpine Branch.pinSpine Branch.originalPin Branch.cohortHome
set_option quotPrecheck false
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p R : ℕ}
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
  {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
    (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix = 2^k}
variable {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
  (t := S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
variable {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c) (hp : 0 < p)

open DescentGL DescentColonies DescentExterior PinCohorts
local notation "SeedPin" => Σ _ : Fin S.copies, Fin (Fintype.card (Port P X.width))


namespace Branch
open DescentTerminalExteriorPackets DescentExteriorReplay ThreeFlat.RAM PhysicalProcedure
variable {tail j rest : ℕ} (base : S.baseGroups=2^tail)
local notation "initialBits" => S.groupWidth k tail 0+k
local notation "retained" => S.groupWidth k tail S.length+k
local notation "shape" => j+(j+rest)
local notation "E" => Fintype.card (Port P X.width)
local notation "Public" => Σ _:Fin (2^shape),Fin E
variable (width : S.groupWidth k tail 0 + k = j + (j + rest))


open DescentTerminalPacketHomeRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM

local notation "tracking" => publicSpine X G S b hp base width
local notation "origPin" => NativeBranch.rawPin S (X:=X) (radix:=radix) base width
local notation "originLayout" => fun _ : Fin E=>LinearEquiv.refl (ZMod 2) (Bits shape)
local notation "oldOwner" => fun u : Public=>host b.origin.source (origPin u)
local notation "newOwner" => fun u : Public=>host b.target (origPin u)
local notation "frozen_" => b.path.frozen


local notation "size₀" => E*2^frozen_
local notation "rows₀" => E*2^(j+rest)
local notation "rep" => fun a:Fin size₀=>origPin (representative tracking originLayout (finProdFinEquiv.symm a))

/- All claims about the initial ancestry tape refer to immutable original
incidence indices of X. No branch field or selected matrix enters these words. -/
open DescentTerminalFrozenRoster Computability.BorderVNP.FragmentBucket
local notation "H" => S.hostSize S.length
local notation "capBits" => 8+S.capGain*S.length
local notation "home₀" => cohortHome X G S b hp base
local notation "fr" => fun u : Fin size₀=>(finProdFinEquiv.symm u : Fin E×Fin (2^frozen_)).2
local notation "codes" => DescentTerminalFrozenRoster.book home₀ fr
local notation "finalWorld" => ((Epochs.finish G hu he r).state c).graph

attribute [local irreducible] DescentTerminalCohortArena.machine DescentTerminalCohortArena.shelf
  DescentTerminalCohortArena.order DescentTerminalCohortArena.indexBase DescentTerminalCohortArena.ticks
  DescentTerminalCohortArena.stop
set_option Elab.async false in
set_option maxHeartbeats 1000000 in
theorem frozen_roster {bw:ℕ} (hops : ℕ→Hop) (L : DescentTerminalPacketHomeRAM.Layout) (m : Memory bw)
    (ok : DescentTerminalPacketHomeRAM.Room L bw rows₀ size₀)
    (fit : ∀t<S.length,DescentExteriorReplay.Room bw size₀ (hops t))
    (seedRead : ∀a:Fin size₀,(hops 0).source.read m (a.val:Computability.VPVNP.BurstRAM.Word bw)=
      (seedAncestry X G S b a:Computability.VPVNP.BurstRAM.Word bw))
    (arrived : b.path.exteriorFields base radix hops m rep)
    (chain : ∀t<S.length,(hops t).dest=(hops (t+1)).source)
    (capacity : ∀t<S.length,size₀ ≤ (hops t).dest.size ∧ (hops t).dest.size<2^bw)
    (last : (hops S.length).source=L.frozen)
    (first : ℕ) (room : DescentTerminalCohortArena.stop first frozen_ capBits size₀ H<2^bw)
    (original : L.frozen.Fits bw first) (alive : 0<H)
    (payload : (frozen_+1)*2^capBits ≤ bw) :
    let bins_:=DescentTerminalCohortArena.shelf first frozen_ capBits size₀ H room
    let ord:=DescentTerminalCohortArena.order first frozen_ capBits size₀ H
    let rank:=DescentTerminalCohortArena.indexBase first frozen_ capBits size₀ H
    let act:=(steps bw size₀ (schedule hops S.length)).seq (DescentTerminalCohortArena.machine first frozen_ capBits size₀ H room L.frozen)
    let fee:=clocks size₀ (schedule hops S.length)+DescentTerminalCohortArena.ticks first frozen_ capBits size₀ H room L.frozen
    ∃o,act.Exec m o fee ∧ CheapCode act ∧
      (∀v:Fin H,(o (bins_.bins+v.val)).val=(codes v).val ∧ (o (ord.counts+v.val)).val=count home₀ v) ∧
      (∀v:(finalWorld).Site,∀pin:Attached finalWorld v,
        let at_:=cohort X G S b hp base pin.val
        o (rank+(dest home₀ at_).val)=(densePin X G S b hp base v pin:Computability.VPVNP.BurstRAM.Word bw) ∧
        DescentExterior.terminalPin initialBits retained frozen_ (matrixCode (pinSpine X G S b hp base).matrix).val
          (o (bins_.bins+(b.target.home v).val)).val pin.val.1.val=densePin X G S b hp base v pin) ∧
      ∀a<first,o a=stage hops size₀ m S.length a := by
  intro bins_ ord rank act fee
  let end_:=stage hops size₀ m S.length
  have spine:=stage_control hops S.length m fit
  have birth:=replayed_frozen X G S b hp base width hops L m ok seedRead arrived chain capacity last
  have keys (u : Fin size₀) : L.frozen.read end_ (u.val:Computability.VPVNP.BurstRAM.Word bw)=((home₀ u).val:Computability.VPVNP.BurstRAM.Word bw) := by
    have h:=u.isLt.trans_le ok.frozenRows
    simp only [Bank.read,Fin.val_cast_of_lt (h.trans ok.frozen.2.1),Nat.mod_eq_of_lt h]
    exact (birth u).trans (congrArg (fun v:Fin H=>(v.val:Computability.VPVNP.BurstRAM.Word bw)) (frozenHome_direct X G S b hp base width u))
  have bound:=cohort_cap X G S b hp base
  obtain ⟨o,ran,cheap,cards,slots,frame⟩ :=
    measured_cohort_rows first room L.frozen end_ alive original home₀ keys bound payload
  refine ⟨o,Procedure.Exec.then spine.1 ran,cheap_seq spine.2 cheap,cards,?_,frame⟩
  intro v pin at_
  refine ⟨?_,?_⟩
  · have belongs : home₀ at_=b.target.home v:=((attachedCohorts X G S b hp base v) pin).2
    change o (rank + (dest home₀ at_).val) = (prior home₀ at_.val (b.target.home v) : Computability.VPVNP.BurstRAM.Word bw)
    rw [← belongs]
    exact slots at_
  · have decoded : (o (bins_.bins + (b.target.home v).val)).val = (codes (b.target.home v)).val :=
      (cards (b.target.home v)).1
    rw [decoded]
    exact decode_published_pin X G S b hp base v pin

end Branch
end
end Hierarchy.DescentSixParty.SeedNamed
end OAI

-- Keep the named projections opaque while Lean indexes theorem signatures.
open OAI.Hierarchy.DescentSixParty.SeedNamed
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin
  Branch.cohortHome Branch.cohort Branch.atCohort Branch.densePin
