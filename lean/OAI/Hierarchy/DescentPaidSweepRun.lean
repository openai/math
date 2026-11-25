import OAI.Hierarchy.DescentPaidSweep

namespace OAI
/-! # Both native all-label sweeps, including complete low and high memory frames -/
namespace Hierarchy.DescentPaidResidentCount.Sweep
open DescentSIMDLookup DescentPackedZip DescentPackedActorMask DescentOrdinaryAtomFieldRAM.ROM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {p n w : ℕ} (base D cap b H G M : ℕ) (labels : Fin p→ Cell n) (ids counts : Expr)
local notation "N₀" => actors D cap
local notation "r₀" => rowCount H G M
local notation "marks" => Presence.directory labels N₀ M
local notation "bits₀" => maskBits D cap n M
local notation "paid₀" => paidBank base p D cap b n H G M
local notation "markBase" => actorBase base p D cap b n H G M
local notation "seen₀" => aliveBank base p D cap b n H G M
local notation "limit₀" => roof base p D cap b n H G M
local notation "ops₁" => List.ofFn (job base D cap b M labels ids counts)
local notation "tasks₁" => ProbeStage.Native.columns r₀ (paid₀).base ops₁
local notation "ops₂" => List.ofFn (Presence.expr labels N₀ M markBase ids)
local notation "tasks₂" => ProbeStage.Native.columns r₀ (seen₀).base ops₂
local notation "step₁" => paidCode base D cap b H G M labels ids counts
local notation "mid" => @paidAfter p n w base D cap b H G M labels ids counts

def program (w : ℕ) :=
  (step₁ w).seq ((mount marks bits₀ w markBase).seq (ProtocolRAM.program w tasks₂))
def ticks :=
  paidClock base D cap b H G M labels ids counts+((4+10*((p*2)*2^bits₀))+clock tasks₂)
def image (m : Memory w) := result tasks₂ (after marks bits₀ markBase (mid m))

local notation "prog" => program base D cap b H G M labels ids counts w
local notation "cost" => ticks base D cap b H G M labels ids counts
local notation "done" => image base D cap b H G M labels ids counts

theorem any (m : Memory w) (srcFit : ids.Fits w base) (cntFit : counts.Fits w base)
    (space : limit₀<2^w) :
    (prog).Exec m (done m) cost ∧
    (∀q,q<base ∨ limit₀≤q→ done m q=m q) ∧ CheapCode prog := by
  let M₁:=maskPages labels N₀ M
  let M₂:=sumPages D cap b M
  let b₂:=sumBits D cap b M
  let split:=sumBase base p D cap n M
  let one:=after M₁ bits₀ base m
  let two:=after M₂ b₂ split one
  let three:=after marks bits₀ markBase (mid m)
  have geo:=geometry base p D cap b n H G M
  have endPaid : (paid₀).base≤ markBase := (Nat.le_add_right ..).trans geo.2.2.1
  have endSeen : (seen₀).base≤limit₀ := Nat.le_add_right _ _
  have orders : base≤(paid₀).base := geo.1.trans geo.2.1
  have marked : markBase≤(seen₀).base := geo.2.2.2.1
  have afterMark : markBase≤limit₀ := marked.trans endSeen
  have afterPaid : (paid₀).base≤limit₀ :=endPaid.trans afterMark
  have oldFits:=paid_fits base D cap b H G M labels ids counts srcFit cntFit (afterPaid.trans_lt space)
  have oneExec:=DescentOrdinaryAtomFieldRAM.ROM.run M₁ bits₀ base m (geo.2.1.trans_lt (afterPaid.trans_lt space))
  have twoExec:=DescentOrdinaryAtomFieldRAM.ROM.run M₂ b₂ split one (afterPaid.trans_lt space)
  have threeExec:=DescentOrdinaryAtomFieldRAM.ROM.run marks bits₀ markBase (mid m) (endSeen.trans_lt space)
  have len₁ : (ops₁).length=p:=List.length_ofFn
  have len₂ : (ops₂).length=p:=List.length_ofFn
  have fits₁ : ∀e∈ops₁,e.Fits w (paid₀).base :=by
    intro e here;obtain ⟨j,rfl⟩:=List.mem_ofFn.mp here
    let f:=oldFits.2.2 j;exact ⟨f.apply,f.right,f.shift,f.left⟩
  have fits₂ : ∀e∈ops₂,e.Fits w (seen₀).base :=by
    intro e here;obtain ⟨j,rfl⟩:=List.mem_ofFn.mp here
    have widthRoom (t : Fin (p*2)) : (marks t).bits≤bits₀ :=by
      obtain ⟨⟨i,v⟩,rfl⟩:=finProdFinEquiv.surjective t
      fin_cases v <;> simp [Presence.directory,binary,maskBits]
    have widthFit (v : Fin 2) :=bank_room marks bits₀ markBase (seen₀).base
      (Presence.pair j v) (widthRoom _) le_rfl (endSeen.trans_lt space)
    exact ⟨widthFit 1,trivial,widthFit 0,ProtocolRAMGeneratedWrite.fits_mono _ ((orders.trans endPaid).trans marked) srcFit⟩
  have s₁ : (ProtocolRAM.program w tasks₁).Exec two (result tasks₁ two) (clock tasks₁):=
    @ProbeStage.Native.columns_exec w r₀ (paid₀).base ops₁ two (ProbeStage.Native.columns_safe ops₁ le_rfl fits₁
    (by simpa only [len₁] using geo.2.2.1.trans_lt (afterMark.trans_lt space)))
  have s₂ : (ProtocolRAM.program w tasks₂).Exec three (result tasks₂ three) (clock tasks₂):=
    @ProbeStage.Native.columns_exec w r₀ (seen₀).base ops₂ three (ProbeStage.Native.columns_safe ops₂ le_rfl fits₂
    (by simpa only [len₂] using geo.2.2.2.2.trans_lt space))
  refine ⟨?_,?_,?_⟩
  · exact Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then oneExec.1 twoExec.1) s₁) (Procedure.Exec.then threeExec.1 s₂)
  · intro q away
    have oldPaid:=away.imp (fun h=>h.trans_le orders) (fun h=>geo.2.2.1.trans (afterMark.trans h))
    have oldSeen:=away.imp (fun h=>h.trans_le ((orders.trans endPaid).trans marked)) (fun h=>geo.2.2.2.2.trans h)
    have f₁:=DescentOrdinaryAtomFieldRAM.ROM.frame M₁ bits₀ base m q (away.imp_right (fun h=>geo.2.1.trans (afterPaid.trans h)))
    have f₂:=DescentOrdinaryAtomFieldRAM.ROM.frame M₂ b₂ split one q (away.imp (fun h=>h.trans_le geo.1) (fun h=>afterPaid.trans h))
    have f₃:=DescentOrdinaryAtomFieldRAM.ROM.frame marks bits₀ markBase (mid m) q
      (away.imp (fun h=>h.trans_le (orders.trans endPaid)) (fun h=>endSeen.trans h))
    exact (ProbeStage.Native.columns_frame ops₂ three (by simpa only [len₂] using oldSeen)).trans
      (f₃.trans ((ProbeStage.Native.columns_frame ops₁ two (by simpa only [len₁] using oldPaid)).trans (f₂.trans f₁)))
  · intro P R K pc reg pub exit i
    exact cheap_seq (cheap_seq (cheap_seq (DescentOrdinaryAtomFieldRAM.ROM.cheap M₁ bits₀ w base)
      (DescentOrdinaryAtomFieldRAM.ROM.cheap M₂ b₂ w split)) (@ProtocolRAM.program_cheap _ _))
      (cheap_seq (DescentOrdinaryAtomFieldRAM.ROM.cheap marks bits₀ w markBase) (@ProtocolRAM.program_cheap _ _)) pc reg pub exit i

theorem issued (m : Memory w) (srcFit : ids.Fits w base) (cntFit : counts.Fits w base)
    (address : Fin H→Fin G→Fin N₀→ Cell n) (charge : Fin H→Fin G→Fin D→ Cell b)
    (idsRead : Source ids (fun h g=>encode n N₀ (address h g)) M m)
    (countsRead : Source counts (fun h g=>encode b D (charge h g)) M m)
    (live : ∀j,labels j≠0) (space : limit₀<2^w) :
    (∀(j : Fin p) (a : Row H G M),done m ((paid₀).base+j.val*r₀+(row H G M a).val)=
      ((data (fun h g=>counted D cap b (target n N₀ (labels j) (encode n N₀ (address h g)))
        (encode b D (charge h g))) a).val:Word w)) ∧
    ∀(j : Fin p) (a : Row H G M),done m ((seen₀).base+j.val*r₀+(row H G M a).val)=
      ((data (fun h g=>if ∃t,address h g t=labels j then (1:Cell 1) else 0) a).val:Word w) :=by
  have geo:=geometry base p D cap b n H G M
  have afterSeen : (seen₀).base≤limit₀:=Nat.le_add_right _ _
  have afterMark:=geo.2.2.2.1.trans afterSeen
  have afterBase:=geo.1.trans (geo.2.1.trans ((Nat.le_add_right ..).trans geo.2.2.1))
  have one:=paid_run base D cap b H G M labels ids counts m srcFit cntFit address charge idsRead countsRead
    (geo.2.2.1.trans_lt (afterMark.trans_lt space))
  have kept : Source ids (fun h g=>encode n N₀ (address h g)) M (mid m) :=fun s=>
    (eval_below ids _ m (mid m) srcFit (fun q h=>one.2.2.1 _ (.inl h))).trans (idsRead s)
  have two:=Presence.original labels address ids (mid m) markBase (seen₀).base live
    (ProtocolRAMGeneratedWrite.fits_mono _ afterBase srcFit) kept le_rfl (geo.2.2.2.2.trans_lt space)
  refine ⟨?_,two.2.1⟩
  intro j a
  have inside : j.val*r₀+(row H G M a).val<p*r₀ :=by
    have at_ := (row H G M a).isLt
    change (row H G M a).val<r₀ at at_
    have right:=Nat.mul_le_mul_right r₀ j.isLt
    rw [Nat.succ_mul] at right
    omega
  have low : (paid₀).base+j.val*r₀+(row H G M a).val< markBase :=by
    rw [Nat.add_assoc]
    exact (Nat.add_lt_add_left inside _).trans_le geo.2.2.1
  exact (two.2.2.1 _ (.inl low)).trans (one.2.1 j a)

end
end Hierarchy.DescentPaidResidentCount.Sweep

end OAI
