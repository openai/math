import OAI.Hierarchy.DescentPaidSweepFields

namespace OAI
/-! # Native all-label paid-row sweep with one fixed mask book and one funded sum book -/
namespace Hierarchy.DescentPaidResidentCount.Sweep
open DescentSIMDLookup DescentPackedZip DescentPackedActorMask DescentOrdinaryAtomFieldRAM.ROM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {p n w : ℕ} (base D cap b H G M : ℕ) (labels : Fin p→ Cell n) (ids counts : Expr)
local notation "N₀" => actors D cap
local notation "r₀" => rowCount H G M
local notation "start₂" => sumBase base p D cap n M
local notation "dst" => paidBank base p D cap b n H G M
local notation "pages₁" => maskPages labels N₀ M
local notation "pages₂" => sumPages D cap b M
local notation "b₁" => maskBits D cap n M
local notation "b₂" => sumBits D cap b M
local notation "fields" => List.ofFn (job base D cap b M labels ids counts)
local notation "jobs" => ProbeStage.Native.columns r₀ (dst).base fields

def paidCode (w : ℕ) :=
  ((mount pages₁ b₁ w base).seq (mount pages₂ b₂ w start₂)).seq (ProtocolRAM.program w jobs)

def paidClock := ((4+10*((p*2)*2^b₁))+(4+10*(2*2^b₂)))+clock jobs

def paidAfter (m : Memory w) := result jobs (after pages₂ b₂ start₂ (after pages₁ b₁ base m))

local notation "mt₀" => maskTable labels N₀ M base
local notation "st₀" => sumTable D cap b M start₂

theorem paid_fits (srcFit : ids.Fits w base) (cntFit : counts.Fits w base)
    (dstBelow : (dst).base<2^w) :
    (∀j : Fin p, Fits ((mt₀) j) ids (.lit 0) (n*N₀) 0 M start₂ w) ∧
    (∀j : Fin p, Fits ((mt₀) j) ids (.lit 0) (n*N₀) 0 M (dst).base w) ∧
    ∀j : Fin p, Fits st₀ (((mt₀) j).read ids (.lit 0)) counts (1*N₀) (b*D) M (dst).base w :=by
  let mt:=mt₀
  let st:=st₀
  have before : base≤ start₂ :=Nat.le_add_right _ _
  have sep : start₂≤(dst).base :=Nat.le_add_right _ _
  have mf (j : Fin p) : Fits (mt j) ids (.lit 0) (n*N₀) 0 M start₂ w :=
    ⟨ProtocolRAMGeneratedWrite.fits_mono _ before srcFit,trivial,
      bank_room pages₁ b₁ base start₂ _ (mask_width labels N₀ M _) le_rfl (sep.trans_lt dstBelow),
      bank_room pages₁ b₁ base start₂ _ (mask_width labels N₀ M _) le_rfl (sep.trans_lt dstBelow),
      congrArg Page.bits (mask_page labels N₀ M j 0),congrArg Page.bits (mask_page labels N₀ M j 1)⟩
  have mf' (j : Fin p) : Fits (mt j) ids (.lit 0) (n*N₀) 0 M (dst).base w := by
    obtain ⟨a,c,e,f,g,k⟩:=mf j
    exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ sep a,c,⟨e.1,e.2.1,e.2.2.trans sep⟩,
      ⟨f.1,f.2.1,f.2.2.trans sep⟩,g,k⟩
  have sf (j : Fin p) : Fits st ((mt j).read ids (.lit 0)) counts (1*N₀) (b*D) M (dst).base w :=
    ⟨⟨(mf' j).apply,(mf' j).right,(mf' j).shift,(mf' j).left⟩,
      ProtocolRAMGeneratedWrite.fits_mono _ (before.trans sep) cntFit,
      bank_room pages₂ b₂ start₂ (dst).base 0 (sum_width D cap b M 0) le_rfl dstBelow,
      bank_room pages₂ b₂ start₂ (dst).base 1 (sum_width D cap b M 1) le_rfl dstBelow,rfl,rfl⟩
  exact ⟨mf,mf',sf⟩

theorem paid_run (m : Memory w) (srcFit : ids.Fits w base) (cntFit : counts.Fits w base)
    (address : Fin H→Fin G→Fin N₀→ Cell n) (charge : Fin H→Fin G→Fin D→ Cell b)
    (idsRead : Source ids (fun h g=>encode n N₀ (address h g)) M m)
    (countsRead : Source counts (fun h g=>encode b D (charge h g)) M m)
    (space : (dst).base+p*r₀<2^w) :
    (paidCode base D cap b H G M labels ids counts w).Exec m (paidAfter base D cap b H G M labels ids counts m)
      (paidClock base D cap b H G M labels ids counts) ∧
    (∀(j : Fin p) (a : Row H G M),paidAfter base D cap b H G M labels ids counts m
      ((dst).base+j.val*r₀+(row H G M a).val)=((data (fun h g=>counted D cap b
        (target n N₀ (labels j) (encode n N₀ (address h g))) (encode b D (charge h g))) a).val:Word w)) ∧
    (∀a,a<base ∨ (dst).base+p*r₀≤a→paidAfter base D cap b H G M labels ids counts m a=m a) ∧
    CheapCode (paidCode base D cap b H G M labels ids counts w) := by
  let m₁:=after pages₁ b₁ base m
  let m₂:=after pages₂ b₂ start₂ m₁
  have before : base≤ start₂ := Nat.le_add_right _ _
  have sep : start₂≤(dst).base := Nat.le_add_right _ _
  have dstBelow : (dst).base<2^w := (Nat.le_add_right ..).trans_lt space
  have step₁:=DescentOrdinaryAtomFieldRAM.ROM.run pages₁ b₁ base m (sep.trans_lt dstBelow)
  have step₂:=DescentOrdinaryAtomFieldRAM.ROM.run pages₂ b₂ start₂ m₁ dstBelow
  have low₁:=DescentOrdinaryAtomFieldRAM.ROM.frame pages₁ b₁ base m
  have low₂:=DescentOrdinaryAtomFieldRAM.ROM.frame pages₂ b₂ start₂ m₁
  have hold (q) (hq : q<base) : m₂ q=m q :=
    (low₂ q (.inl (hq.trans_le before))).trans (low₁ q (.inl hq))
  have src : Source ids (fun h g=>encode n N₀ (address h g)) M m₂ := fun z=>
    (eval_below ids _ m m₂ srcFit hold).trans (idsRead z)
  have cnt : Source counts (fun h g=>encode b D (charge h g)) M m₂ := fun z=>
    (eval_below counts _ m m₂ cntFit hold).trans (countsRead z)
  let mt:=maskTable labels N₀ M base
  let st:=sumTable D cap b M start₂
  obtain ⟨mf,mf',sf⟩:=paid_fits base D cap b H G M labels ids counts srcFit cntFit dstBelow
  have mfWord (j : Fin p) : Static (mt j) (select N₀ (labels j)) M m₂ :=
    table_kept (mf j) (binary_mounted (select N₀ (labels j)) M pages₁ b₁ base m
      (mask_width labels N₀ M) (Presence.pair j) (mask_page labels N₀ M j)) (fun q hq=>low₂ q (.inl hq))
  have sfWord : Static st (counted D cap b) M m₂ :=
    binary_mounted (counted D cap b) M pages₂ b₂ start₂ m₁ (sum_width D cap b M) id (fun j=>rfl)
  have len : (fields).length=p:=List.length_ofFn
  have fits : ∀e∈fields,e.Fits w (dst).base := by
    intro e he
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp he
    exact ⟨(sf j).apply,(sf j).right,(sf j).shift,(sf j).left⟩
  have native : (ProtocolRAM.program w jobs).Exec m₂ (result jobs m₂) (clock jobs):=
    @ProbeStage.Native.columns_exec w r₀ (dst).base fields m₂
      (ProbeStage.Native.columns_safe fields le_rfl fits (by simpa only [len] using space))
  refine ⟨?_,?_,?_,?_⟩
  · exact Procedure.Exec.then (Procedure.Exec.then step₁.1 step₂.1) native
  · intro j a
    refine (ProbeStage.Native.columns_read fields m₂ le_rfl fits j.val (j.isLt.trans_eq len.symm)
      (row H G M a)).trans ?_
    have picks := read_data (mt j) ids (.lit 0) (dst).base (mf' j) (select N₀ (labels j))
      (select_empty N₀ (labels j)) m₂ (mfWord j) _ (fun _ _=>(0:Cell 0)) src (clear_source m₂)
    simpa only [List.getElem_ofFn,Fin.eta,job,mt,st,select] using read_data st ((mt j).read ids (.lit 0)) counts (dst).base (sf j)
      (counted D cap b) (empty ..) m₂ sfWord _ _ picks cnt a
  · intro q away
    have upper : (dst).base≤(dst).base+p*r₀ :=Nat.le_add_right _ _
    exact (ProbeStage.Native.columns_frame fields m₂ (by simpa only [len] using away.imp_left (fun h=>h.trans_le (before.trans sep)))).trans
      ((low₂ q (away.imp (fun h=>h.trans_le before) (fun h=>upper.trans h))).trans
        (low₁ q (away.imp_right (fun h=>sep.trans (upper.trans h)))))
  · intro P R K pc reg pub exit i
    exact cheap_seq (cheap_seq (DescentOrdinaryAtomFieldRAM.ROM.cheap pages₁ b₁ w base)
      (DescentOrdinaryAtomFieldRAM.ROM.cheap pages₂ b₂ w start₂)) (@ProtocolRAM.program_cheap _ _) pc reg pub exit i

end
end Hierarchy.DescentPaidResidentCount.Sweep

end OAI
