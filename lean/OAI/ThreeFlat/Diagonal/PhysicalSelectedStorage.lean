import OAI.ThreeFlat.Diagonal.PhysicalIndividualCharge
import OAI.ThreeFlat.RAM.HistoryStageTariff

namespace OAI
/-! # Storage bounds for the assembled terminal rows -/

noncomputable section
namespace ThreeFlat.Diagonal.PhysicalStage.Block
open RAM.HistoryStageBody HistoryContraction
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] (B : Block F)

/-- The true selected root fits each S12 slab. Its native row stream is
charged by its typed tree, and its pins consist of surviving endpoints and
the incidence words of the same final geometric site. -/
theorem terminal_storage_at_charge {u k rem pins ext rowRate unitWork : ℕ}
    (A : State (2^B.exponent 0) ((B.repeat k).charge+rem))
    (h : ((B.repeat k).run rem A).plan.History) (start pairs : A.Site→ℕ)
    (seed : ∀ x,1+A.incidentWidth x+pairs x ≤ start x) (site : (((B.repeat k).run rem A).plan.finish h).Site)
    (net : BitNetwork F pins) (age : 2≤u) (positive : 1≤unitWork) (rate : rowRate≤unitWork)
    (rows : net.cells≤rowRate*((B.repeat k).run rem A).chargeAt h (B.charges k rem A) start site)
    (surviving : ext≤2*∑ x : {x // ((B.repeat k).run rem A).plan.destination h x=site},pairs x.val)
    (arity : pins=ext+((B.repeat k).run rem A).terminalIncident h site)
    (peak : ((B.repeat k).run rem A).chargeAt h (B.charges k rem A) start site*unitWork≤2^((3*u^10+4)/5)) :
    4*net.cells≤2^(u^10) ∧ ext≤2^(u^10) ∧ pins≤2^(u^10) := by
  let charge:=((B.repeat k).run rem A).chargeAt h (B.charges k rem A) start site
  have bounded : unitWork*charge≤2^((3*u^10+4)/5):=by rwa [Nat.mul_comm]
  have q : charge≤2^((3*u^10+4)/5):=by
    have scale:=Nat.mul_le_mul_right charge positive
    simpa only [Nat.one_mul] using scale.trans bounded
  have stream:=rows.trans ((Nat.mul_le_mul_right charge rate).trans bounded)
  have floor:=B.terminal_charge_covers k rem A h start pairs seed site
  change 1+((B.repeat k).run rem A).terminalIncident h site+_≤charge at floor
  have space:=StageRun.site_peak_slab age
  omega

/-- For the actual paper run the schedule already proves the required
pointwise peak for every root. There is no memory-cap premise on that root. -/
theorem cursor_terminal_storage {u rem low off slots e unitWork pins ext rowRate : ℕ}
    (age : 40≤u) (exp : e≤u) (half : low≤u^10/2) (growth : B.peakBase≤u)
    (slotCap : off*slots*3≤u^e) (hk : 2≤(B.repeat (u^8)).charge+rem)
    (h : ((B.repeat (u^8)).run rem (B.cursorState hk low off slots)).plan.History)
    (start pairs : (B.cursorState hk low off slots).Site→ℕ) (seedHigh : ∀ x,start x≤2^low*u^e)
    (seedLow : ∀ x,1+(B.cursorState hk low off slots).incidentWidth x+pairs x ≤ start x) (tariff : unitWork≤u^e)
    (site : (((B.repeat (u^8)).run rem (B.cursorState hk low off slots)).plan.finish h).Site)
    (net : BitNetwork F pins) (positive : 1≤unitWork) (rate : rowRate≤unitWork)
    (rows : let A:=B.cursorState hk low off slots;let r:=(B.repeat (u^8)).run rem A
      net.cells≤rowRate*r.chargeAt h (B.charges (u^8) rem A) start site)
    (surviving : let r:=(B.repeat (u^8)).run rem (B.cursorState hk low off slots)
      ext≤2*∑ x : {x // r.plan.destination h x=site},pairs x.val)
    (arity : pins=ext+((B.repeat (u^8)).run rem (B.cursorState hk low off slots)).terminalIncident h site) :
    4*net.cells≤2^(u^10) ∧ ext≤2^(u^10) ∧ pins≤2^(u^10) :=
  B.terminal_storage_at_charge (B.cursorState hk low off slots) h start pairs seedLow site net (by omega) positive
    rate rows surviving arity (B.cursor_terminal_peak age exp half growth slotCap hk h start seedHigh tariff site)

end

end ThreeFlat.Diagonal.PhysicalStage.Block

namespace ThreeFlat.Diagonal.PhysicalStage.Block
open HistoryContraction RAM
open scoped BigOperators Classical
noncomputable section
variable {F Pins : Type} [Field F] [Fintype F] (B : Block F) {u rem low off slots e unitWork rowRate : ℕ}
variable (hk : 2≤(B.repeat (u^8)).charge+rem)
local notation "A" => B.cursorState hk low off slots
set_option quotPrecheck false in
local notation "R" => (B.repeat (u^8)).run rem A

omit [Fintype F] in
/-- The selected root's real compiled cells, external prefix and full pin arity fit
in their S12 slabs, using its chronological charge and the original cursor rows. -/
theorem cursor_assembled_storage (age : 40≤u) (exp : e≤u) (half : low≤u^10/2)
    (growth : B.peakBase≤u) (slotCap : off*slots*3≤u^e)
    (h : (R).plan.History) (J : Run.WordSteps Pins R) (L : (A).Words Pins)
    (ord : (A).OrderedHalves L) (N : Forest F L.ports.form)
    (start pairs : (A).Site→ℕ) (seedHigh : ∀ x,start x≤2^low*u^e)
    (seedLow : ∀ x,1+(A).incidentWidth x+pairs x ≤ start x) (endpoints : ∀ x,L.ext x=2*pairs x)
    (site : ((R).plan.finish h).Site) (tariff : unitWork≤u^e) (positive : 1≤unitWork)
    (rate : rowRate≤unitWork)
    (rows : (((R).plan.assemble h ((R).wordAssembly J L) N).2 site).compile.cells≤
      rowRate*(R).chargeAt h (B.charges (u^8) rem A) start site) :
    let z:=cast (congrArg Shape.Site ((R).terminalLayer_shape h)).symm site
    let res:=(R).plan.assemble h ((R).wordAssembly J L) N
    4*(res.2 site).compile.cells≤2^(u^10) ∧ ((R).endWords h J L).ext z≤2^(u^10) ∧ res.1.width site≤2^(u^10) := by
  apply B.cursor_terminal_storage age exp half growth slotCap hk h start pairs seedHigh seedLow tariff site
    (((R).plan.assemble h ((R).wordAssembly J L) N).2 site).compile positive rate rows
  · let fiber := {x // (R).plan.destination h x = site}
    have twice : (∑ x : fiber, L.ext x.val) = ∑ x : fiber, 2 * pairs x.val :=
      Finset.sum_congr rfl (fun x _ => endpoints x.val)
    exact le_of_eq (((R).terminal_ext_sum h J L site).trans
      (twice.trans (Finset.mul_sum Finset.univ (fun x : fiber => pairs x.val) 2).symm))
  · exact (R).terminal_width_exact h J L ord N site

end

end ThreeFlat.Diagonal.PhysicalStage.Block

end

end OAI
