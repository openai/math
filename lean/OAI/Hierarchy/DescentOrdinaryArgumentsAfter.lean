import OAI.Hierarchy.DescentOrdinaryArgumentsBefore
import OAI.Hierarchy.DescentOrdinaryFinalReads
import OAI.Hierarchy.DescentDatedOrdinaryNodeBanks

namespace OAI
/-! # Publish the ordinary completed operand state after the funded venue -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentOrdinaryFinal DescentDatedPriorOperand DescentSIMDLookup DescentOperandStateBanks
open DescentPackedColony DescentPackedOperand ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) {w : ℕ}
def finalChart : DescentOrdinaryFinal.Chart:=⟨v.resolver,v.metadata.chart.bits,v.metadata.chart.bits⟩
def nodeBankBase (floor : ℕ) :=v.nodeChart.inputsEnd (v.nodeChart.digitEnd (v.metaStart floor)
  (v.resolver.size+2)) v.metadata.paidBits (v.resolver.size+2)
def finalSources (floor : ℕ) : v.finalChart.Sources:=
  ⟨v.normalizedEnd floor,v.vectorOutput floor,v.nodeChart.bank (v.nodeBankBase floor)⟩

def afterEnd (floor : ℕ) :=v.finalChart.endAddress (v.metaEnd floor)
theorem after_end (floor : ℕ) (issued : v.operandBook=v.finalChart) : v.afterEnd floor=v.operandEnd floor:=by
  simp only [afterEnd,operandEnd,issued]

def argumentsAfter (floor : ℕ) (safe : v.finalChart.Early (v.finalSources floor) (v.metaEnd floor) w)
    (space : v.afterEnd floor<2^w) : NativePhase w:=
  let B:=v.finalChart
  let s:=v.finalSources floor
  let base:=v.metaEnd floor
  ⟨B.program s base w,B.ticks s base,B.image s base,(B.any s base (fun _=>0) safe space).2.1⟩

theorem argumentsAfter_any (floor : ℕ) (safe : v.finalChart.Early (v.finalSources floor) (v.metaEnd floor) w)
    (space : v.afterEnd floor<2^w) (m : Memory w) :
    (v.argumentsAfter floor safe space).Runs m ∧
    ∀a,a<v.metaEnd floor ∨ v.afterEnd floor≤a → (v.argumentsAfter floor safe space).image m a=m a:=
  ⟨(v.finalChart.any (v.finalSources floor) (v.metaEnd floor) m safe space).1,
   (v.finalChart.any (v.finalSources floor) (v.metaEnd floor) m safe space).2.2⟩

abbrev MetaWords := Fin 2→Fin v.resolver.blocks→Fin v.resolver.hosts→Fin v.resolver.groups→
  Cell (v.metadata.chart.bits*v.resolver.nodes)

def numericInputs («meta» : v.MetaWords) (old : Books v.resolver) (jobs : Fin v.resolver.jobs→DescentDatedPriorOperand.Source v.resolver) :
    v.finalChart.Values:=fun p x i h g=>
  let B:=v.finalChart
  let n:ℕ := (B.columns.symm i).elim
    (fun f=>if hit:f.val<2 then («meta» ⟨f.val,hit⟩ x h g).val else (old x p h g).val)
    (fun k=>(word ((jobs (v.resolver.index (x,B.slots.symm k))).compiled h g)).val)
  (n:ℕ)

theorem inputs_issued (floor : ℕ) (m : Memory w) («meta» : v.MetaWords) (old : Books v.resolver)
    (jobs : Fin v.resolver.jobs→DescentDatedPriorOperand.Source v.resolver)
    (newRead : ∀f x,Reads (v.nodeChart.bank (v.nodeBankBase floor) f x) («meta» f x) v.resolver.lanes m)
    (spanRead : ∀x p,Reads (previousBank v.resolver (v.vectorOutput floor) x p) (old x p) v.resolver.lanes m)
    (keyRead : ∀j,Reads (Banks.wordBank v.resolver (v.normalizedEnd floor) j) (fun h g=>word ((jobs j).compiled h g)) v.resolver.lanes m) :
    ∀p x i,Reads (v.finalChart.sourceBank (v.finalSources floor) p x i) ((v.numericInputs «meta» old jobs) p x i) v.resolver.lanes m:=by
  intro p x i
  let width (col : Fin 3 ⊕ Fin v.finalChart.keys) :=
    v.finalChart.widths (col.elim (fun j => j.castLE (by decide)) (fun _ => 3))
  let bank (col : Fin 3 ⊕ Fin v.finalChart.keys) : Bank := col.elim
    (fun f => if h : f.val < 2 then v.nodeChart.bank (v.nodeBankBase floor) ⟨f.val,h⟩ x
      else previousBank v.resolver (v.vectorOutput floor) x p)
    (fun k => Banks.wordBank v.resolver (v.normalizedEnd floor) (v.resolver.index (x,v.finalChart.slots.symm k)))
  let value (col : Fin 3 ⊕ Fin v.finalChart.keys) (h : Fin v.resolver.hosts) (g : Fin v.resolver.groups) : Cell (width col) :=
    (col.elim (fun f => if hit : f.val < 2 then («meta» ⟨f.val,hit⟩ x h g).val else (old x p h g).val)
      (fun k => (word ((jobs (v.resolver.index (x,v.finalChart.slots.symm k))).compiled h g)).val) : ℕ)
  suffices read : ∀ col, Reads (bank col) (value col) v.resolver.lanes m from read (v.finalChart.columns.symm i)
  have castRead {bits : ℕ} (b : Bank) (t : Fin v.resolver.hosts → Fin v.resolver.groups → Cell bits)
      (held : Reads b t v.resolver.lanes m) :
      Reads b (fun h g => ((t h g).val : Cell bits)) v.resolver.lanes m := by
    simpa only [Fin.cast_val_eq_self] using held
  intro col
  cases col with
  | inl f =>
    fin_cases f
    · exact castRead _ _ (newRead 0 x)
    · exact castRead _ _ (newRead 1 x)
    · exact castRead _ _ (spanRead x p)
  | inr j => exact castRead _ _ (keyRead (v.resolver.index (x,v.finalChart.slots.symm j)))

theorem argumentsAfter_issued (floor : ℕ) (safe : v.finalChart.Early (v.finalSources floor) (v.metaEnd floor) w)
    (space : v.afterEnd floor<2^w) (m : Memory w) («meta» : v.MetaWords) (old : Books v.resolver)
    (jobs : Fin v.resolver.jobs→DescentDatedPriorOperand.Source v.resolver)
    (newRead : ∀f x,Reads (v.nodeChart.bank (v.nodeBankBase floor) f x) («meta» f x) v.resolver.lanes m)
    (spanRead : ∀x p,Reads (previousBank v.resolver (v.vectorOutput floor) x p) (old x p) v.resolver.lanes m)
    (keyRead : ∀j,Reads (Banks.wordBank v.resolver (v.normalizedEnd floor) j) (fun h g=>word ((jobs j).compiled h g)) v.resolver.lanes m)
    (x : Fin v.resolver.blocks) (p : Pages v.resolver.operands) :
    Reads (previousBank v.resolver (v.finalChart.out (v.metaEnd floor)) x p)
      (fun h g=>v.finalChart.law p (v.finalChart.dataAt (v.numericInputs «meta» old jobs) p x h g))
      v.resolver.lanes ((v.argumentsAfter floor safe space).image m):=
  v.finalChart.issued (v.finalSources floor) (v.metaEnd floor) m safe space (v.numericInputs «meta» old jobs)
    (v.inputs_issued floor m «meta» old jobs newRead spanRead keyRead) x p
end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
