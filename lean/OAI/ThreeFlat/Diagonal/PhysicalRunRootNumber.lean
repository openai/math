import OAI.ThreeFlat.Diagonal.PhysicalArchiveJoin
import OAI.ThreeFlat.Diagonal.CompressorWordEncoding

namespace OAI
/-! # Physical terminal site order shared by the archive and the semantic schedule -/
namespace ThreeFlat.Diagonal.PhysicalStage.Run
open HistoryContraction
open scoped Classical
noncomputable section
variable {F : Type} [Field F]

def terminalOrdinal : {d l : ℕ} → {A : State d l} → (r : Run F A) → (h : r.plan.History) →
    r.readTerminal (fun X=>X.Site) h → ℕ
  | _,l,_,.done A,_,x =>
    (A.order (A.chart.symm x).1).val*2^l+(CompressorPacking.Native.tagOrdinal l (A.chart.symm x).2).val
  | _,_,_,.step R next,h,x=>(next h.1).terminalOrdinal (tailHistory R next h) x

def FinalNumbered {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O) : Prop :=
  ∀ v : r.readTerminal (fun X=>X.Site) h,((r.finalArchive h C O p).2 v).val=r.terminalOrdinal h v

private theorem numbered_cast {d l : ℕ} {A : State d l} (r : Run F A) {h h' : r.plan.History}
    (eqv : h=h') (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O) (n : r.FinalNumbered h C O p) :
    r.FinalNumbered h' C O (eqv ▸ p) := by cases eqv;exact n

theorem joined_finalNumbered {d l D L : ℕ} {A : State d l}
    (R : Move F A D L) (next : ∀j,Run F (R.next j)) (C : (Run.step R next).Charges) (O : A.ArchiveSites)
    (j : Fin R.rules.count) (h : (next j).plan.History) (row : R.ArchiveStep j O (C.1 j))
    (p : (next j).ArchivePath h (C.2 j) row.sites) (numbered : (next j).FinalNumbered h (C.2 j) row.sites p) :
    (Run.step R next).FinalNumbered (joinHistory R next j h) C O (joinArchivePath R next C O j h row p) :=
  numbered_cast (next j) (tailHistory_joinHistory R next j h).symm (C.2 j) row.sites p numbered

end
end ThreeFlat.Diagonal.PhysicalStage.Run

namespace ThreeFlat.Diagonal.PhysicalStage.Run
open HistoryContraction
open scoped Classical
noncomputable section
variable {F : Type} [Field F]

/-- Number the actual terminal layer's base and lane in their native product order. -/
private def terminalEnumeration : {d l : ℕ}→{A : State d l}→(r : Run F A)→(h : r.plan.History)→
    (n : ℕ) × {e : r.readTerminal (fun X=>X.Site) h ≃ Fin n //
      ∀ v,(e v).val=r.terminalOrdinal h v}
  | _, l, _, .done A, h =>
    let e := A.chart.symm.trans ((A.order.prodCongr (CompressorPacking.Native.tagOrdinal l)).trans finProdFinEquiv)
    ⟨_,e,fun v=>by
      change (finProdFinEquiv (A.order (A.chart.symm v).1,
        CompressorPacking.Native.tagOrdinal l (A.chart.symm v).2)).val=_
      simp [terminalOrdinal,finProdFinEquiv]; ac_rfl⟩
  | _, _, _, .step R next, h => terminalEnumeration (next h.1) (tailHistory R next h)

/-- Every history has its own canonical terminal numbering prior to any RAM execution. -/
def terminalOrderEquiv {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History) :
    (r.plan.finish h).Site ≃ Fin (Fintype.card (r.plan.finish h).Site) :=
  let raw:=r.terminalEnumeration h
  let head:=(r.finalSite h).symm.trans raw.2.1
  let size:=((Fintype.card_congr head).trans (Fintype.card_fin raw.1)).symm
  head.trans (finCongr size)

theorem terminalOrderEquiv_val {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (v : (r.plan.finish h).Site) :
    (r.terminalOrderEquiv h v).val=r.terminalOrdinal h ((r.finalSite h).symm v) :=
  (r.terminalEnumeration h).2.2 ((r.finalSite h).symm v)

end
end ThreeFlat.Diagonal.PhysicalStage.Run

end OAI
