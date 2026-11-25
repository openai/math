import OAI.Hierarchy.FactorPinIntervals
import OAI.ThreeFlat.Diagonal.PhysicalTerminalSource
import OAI.ThreeFlat.Diagonal.PhysicalWordAssembly
import OAI.ThreeFlat.Diagonal.HistoryPackedSources

namespace OAI
/-! # Physical source addresses for a receiver's selected terminal trees

An external leg follows the actual ownership path to its seed address. An
incident boundary leg reads the corresponding bit of the common selector.
-/

noncomputable section
namespace Hierarchy.TraceReceiverWordSources
open ThreeFlat Diagonal Diagonal.HistoryContraction Diagonal.PhysicalStage
open FactorPinIntervals

variable {T F : Type} [Field F] {d l S N p : ℕ} {A : State d l}
    (R : Run F A) (h : R.plan.History) (J : R.Assembler (Fin S → Bool))
    (U : A.Words (Fin S → Bool)) (seed : Forest F U.ports.form)
    (P : Layout T S N p) (src : ∀ v, Fin (U.ext v) → Fin S)
set_option quotPrecheck false

local notation "X" => (R.terminalLayer h).state
local notation "K" => R.endWords h J.steps U
local notation "Z" => R.plan.assemble h (J U) seed

/-- All selected roots use the same bounded suffix containing the common
wire bits. Only the external occurrence slots depend on the factor schedule. -/
def wires (suffix : ℕ) (fits : suffix+(X).widthSum≤p) :
    ∀ v : (R.plan.finish h).Site, Fin ((Z).1.width v) → Fin p :=
  transferWire (R.terminalLayer_shape h) (R.endWords_form h J.steps U seed).symm
    (fun v => (K).ports.physicalSource (fun y j =>
      let a := R.extAncestor h J.steps U y j
      P.slot (src a.1 a.2))
      (fun e j => ⟨suffix+((X).edgeBit e j).val, by have := ((X).edgeBit e j).isLt; omega⟩) v)

/-- The form transport changes only the dependent type of the port.
The native ordinal and the wire itself remain the physical ones. -/
theorem transfer_at {A B : Shape} {Pins : Type} {p : ℕ} (shape : A=B)
    {U : Form A Pins} {V : Form B Pins} (form : HEq U V)
    (src : ∀ v,Fin (U.width v)→Fin p) (u : A.Site) (v : B.Site) (same : HEq u v)
    (i : Fin (U.width u)) (j : Fin (V.width v)) (ordinal : i.val=j.val) :
    transferWire shape form src v j=src u i := by
  subst B
  obtain rfl:=eq_of_heq form
  obtain rfl:=eq_of_heq same
  have eqi : i=j := Fin.ext ordinal
  subst j
  rfl

/-- The terminal map RAM addresses the same wire using its recovered state,
whereas the selected forest uses the transported terminal form. -/
theorem wires_at (suffix : ℕ) (fits : suffix+(X).widthSum≤p)
    (physical : (X).shape.Site) (root : (R.plan.finish h).Site) (same : HEq physical root)
    (i : Fin ((K).ports.form.width physical)) (j : Fin ((Z).1.width root)) (ordinal : i.val=j.val) :
    wires R h J U seed P src suffix fits root j=
      (K).ports.physicalSource (fun u k=>let a:=R.extAncestor h J.steps U u k; P.slot (src a.1 a.2))
        (fun e b=>⟨suffix+((X).edgeBit e b).val,by have:=((X).edgeBit e b).isLt;omega⟩) physical i :=
  transfer_at (R.terminalLayer_shape h) (R.endWords_form h J.steps U seed).symm _ physical root same i j ordinal

/-- The word-level address mapper discharges every pin equation of the
selected forest. Its data hypotheses concern only the original seed port,
the receiver payload slice and the decoded selector suffix. -/
theorem wires_read (ord : (R.plan.finish h).Site ≃ Fin N) (tick : T) (raw : Fin S → Bool)
    (tape : Fin p → Bool) (suffix : ℕ) (fits : suffix+(X).widthSum≤p)
    (boundary : Fin (X).widthSum → Bool)
    (seed_read : ∀ v j, U.pin v raw j=raw (src v j))
    (source_owner : ∀ v j, P.origin (src v j)=ord (R.plan.destination h v))
    (payload : ∀ i, P.tick i=tick → tape (P.slot i)=raw i)
    (decoded : ∀ i : Fin (X).widthSum, tape ⟨suffix+i.val,by have := i.isLt; omega⟩=boundary i)
    (root : (R.plan.finish h).Site) (member : ord root ∈ P.rows tick) :
    ∀ i, tape (wires R h J U seed P src suffix fits root i) =
      (Z).1.read root raw ((R.plan.finish h).graph.atVertex (R.terminalLabels h boundary) root) i := by
  apply transferWire_reads (R.terminalLayer_shape h) (K).ports.form (Z).1
    (R.endWords_form h J.steps U seed).symm _ tape raw ((X).boundaryBits.symm boundary) root
  intro z eqRoot
  apply (K).ports.physicalSource_read
  · intro j
    let a := R.extAncestor h J.steps U z j
    have dest : R.plan.destination h a.1=root :=
      eq_of_heq ((R.extAncestor_destination h J.steps U z j).trans eqRoot)
    have owns : P.origin (src a.1 a.2)=ord root := (source_owner a.1 a.2).trans (congrArg ord dest)
    have tickOf : P.tick (src a.1 a.2)=tick := (congrArg P.owner owns).trans ((P.owns (ord root) tick).mp member)
    exact (payload _ tickOf).trans ((seed_read a.1 a.2).symm.trans (R.extAncestor_read h J.steps U z j raw).symm)
  · intro a j
    exact (decoded ((X).edgeBit a.1.1 j)).trans ((X).edgeBit_read boundary a.1.1 j)

end Hierarchy.TraceReceiverWordSources

end
end OAI
