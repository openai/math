import OAI.ThreeFlat.Diagonal.PhysicalRecordFamily
import OAI.ThreeFlat.Diagonal.HistoryAssembly

namespace OAI
/-! # Native terminal wire-bit order and port transfer between equal forms -/

namespace ThreeFlat.Diagonal.PhysicalStage
open HistoryContraction
open scoped Classical
noncomputable section

def State.edgeBit {d l : ℕ} (A : State d l) (e : A.shape.Edge) (j : Fin (A.width e)) : Fin A.widthSum :=
  A.bitAddress (A.wireOrder e) (Fin.cast (congrArg A.width (A.wireOrder.symm_apply_apply e).symm) j)

theorem State.edgeBit_read {d l : ℕ} (A : State d l) (w : Fin A.widthSum→Bool) (e : A.shape.Edge) (j : Fin (A.width e)) :
    w (A.edgeBit e j)=((A.boundaryBits.symm w) e).val.testBit j.val := by
  obtain ⟨i,rfl⟩:=A.wireOrder.symm.surjective e
  have transport (a : Fin A.edgeCount) (same : a=i) :
      A.bitAddress a (j.cast (congrArg A.wireWidth same.symm))=A.bitAddress i j := by
    subst a
    rfl
  exact (congrArg w (transport _ (A.wireOrder.apply_symm_apply i))).trans (A.bitAddress_read w i j).symm

def transferWire {X Y : Shape} {Pins : Type} {p : ℕ} (e : X=Y) {U : Form X Pins} {V : Form Y Pins}
    (form : HEq U V) (src : ∀ u,Fin (U.width u)→Fin p) : ∀ v,Fin (V.width v)→Fin p := by
  subst Y
  have eqv:=eq_of_heq form
  subst V
  exact src

theorem transferWire_reads {X Y : Shape} {Pins : Type} {p : ℕ} (e : X=Y)
    (U : Form X Pins) (V : Form Y Pins) (form : HEq U V) (src : ∀ u,Fin (U.width u)→Fin p)
    (input : Fin p→Bool) (pin : Pins) (b : X.Boundary) (root : Y.Site)
    (read : ∀ z : X.Site, HEq z root → ∀ j, input (src z j)=U.read z pin (X.graph.atVertex b z) j) :
    ∀ j, input (transferWire e form src root j)=V.read root pin
      (Y.graph.atVertex (cast (congrArg Shape.Boundary e) b) root) j := by
  subst Y
  have eqv:=eq_of_heq form
  subst V
  exact read root HEq.rfl

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
