import OAI.Hierarchy.TaggedWireCoreSpillLayout
import OAI.Hierarchy.TaggedWireSettledMatrix
import OAI.Hierarchy.TaggedWireNativeOrder
import OAI.Hierarchy.ProtocolRAMRepairCommodity

namespace OAI
/-! # The mixed-radix input basis of the dated spill circuit

Within a shared chord, goods are numbered by the original paid inventory
address. The output uses the physical edge ordinal. A route can still visit a
given physical edge more than once; its occurrence rank uses the supplied
native chronological directory. -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph AdaptiveProbe WireTelescope
open ProtocolRAM.PurchaseInventory
open scoped Classical BigOperators
variable {F : Type*} [Field F] {S : PurchaseSampler} {h d k K edges r : ℕ}
    {π : Equiv.Perm (Fin (2^h))} {place : Site h d k→Fin K}
    (B : Mount (S:=S) π place edges) (inj : Function.Injective place) (pad : Chord K)

namespace SpillRows
variable {n : ℕ} {I : Type} [Fintype I]

structure Chart (K edges n : ℕ) (I : Type) where
  data : SettledMatrix.Layout K edges I Empty
  num : Fin n ≃ SettledMatrix.Source edges I Empty

namespace Chart
variable (A : Chart K edges n I)
abbrev edge := A.data.edge
def family := A.data.original ∘ A.num
def routes := A.data.steps ∘ A.num
def bits (spill : I→ℕ) := SettledMatrix.Layout.available (fun _:Fin edges=>0) spill (fun _:Empty=>0) (fun _=>0) ∘ A.num
omit [Fintype I] in
theorem paths (i : Fin n) : Traverses (rowGraph A.edge) (A.family i).val.1 (A.routes i) (A.family i).val.2 :=
  A.data.paths (A.num i)

theorem installed (spill : I→ℕ) : installedWidths A.family (A.bits spill)=A.data.goods.chordWidths spill := by
  change (∑i,SettledMatrix.Layout.available (fun _:Fin edges=>0) spill (fun _:Empty=>0) (fun _=>0) (A.num i) •
    unitChord (A.data.original (A.num i)))=_
  rw [A.num.sum_comp (fun x=>SettledMatrix.Layout.available (fun _:Fin edges=>0) spill (fun _:Empty=>0)
    (fun _=>0) x • unitChord (A.data.original x))]
  simp [SettledMatrix.Source,Fintype.sum_sum_type,SettledMatrix.Layout.available,SettledMatrix.Layout.original,
    PortGraph.chordWidths,fun i=>oriented_width A.data.goods i (A.data.goodsDistinct i) (spill i)]

theorem measured (spill : I→ℕ) (e : Fin edges) : routeLoad A.routes (A.bits spill) e=routeLoad A.data.core spill e := by
  change (∑i,(A.data.steps (A.num i)).count e*SettledMatrix.Layout.available (fun _:Fin edges=>0) spill
    (fun _:Empty=>0) (fun _=>0) (A.num i))=_
  rw [A.num.sum_comp (fun x=>(A.data.steps x).count e*SettledMatrix.Layout.available (fun _:Fin edges=>0) spill
    (fun _:Empty=>0) (fun _=>0) x)]
  simp [SettledMatrix.Source,Fintype.sum_sum_type,SettledMatrix.Layout.steps,SettledMatrix.Layout.available,routeLoad]

def nativeOrder (enum : Fin r≃RouteOccurrence A.data.core A.data.center) : Fin (edges+r)≃Σi,Fin (A.routes i).length :=
  finSumFinEquiv.symm.trans <| (Equiv.sumCongr (Equiv.refl _) enum).trans <|
    A.data.occurrences.trans (Equiv.sigmaCongrLeft (β:=fun x=>Fin (A.data.steps x).length) A.num).symm

omit [Fintype I] in
theorem native_edge (enum : Fin r≃RouteOccurrence A.data.core A.data.center) (j : Fin (edges+r)) :
    (A.routes (A.nativeOrder enum j).1).get (A.nativeOrder enum j).2=A.data.nativeEdge enum j := by
  let z:=(Equiv.sumCongr (Equiv.refl _) enum) (finSumFinEquiv.symm j)
  let e:=Equiv.sigmaCongrLeft (β:=fun i=>Fin (A.data.steps i).length) A.num
  exact (congrArg (fun t : Σi,Fin (A.data.steps i).length=>(A.data.steps t.1).get t.2)
    (e.apply_symm_apply (A.data.occurrences z))).trans (A.data.occurrence_edge z)

omit [Fintype I] in
theorem native_width (enum : Fin r≃RouteOccurrence A.data.core A.data.center) (spill : I→ℕ) (j : Fin (edges+r)) :
    A.bits spill (A.nativeOrder enum j).1=A.data.nativeWidth enum (fun _=>0) spill (fun _=>0) (fun _=>0) j := by
  let z:=(Equiv.sumCongr (Equiv.refl _) enum) (finSumFinEquiv.symm j)
  let e:=Equiv.sigmaCongrLeft (β:=fun i=>Fin (A.data.steps i).length) A.num
  let width:=SettledMatrix.Layout.available (fun _:Fin edges=>0) spill (fun _:Empty=>0) (fun _=>0)
  apply (congrArg (fun t : Σi,Fin (A.data.steps i).length=>width t.1) (e.apply_symm_apply (A.data.occurrences z))).trans
  change width (A.data.occurrences z).1=Sum.elim (fun _=>0) (RouteOccurrence.weight spill (fun _=>0) (fun _=>0)) z
  rcases z with i|⟨i,u⟩|⟨g,u⟩ <;>rfl

def operator (spill : I→ℕ) {m : ℕ} (ord : Fin m≃Σi,Fin (A.routes i).length) :=
  chordRouter (F:=F) A.family A.edge A.routes (A.bits spill) ord A.paths
end Chart

def chronological (h N k edges : ℕ) :
    Fin (edges+footprint h N k) ≃ SettledMatrix.Source edges (Commodity (Fin (2^h)) N k) Empty :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) ((slotEquiv h N k).symm.trans (Equiv.sumEmpty _ Empty).symm))

@[simp] theorem original_good (g : Commodity (Fin (2^h)) d k) :
    ((chronological h d k edges).symm (.inr (.inl g))).val=edges+slot g := rfl
@[simp] theorem original_paid (e : Fin edges) : ((chronological h d k edges).symm (.inl e)).val=e.val := rfl
end SpillRows

namespace Mount
def datedLayout : SpillRows.Chart K edges (edges+footprint h (Stages h d) k) (Commodity (Fin (2^h)) (Stages h d) k) :=
  ⟨B.spillLayout inj pad,SpillRows.chronological h (Stages h d) k edges⟩
end Mount
end Hierarchy.ProbeStage.CoreBoard
end

end OAI
