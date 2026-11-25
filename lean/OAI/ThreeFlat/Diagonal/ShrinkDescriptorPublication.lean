import OAI.ThreeFlat.Diagonal.ShrinkDescriptorReadback

namespace OAI
/-! # Word equations for the six persistent shrinking-stage site tables -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.DescriptorSpan

open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.DescriptorScan RAM.HeaderScan RAM.PhysicalPinsExpr NavigationDirectory
open scoped Fin.NatCast
variable {w : ℕ} (S : Graph.Stage) (K : ℕ) (c : Cursor) (x : Dimensions) (layout : Bool)
set_option quotPrecheck false
local notation "f" => fields K c x layout
local notation "p" => Resident.pointers K c x
local notation "extra" => ((p).costs+2*(x.motifs+1))
local notation "tail" => (allocate K c (.shrink x)).next.heap

private theorem descriptors_consecutive (kind : ℕ) :
    Consecutive (fields K c x layout) (NodeRecipe.descriptors S K kind) extra tail := by
  refine ⟨f 42,⟨f 36,?_,f 38,?_,f 40,?_,?_⟩,f 44,?_,?_⟩ <;>
    simp [Consecutive,NodeRecipe.kernelBase,NodeRecipe.incidentBase,NodeRecipe.halfBase,NodeRecipe.rowsBase,
      NodeRecipe.childrenBase,NodeRecipe.ownerBase,fields,Resident.pointers,allocate,headerWord,headerExtra,extraEnd]

variable (cur : Word w) (kind : ℕ) (old final : Memory w)

/-- The entire indexed file. A method for each physical table appears below. -/
def PublishedDescriptors : Prop :=
  Published (NodeRecipe.descriptors S K kind) cur (fields K c x layout) extra old final

/-- A word equation in terms of the precise memory visible at the time of its read. -/
def RowValue (start i : ℕ) (row : Template.F) : Prop :=
  let a:=fields K c x layout start+i
  final a=Formula.value (fun _=>cur) (beforeAddress extra a old final) (fun _=>(a:Word w)) row

theorem publish_descriptors (pub : Fin 1→Word w)
    (head : Scans.Header cur old c.header 63 f) (earlier : c.header+64≤c.heap) (later : tail≤cur.val) :
    PublishedDescriptors S K c x layout cur kind old
      (((NodeRecipe.descriptors S K kind).install cur).execute cur pub old).2 := by
  have lo : c.heap≤extra := by simp [Resident.pointers,allocate,headerWord]; omega
  intro a row atWord
  exact publish (NodeRecipe.descriptors S K kind) cur pub old head (earlier.trans lo) later
    (descriptors_consecutive S K c x layout kind) atWord

variable {S K c x layout cur kind old final}
variable (stored : PublishedDescriptors S K c x layout cur kind old final)
include stored

/-- Future high-memory writes, including the stage-pointer advance, preserve every saved row. -/
theorem PublishedDescriptors.frameOut {later : Memory w}
    (equal : ∀ a,a<tail → later a=final a) :
    PublishedDescriptors S K c x layout cur kind old later := by
  intro a row word
  have range:=word.range (descriptors_consecutive S K c x layout kind).span.2
  have same : beforeAddress extra a old later=beforeAddress extra a old final := by
    funext j
    by_cases h : extra≤j ∧ j<a
    · simp only [beforeAddress,ite_eq_left h];exact equal j (h.2.trans range.2)
    · simp [beforeAddress,h]
  rw [equal a range.2,same]
  exact stored word

theorem PublishedDescriptors.kernel {i : ℕ} (h : i<f 35) :
    RowValue K c x layout cur old final 34 i (NodeRecipe.kernel S K kind) :=
  stored (.left (.left (.one h)))

theorem PublishedDescriptors.incident {i : ℕ} (h : i<f 37) :
    RowValue K c x layout cur old final 36 i (NodeRecipe.motif S K) :=
  stored (.left (.right (.left (.one h))))

theorem PublishedDescriptors.halfHeader {i : ℕ} (h : i<f 39) :
    RowValue K c x layout cur old final 38 i (NodeRecipe.halfHeader S.outputDegree) :=
  stored (.left (.right (.right (.left (.one h)))))

theorem PublishedDescriptors.half {i : ℕ} (h : i<f 41) :
    RowValue K c x layout cur old final 40 i (NodeRecipe.halfRows S.outputDegree) :=
  stored (.left (.right (.right (.right (.one h)))))

theorem PublishedDescriptors.child {i : ℕ} (h : i<f 43) :
    RowValue K c x layout cur old final 42 i (NodeRecipe.selectedAt
      (fun lay=>ChildRows.entry Template.ptr S lay (NodeRecipe.offset NodeRecipe.childrenBase))) :=
  stored (.right (.left (.one h)))

theorem PublishedDescriptors.owner {i : ℕ} (h : i<f 45) :
    RowValue K c x layout cur old final 44 i (NodeRecipe.selectedAt
      (fun lay=>ChildRows.parent Template.ptr S lay (NodeRecipe.offset NodeRecipe.ownerBase))) :=
  stored (.right (.right (.one h)))

omit stored in
theorem RowValue.read {start i : ℕ} {row : Template.F} {v : Word w}
    (rowAt : RowValue K c x layout cur old final start i row)
    (bounds : f start+i<tail)
    (read : ∀ m : Memory w,agreesOutside extra tail m old →
      Formula.value (fun _=>cur) m (fun _=>((f start+i:ℕ):Word w)) row=v) :
    final (f start+i)=v := by
  apply rowAt.trans (read _ ?_)
  intro j outside
  exact beforeAddress_frame extra (f start+i) old final j
    (outside.imp id (fun h=>bounds.le.trans h))


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.DescriptorSpan

end OAI
