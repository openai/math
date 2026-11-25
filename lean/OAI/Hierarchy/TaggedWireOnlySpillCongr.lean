import OAI.Hierarchy.TaggedWireSpillMatrix
import OAI.Hierarchy.TaggedWireSpillRouterCongr
import OAI.Hierarchy.ProtocolRAMDateSpillDirectory

namespace OAI
/-! # Entrywise invariance of spill routing off the original mounted core -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.Mount
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open AdaptiveProbe WireTelescope ProtocolRAMDateSpillRank ProtocolRAM.Calendar.CoreRoute
open scoped Classical BigOperators
variable {F : Type*} [Field F] {S : PurchaseSampler} {h d k K edges : ℕ}
    {π : Equiv.Perm (Fin (2^h))} {place : Site h d k→Fin K}
variable (B C : Mount (S:=S) π place edges) (inj : Function.Injective place) (pad : Chord K)
    (o : Orders h d k) (spill : Commodity (Fin (2^h)) (Stages h d) k→ℕ)

/-- Any positive spill wire is literally the image of an original core row,
even when its commodity walk visits the same numbered wire several times. -/
theorem spill_row_of_positive (i : Fin edges) (active : 0<routeLoad B.ordinary spill i) :
    ∃j,B.row j=i := by
  by_contra off
  have absent (j : Commodity (Fin (2^h)) (Stages h d) k) : i∉B.ordinary j := by
    intro found
    obtain ⟨e,_,eqn⟩:=List.mem_map.mp found
    exact off ⟨e,eqn⟩
  have zero : routeLoad B.ordinary spill i=0 :=
    Finset.sum_eq_zero (fun j _=>by simp [List.count_eq_zero.mpr (absent j)])
  omega

private theorem installed_spill (B : Mount (S:=S) π place edges) (inj : Function.Injective place)
    (pad : Chord K) (spill : Commodity (Fin (2^h)) (Stages h d) k→ℕ) :
    let L:=B.datedLayout inj pad
    installedWidths L.edge (routeLoad L.routes (L.bits spill))=B.actual.chordWidths (routeLoad B.ordinary spill) := by
  intro L
  rw [show routeLoad L.routes (L.bits spill)=routeLoad B.ordinary spill from funext (L.measured spill)]
  exact filled_width _ pad _ (B.spill_off_loop inj spill)

private theorem trans_congr {A B C : Type*} {e f : A≃B} {g h : B≃C}
    (ab : e=f) (bc : g=h) : e.trans g=f.trans h := by
  cases ab
  cases bc
  rfl

theorem onlySpill_congr (sameRow : B.row=C.row) :
    ∃head : B.actual.chordWidths (routeLoad B.ordinary spill)=C.actual.chordWidths (routeLoad C.ordinary spill),
      rebase rfl head (B.onlySpill (F:=F) inj pad spill (spillEnum B o))=
        C.onlySpill (F:=F) inj pad spill (spillEnum C o) := by
  obtain ⟨g,z,tail,head⟩:=B
  obtain ⟨g',z',tail',head'⟩:=C
  change z=z' at sameRow
  subst z'
  let B : Mount (S:=S) π place edges := ⟨g,z,tail,head⟩
  let C : Mount (S:=S) π place edges := ⟨g',z,tail',head'⟩
  let L:=B.datedLayout inj pad
  let L':=C.datedLayout inj pad
  let bits:=L.bits spill
  let loads:=routeLoad L.routes bits
  have liveInput (i) (positive : 0<bits i) : L.family i=L'.family i := by
    change L.data.original (L.num i)=L'.data.original (L.num i)
    change 0<SettledMatrix.Layout.available (fun _:Fin edges=>0) spill (fun _:Empty=>0)
      (fun _:Empty=>0) (L.num i) at positive
    rcases choice:L.num i with e|j|v
    · simp [choice,SettledMatrix.Layout.available] at positive
    · rfl
    · exact v.elim
  have liveOutput (i : Fin edges) (positive : 0<loads i) : L.edge i=L'.edge i := by
    obtain ⟨j,equal⟩:=B.spill_row_of_positive spill i (positive.trans_eq (L.measured spill i))
    change filledChord g pad i=filledChord g' pad i
    change z j=i at equal
    subst i
    simp only [filledChord,tail,head,tail',head']
  have stable := congrArg Sigma.fst (BitRows.data_congr L.edge L'.edge loads liveOutput)
  have shape := ((installed_spill B inj pad spill).symm.trans stable).trans (installed_spill C inj pad spill)
  refine ⟨shape,eq_of_heq ((rebase_heq rfl shape _).trans ?_)⟩
  let left := L.operator (F:=F) spill (L.nativeOrder (spillEnum B o))
  let right := L'.operator (F:=F) spill (L'.nativeOrder (spillEnum C o))
  have source : HEq (B.onlySpill (F:=F) inj pad spill (spillEnum B o)) left :=
    rebase_heq (L.installed spill) (installed_spill B inj pad spill) left
  have target : HEq (C.onlySpill (F:=F) inj pad spill (spillEnum C o)) right :=
    rebase_heq (L'.installed spill) (installed_spill C inj pad spill) right
  have enumerated : spillEnum B o=spillEnum C o := by
    apply Equiv.ext
    intro j
    rfl
  have occurrences : L.data.occurrences=L'.data.occurrences := by
    apply Equiv.ext
    rintro (e|⟨j,a⟩|⟨v,a⟩)
    · rfl
    · rfl
    · exact v.elim
  have relabel : (Equiv.sigmaCongrLeft (β:=fun x=>Fin (L.data.steps x).length) L.num).symm =
      (Equiv.sigmaCongrLeft (β:=fun x=>Fin (L'.data.steps x).length) L'.num).symm := by
    apply congrArg Equiv.symm
    apply Equiv.ext
    rintro ⟨i,j⟩
    rfl
  have rank : L.nativeOrder (spillEnum B o)=L'.nativeOrder (spillEnum C o) := by
    have named : (Equiv.refl (Fin edges)).sumCongr (spillEnum B o) =
        (Equiv.refl (Fin edges)).sumCongr (spillEnum C o) :=
      congrArg (fun f=>(Equiv.refl (Fin edges)).sumCongr f) enumerated
    exact trans_congr rfl (trans_congr named (trans_congr occurrences relabel))
  have inner := chordRouter_supported (F:=F) L.routes bits liveInput liveOutput
    (L.nativeOrder (spillEnum B o)) L.paths L'.paths
  have renamed := congrArg (fun order=>chordRouter (F:=F) L'.family L'.edge
    L.routes bits order L'.paths) rank
  have inner : HEq left right := inner.trans (heq_of_eq renamed)
  exact source.trans (inner.trans target.symm)

end Hierarchy.ProbeStage.CoreBoard.Mount
end

end OAI
