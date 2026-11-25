import OAI.Computability.BorderVNP.FiniteEvaluatorMergedHostScore

/-! # Host factors on decoded logical cells for both real argument formats -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.Reports

open VPVNP.BurstRAM RoutingISA RoutingISA.CellPacket.Supplement
open scoped BigOperators Classical

variable {F : Type*} [Field F] [Fintype F] {Orig : Type} {w : ℕ}

/-- The true global owner scan and compact scalar scan on any physical
memory with the current frame and owner-column readback. -/
theorem hostFactor_rows_for (X : Cells.Inputs F) (pub : Arg → Word w) (after : Memory w)
    (frame : CellDispatch.Frame.ofMemory pub after=⟨X.layout.team,X.layout.calls,X.layout.cells⟩)
    (owners : ∀ c < X.layout.cells, (after (X.layout.call c)).val=X.layout.owner X.publicMem c) :
    X.hostFactor pub after = ∏ i : Fin X.count,
      ((X.cells (TypedTaskBuilder.globalCell X.layout X.publicMem i.val)).weight : F) *
        Merged.reportScalar (X.digits i.val) (X.claim i.val) := by
  let l := X.layout
  let raw := X.publicMem
  let f := (⟨l.team,l.calls,l.cells⟩ : CellDispatch.Frame)
  let val := fun j => (X.cells (TypedTaskBuilder.globalCell l raw j)).weight
  have owned : ((f.ownedRows after 0 f.count).map (fun c => (X.cells c).weight)).prod =
      ∏ i : Fin X.count, val i.val := by
    refine (congrArg List.prod (List.map_congr_left ?_)).trans (owned_product l raw after val owners)
    intro c hc
    obtain ⟨pos,test⟩ := List.mem_filter.mp hc
    obtain ⟨j,hj,eq⟩ := List.mem_range'.mp pos
    have cn : c < l.cells := by simpa [eq,f] using hj
    have addr : f.address c=l.call c := by simp [f,CellDispatch.Frame.address,TypedTaskBuilder.Layout.call,Nat.mul_comm,Nat.add_comm]
    have ownedHere := of_decide_eq_true test
    change (after (f.address c)).val=l.team at ownedHere
    rw [addr,owners c cn] at ownedHere
    simp only [val,TypedTaskBuilder.global_at l raw cn ownedHere]
  change X.hostFactor pub after=_
  rw [Cells.Inputs.hostFactor,frame,owned,Int.cast_prod]
  have rng : List.range X.count=List.ofFn (fun i : Fin X.count => i.val) := by
    apply List.ext_getElem <;> simp
  rw [Cells.Inputs.outputs,rng,List.map_ofFn,List.prod_ofFn,← Finset.prod_mul_distrib]
  rfl

/-- The native signed and scalar scans use the same globally numbered logical
cell for every compact owned task. This result applies to the actual sparse
decoder and to dense packets. -/
theorem hostFactor_after_splice_for (X : Cells.Inputs F) (codec : Cells.Codec) (pub : Arg → Word w) (m : Memory w)
    (owned : ℕ → Batch.Owned Orig) (published : readings m=X.layout.published X.publicMem)
    (apart : MetaOutside X.layout X.count owned) {n : ℕ}
    (ready : Cells.Prepared X pub (Batch.written m (fun j => (owned j).cell) X.count) n codec) :
    X.hostFactor pub (Batch.written m (fun j => (owned j).cell) X.count) =
      ∏ i : Fin X.count, ((X.cells (TypedTaskBuilder.globalCell X.layout X.publicMem i.val)).weight : F) *
        Merged.reportScalar (X.digits i.val) (X.claim i.val) := by
  let l := X.layout
  let raw := X.publicMem
  let after := Batch.written m (fun j => (owned j).cell) X.count
  let f := (⟨l.team,l.calls,l.cells⟩ : CellDispatch.Frame)
  have frame : CellDispatch.Frame.ofMemory pub after=f := by
    unfold CellDispatch.Frame.ofMemory
    rw [ready.pointer]
    congr 1
    · exact ready.fields.outer.1
    · exact ready.fields.outer.2.2.1
    · exact ready.fields.outer.2.2.2.1
  have owners (c : ℕ) (hc : c < l.cells) : (after (l.call c)).val=l.owner raw c := by
    have kept := Batch.preserve m (fun j => (owned j).cell) (i:=0) (Nat.zero_le X.count)
      (l.call c) (fun j _ hj => ((apart j hj).2.2 c hc).2)
    change readings after (l.call c)=_
    rw [show readings after (l.call c)=readings m (l.call c) from congrArg Fin.val kept,published]
    exact l.published_owner raw ready.room hc
  exact hostFactor_rows_for X pub after frame owners

end FiniteEvaluator.Reports

namespace FiniteEvaluator.Merged

open Crossing Packing Packing.Inherited FiniteDiagonal FiniteDiagonal.CellTrace BorderVNP.Cube Cube.Physical
open VPVNP.BurstRAM RoutingISA RoutingISA.CellPacket.Supplement TeamRAM
open scoped Classical BigOperators

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
  {F : Type*} [Field F] [Fintype F] {T : N.Tables F} {L : FieldPacketPlan N F} {S : FieldSiteDirectory N T}
  (V : FieldRawLayout L S) (R : ℕ) (bank : Ports bits) (z : V.Public R)
  (u : Fin (R+1)) (digits : ℕ) (rows : List Reports.Row)
  (order : Fin rows.length ≃ {c : L.Cell // V.cellOwner R z c = u})
  (X : Cells.Inputs F) (claim : ∀ _ : Fin rows.length, Fin (Fintype.card F) → Fin digits → Bool)
local notation "site₀" i => rowSite V R z u rows order i
local notation "input₀" i => rowInput V R bank z u rows order i
local notation "cell₀" i => X.cells (TypedTaskBuilder.globalCell X.layout X.publicMem (Fin.val i))

/-- Logical field inputs at their real compact task ordinals. Sparse packet bytes
are decoded before taking the logical supplied bank below. -/
structure RowInputs : Prop where
  /-- Number of true owned cells, published in frame word 90. -/
  count : X.count=rows.length
  /-- Genuine boxes, rebased bindings and field count addresses of each merged cell. -/
  directory : ∀ i : Fin rows.length, (cell₀ i).directory=Placement.packet N L.cell (order i).val
    V.siteID S.edgeID S.portID S.site (Reports.fields (site₀ i).size (Fintype.card F) digits)
  /-- Exact count of internal and staged private bits. -/
  wires : ∀ i : Fin rows.length, (cell₀ i).privateWires=(site₀ i).work
  /-- The physical endpoint values and true chronological report suffix after decoding. -/
  external : ∀ i : Fin rows.length, (cell₀ i).external=List.ofFn (input₀ i)++FiniteScalarRounds.stream F (claim i)
  /-- The scalar scanner uses the fixed number of binary places of these reports. -/
  digitsAt : ∀ i : Fin rows.length, X.digits i.val=digits
  /-- Every physical report digit is the corresponding bit of the indexed matrix. -/
  claimsAt : ∀ (i : Fin rows.length) v j, X.claim i.val v j=claim i v (Fin.cast (digitsAt i) j)

private theorem cast_scalar {a b : ℕ} (h : a=b) (p : Fin (Fintype.card F) → Fin a → Bool)
    (q : Fin (Fintype.card F) → Fin b → Bool) (same : ∀ v j, p v j=q v (Fin.cast h j)) :
    reportScalar a p=reportScalar b q := by
  subst b
  exact congrArg _ (funext fun v => funext fun j => same v j)

private theorem rowProduct (h : RowInputs V R bank z u digits rows order X claim) :
    (∏ i : Fin X.count, ((X.cells (TypedTaskBuilder.globalCell X.layout X.publicMem i.val)).weight : F) *
      reportScalar (X.digits i.val) (X.claim i.val)) =
    ∏ i : Fin rows.length, rowScore V R bank z u digits rows order i (claim i) := by
  let term := fun j => ((X.cells (TypedTaskBuilder.globalCell X.layout X.publicMem j)).weight : F) *
    reportScalar (X.digits j) (X.claim j)
  change (∏ i : Fin X.count, term i.val)=_
  refine ((finCongr h.count).prod_comp (fun i => term i.val)).trans (Finset.prod_congr rfl ?_)
  intro i _
  have dir := h.directory i
  rw [← report_directory N L.cell (order i).val V.siteID S.edgeID S.portID S.site] at dir
  have hv : (cell₀ i)=validator (site₀ i) digits (input₀ i) (claim i) := by
    cases eq : (cell₀ i) with
    | mk d k bs =>
      have work := h.wires i
      have ext := h.external i
      rw [eq] at dir work ext
      unfold validator
      change d=_ at dir
      change k=_ at work
      change bs=_ at ext
      rw [dir,work,ext]
      rfl
  change ((cell₀ i).weight : F)*reportScalar (X.digits i.val) (X.claim i.val)=_
  rw [hv,cast_scalar (h.digitsAt i) _ (claim i) (h.claimsAt i)]
  rfl

/-- Host field weight on an arbitrary genuine runtime memory, including
the rewritten external task pointers produced by the sparse prepass. -/
theorem hostFactor_rowScore_memory (h : RowInputs V R bank z u digits rows order X claim)
    {w : ℕ} (pub : Arg → Word w) (after : Memory w)
    (frame : CellDispatch.Frame.ofMemory pub after=⟨X.layout.team,X.layout.calls,X.layout.cells⟩)
    (owners : ∀ c < X.layout.cells, (after (X.layout.call c)).val=X.layout.owner X.publicMem c) :
    X.hostFactor pub after=∏ i : Fin rows.length, rowScore V R bank z u digits rows order i (claim i) := by
  rw [Reports.hostFactor_rows_for X pub after frame owners]
  exact rowProduct V R bank z u digits rows order X claim h

/-- Full owned host weight on the real post-splice memory for either decoder,
using decoded endpoint and field-matrix data at their true physical rows. -/
theorem hostFactor_rowScore_for (h : RowInputs V R bank z u digits rows order X claim) (codec : Cells.Codec)
    {w n : ℕ} {Orig : Type} (pub : Arg → Word w) (m : Memory w) (owned : ℕ → Batch.Owned Orig)
    (published : readings m=X.layout.published X.publicMem) (apart : Reports.MetaOutside X.layout X.count owned)
    (ready : Cells.Prepared X pub (Batch.written m (fun j => (owned j).cell) X.count) n codec) :
    X.hostFactor pub (Batch.written m (fun j => (owned j).cell) X.count) =
      ∏ i : Fin rows.length, rowScore V R bank z u digits rows order i (claim i) := by
  rw [Reports.hostFactor_after_splice_for X codec pub m owned published apart ready]
  exact rowProduct V R bank z u digits rows order X claim h

end FiniteEvaluator.Merged

end BorderVNP
end Computability
end OAI
