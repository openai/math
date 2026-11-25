import OAI.Computability.BorderVNP.FiniteEvaluatorPrepareReportsReady
import OAI.Computability.BorderVNP.CellSparseExteriorSupplementalCost
import OAI.Computability.BorderVNP.CellSparseExteriorTeamCost

/-! # The prepared finite field evaluator on actual compressed cell arguments -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.Reports

open VPVNP.BurstRAM RoutingISA RoutingISA.CompactMachine RoutingISA.TypedTaskBuilder
open RoutingISA.CellPacket RoutingISA.CellPacket.Supplement
open scoped Classical

variable {Site : Type} {F : Type*} [Fintype F]

/-- The local scalar packer reads the raw report suffix of the physical sparse
field. The signed validator restores the dense mathematical input by its true
global cell ordinal. -/
noncomputable def sparseInputs (l : TypedTaskBuilder.Layout) (raw : ℕ → ℕ) (owned : ℕ → Supplement.Batch.Owned Site)
    (fields : ℕ → SparseExterior.Field) (digits : ℕ → ℕ)
    (claims : ∀ i, FiniteScalarRounds.Index F → Fin (digits i) → Bool) : Cells.Inputs F :=
  { inputs l raw owned (fun i => (fields (globalCell l raw i)).prefix) digits claims with
    cells := fun c => { TypedBatch.cellInput (owned (l.before raw c)).placed with external := (fields c).values } }

/-- The metadata retained across the sparse pass, including the actual tail
width at the original dense-bank header and the true call owner. -/
def SparseMetaOutside (l : TypedTaskBuilder.Layout) (sl : SparseExterior.Layout) (rows : ℕ → SparseExterior.Owned) : Prop :=
  ∀ j < sl.count,
    (∀ k < 112, (rows j).Outside sl j (l.frame+k)) ∧
    (∀ k < 8, (rows j).Outside sl j (l.control+k)) ∧
    (∀ k < l.cells, (rows j).Outside sl j (l.tails+k) ∧ (rows j).Outside sl j (l.call k))

/-- The real sparse pass publishes the typed row's encoded pointer and length.
The original scalar metadata and the protected patched descriptors suffice,
including when the logical supplied bank contains unoccupied positions. -/
theorem sparsePrepared {w n : ℕ} (pub : Arg → Word w) (m mt : Memory w)
    (l : TypedTaskBuilder.Layout) (raw : ℕ → ℕ) (src : ℕ → Supplement.Batch.Owned Site)
    (sl : SparseExterior.Layout) (os : ℕ → SparseExterior.Owned) (fields : ℕ → SparseExterior.Field)
    (digits : ℕ → ℕ) (claims : ∀ i, FiniteScalarRounds.Index F → Fin (digits i) → Bool)
    (ptr : (pub 0).val=l.frame) (frame : l.Fields (readings m)) (width : (m (l.frame+30)).val=w)
    (num : (m (l.frame+90)).val=l.before raw l.cells) (count : sl.count=l.before raw l.cells)
    (tasks : sl.tasks=l.tasks) (post : readings mt=SparseExterior.written sl os (readings m) sl.count)
    (safe : SparseExterior.Protected sl os (fun i => (src i).typed)) (apart : SparseMetaOutside l sl os)
    (room : l.Room raw w) (arena : l.Arenas raw w (fun i => (os i).typed sl (src i).typed))
    (control : l.SourceRange l.control 8) (tails : l.SourceRange l.tails l.cells)
    (header : ∀ i < sl.count, (src i).typed.Stored m sl.tasks i)
    (desc : ∀ i < sl.count, WordsAt (readings m) (src i).typed.cell.descriptorBase (descriptors (src i).typed.cell.chunks))
    (chunks : ∀ i < sl.count, ∀ c ∈ (src i).typed.cell.chunks, c.Stored (readings m))
    (owner : ∀ c < l.cells, (m (l.call c)).val=l.owner raw c)
    (call : ∀ i < sl.count, (src i).callRow=l.call (globalCell l raw i))
    (zero : ∀ i < sl.count, (src i).extra=[])
    (field : ∀ i < sl.count, (os i).field=fields (globalCell l raw i))
    (data : ∀ i < sl.count, (fields (globalCell l raw i)).tail=FiniteScalarRounds.stream F (claims i))
    (tail : ∀ i < sl.count, (m (l.tails+globalCell l raw i)).val=(FiniteScalarRounds.stream F (claims i)).length)
    (scalar : ∀ i < sl.count, 2*digits i*Fintype.card F < nativeClock n)
    (cap : ∀ i < sl.count, (((os i).typed sl (src i).typed).cell.burst w).length ≤ TeamScales.width n (1/2))
    (legal : ∀ i < sl.count, (src i).placed.directory.ProfileWidths ∧
      SparseExterior.clock w (src i).placed.directory (src i).placed.privateWires (os i).field ≤ n^25) :
    let rows := fun i => (os i).supplemental sl (src i)
    Cells.Prepared (sparseInputs l raw rows fields digits claims) pub mt n (.sparse fields) := by
  intro rows
  have keep (a : ℕ) (h : ∀ j < sl.count, (os j).Outside sl j a) : readings mt a=readings m a := by
    rw [post]; exact SparseExterior.written_preserve sl os (readings m) (i:=0) (Nat.zero_le _) _ (fun j _ hj => h j hj)
  have outer (j : ℕ) (hj : j<112) := keep (l.frame+j) (fun i hi => (apart i hi).1 j hj)
  have inner (j : ℕ) (hj : j<8) := keep (l.control+j) (fun i hi => (apart i hi).2.1 j hj)
  have live : l.Fields (readings mt) := by
    constructor
    · obtain ⟨a,b,c,d,e,f,g,h⟩ := frame.outer
      exact ⟨(outer 0 (by decide)).trans a,(outer 7 (by decide)).trans b,(outer 14 (by decide)).trans c,
        (outer 15 (by decide)).trans d,(outer 72 (by decide)).trans e,(outer 87 (by decide)).trans f,
        (outer 89 (by decide)).trans g,(outer 92 (by decide)).trans h⟩
    · obtain ⟨a,b,c,d,e,f,g,h⟩ := frame.header
      exact ⟨(inner 0 (by decide)).trans a,(inner 1 (by decide)).trans b,(inner 2 (by decide)).trans c,
        (inner 3 (by decide)).trans d,(inner 4 (by decide)).trans e,(inner 5 (by decide)).trans f,
        (inner 6 (by decide)).trans g,(inner 7 (by decide)).trans h⟩
  have dispatch : CellDispatch.Frame.ofMemory pub mt=⟨l.team,l.calls,l.cells⟩ := by
    unfold CellDispatch.Frame.ofMemory; rw [ptr]
    congr 1
    · exact live.outer.1
    · exact live.outer.2.2.1
    · exact live.outer.2.2.2.1
  have address (i : ℕ) : (CellDispatch.Frame.ofMemory pub mt).address i=l.call i := by
    rw [dispatch]; simp [CellDispatch.Frame.address,TypedTaskBuilder.Layout.call,Nat.mul_comm,Nat.add_comm]
  have rank (c : ℕ) (hc : c < (CellDispatch.Frame.ofMemory pub mt).count)
      (hm : (mt ((CellDispatch.Frame.ofMemory pub mt).address c)).val=(CellDispatch.Frame.ofMemory pub mt).team) :
      l.before raw c<sl.count ∧ globalCell l raw (l.before raw c)=c := by
    rw [address,dispatch] at hm
    rw [dispatch] at hc
    have chosen : l.owner raw c=l.team :=
      (owner c hc).symm.trans ((keep _ (fun j hj => ((apart j hj).2.2 c hc).2)).symm.trans hm)
    exact ⟨count ▸ l.before_strict raw hc chosen,global_at l raw hc chosen⟩
  have stored (i : ℕ) (hi : i<sl.count) := SparseExterior.stored_after sl os (fun j => (src j).typed) m mt post safe
    i hi (header i hi) (desc i hi) (chunks i hi)
  have owned (i : ℕ) (hi : i<l.before raw l.cells) : i<sl.count := count ▸ hi
  refine ⟨ptr,live,(outer 30 (by decide)).trans width,(outer 90 (by decide)).trans num,
    room,arena,control,tails,fun _ _ => rfl,?_,?_,?_,?_,fun _ _ => rfl,?_,?_,?_⟩
  · intro i hi
    exact tasks ▸ (stored i (owned i hi)).1
  · intro i hi
    exact (stored i (owned i hi)).2
  · intro i hi
    change (os i).field.bytes=(fields (globalCell l raw i)).prefix++FiniteScalarRounds.stream F (claims i)
    rw [field i (owned i hi),SparseExterior.Field.bytes_eq,data i (owned i hi)]
  · intro i hi
    have bound := (global_spec l raw hi).1
    exact (keep _ (fun j hj => ((apart j hj).2.2 _ bound).1)).trans (tail i (owned i hi))
  · intro i hi; exact scalar i (owned i hi)
  · refine ⟨?_,fun i hi => cap i (owned i hi)⟩
    intro c hc hm
    obtain ⟨hi,e⟩ := rank c hc hm
    let i := l.before raw c
    have index : i < l.before raw l.cells := count ▸ hi
    refine ⟨i,index,(call i hi).trans ((congrArg l.call e).trans (address c).symm),?_⟩
    change (Supplement.task (src i).layout ((os i).placed sl (src i).placed) (src i).geometry (src i).extra).payload =
      CellSparse.Packet.input (src i).placed.directory (src i).placed.privateWires (fields c).bytes
    rw [Supplement.payload_eq,zero i hi,List.append_nil]
    change CellSparse.Packet.input _ _ (os i).field.bytes=_
    rw [field i hi,e]
    rfl
  · intro c hc hm
    obtain ⟨hi,e⟩ := rank c hc hm
    let i := l.before raw c
    have valid := legal i hi
    rw [field i hi,e] at valid
    exact ⟨valid.1,valid.2,rfl⟩

end FiniteEvaluator.Reports

end BorderVNP
end Computability
end OAI
