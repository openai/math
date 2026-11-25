import OAI.Computability.BorderVNP.CellPacketGeometryHistoryOutput
import OAI.Computability.BorderVNP.CellSparseExteriorSupplementalSources

/-! # The native supplemental reader's inputs in every physically published sparse cell -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History.Native

open CellSparse CellSparse.Packet CellSparse.Packet.Source SiteWords RoutingISA.CellPacket
open VPVNP.BurstRAM RoutingISA

variable {a C p d dest H : ℕ} {O E : Type}
variable {G : SiteWords.Directory (Fin a) O C} {ptr : O → E} {arg : E → ℕ} {mem : ℕ → ℕ}

/-- Concrete prepass inputs. The merged descriptors occupy the prefix of the
cell range, followed by its four reserved triples. -/
structure CellMemory (P : Placed O) (geom exclusive : ℕ) (mem : ℕ → ℕ) : Prop where
  prefixDescriptors : WordsAt mem P.descriptorBase (descriptors (Supplement.prefixChunks P))
  prefixWords : WordsAt mem P.publicBase ((Supplement.prefixParts P).flatMap Part.publicBuffer)
  geometry : WordsAt mem geom (fieldList record P.rows++fieldList vector P.reports)
  count : mem geom = P.rows.length
  tail : WordsAt mem (P.descriptorBase+(descriptors (Supplement.prefixChunks P)).length)
    ([0,geom,1+(P.rows.flatMap record).length+(fieldList vector P.reports).length] ++ List.replicate 9 0)
  endAddress : exclusive = P.descriptorBase+(descriptors (Supplement.prefixChunks P)).length+12

private theorem chunkCount (slot : O → ℕ) (fs : O → List Factor) (xs : List (Source.Part O)) (base : ℕ) :
    (chunks slot H fs base xs).length=xs.length := by
  induction xs generalizing base with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [chunks,ih]

/-- All cells share the same reconstructed source/descriptor buffers. Their
absolute addresses are the ranks loaded from the two real native marker columns. -/
theorem Published.cells (h : Published G p d dest H ptr arg mem) (slot : O → ℕ) (fs : O → List Factor)
    (address : ∀ i, arg (ptr i)=slot i) :
    ∃ hf : C+G.words.length+C≤2^p, ∃ hs : C+(Schema.coords (G.referenceRows ptr).length).length+C≤2^d,
    ∀ c : Fin C, ∀ ext scratch burst external,
      let words := sectionRange mem dest (Markers.start hf c) (Markers.stop hf c)
      let table := sectionRange mem (descriptorBank dest p) (Markers.start hs c) (Markers.stop hs c)
      let placed := G.placed c H slot fs words.1 table.1 ext scratch burst external
      let geom := words.1+((Supplement.prefixParts placed).flatMap Part.publicBuffer).length
      CellMemory placed geom (descriptorBank dest p+mem (descriptorBank dest p+(2^d+(Markers.stop hs c).val))) mem := by
  obtain ⟨hf,hs,π,buf⟩ := h
  refine ⟨hf,hs,fun c ext scratch burst external => ?_⟩
  intro words table placed geom
  have r := buf.reserved_split address fs c
  have packed := r.1
  rw [List.append_assoc] at packed
  have prefixRows := packed.left
  have tail := packed.right
  have source := (buf.publicWords c).2
  have parts : plan (G.privateWires c) (G.cellBoxes c) (G.cellRecords c) (G.reports c) =
      Schema.prefixParts G c ++ [.publicWords (fieldList record (G.cellRecords c)++fieldList vector (G.reports c))] := rfl
  rw [parts] at source
  simp only [List.flatMap_append,List.flatMap_singleton,Part.publicBuffer] at source
  refine ⟨prefixRows,source.left,source.right,r.2.1,tail,?_⟩
  have stop := (buf.descriptor_end c).2
  have len := (buf.reserved address fs c).1
  rw [parts,List.length_append,List.length_singleton] at len
  have prefixLen : (descriptors (Supplement.prefixChunks placed)).length=3*(Schema.prefixParts G c).length := by
    rw [descriptors_length,Supplement.prefixChunks,chunkCount]
    rfl
  change table.1+table.2 = _ at stop
  change table.2 = _ at len
  change _ = table.1+(descriptors (Supplement.prefixChunks placed)).length+12
  rw [←stop,prefixLen]; omega

/-- A bounded read of the retained geometry survives the subsequent input and
task initialization stores whenever those addresses have been preserved. -/
private theorem keep_words {m n : ℕ → ℕ} {a : ℕ} {xs : List ℕ} (h : WordsAt m a xs)
    (kept : ∀ i : Fin xs.length, n (a+i.val)=m (a+i.val)) : WordsAt n a xs :=
  fun i => (kept i).trans (h i)

/-- The whole reserved descriptor range, including its final twelve words,
survives the task-row writer. The caller's interval condition also protects
the prefix passed to the sparse private reader. -/
theorem CellMemory.tail_scalars {O : Type} {P : Placed O} {geom exclusive : ℕ} {m : ℕ → ℕ}
    (h : CellMemory P geom exclusive m) (next : ℕ → ℕ)
    (kept : ∀ a, P.descriptorBase ≤ a → a < exclusive → next a=m a) :
    let t := P.descriptorBase+(descriptors (Supplement.prefixChunks P)).length
    next (t+1)=geom ∧ next (t+2)=1+(P.rows.flatMap record).length+(fieldList vector P.reports).length := by
  intro t
  have endEq : exclusive=t+12 := h.endAddress
  have first := h.tail ⟨1,by simp⟩
  have second := h.tail ⟨2,by simp⟩
  have start : P.descriptorBase ≤ t := Nat.le_add_right ..
  exact ⟨(kept (t+1) (by omega) (by omega)).trans first,(kept (t+2) (by omega) (by omega)).trans second⟩

/-- Actual delivered one-copy bodies supply the private chunks of the native
reader after the transmission phase. The geometry preservation assumptions
concern only its two public subintervals and the original descriptor prefix. -/
theorem CellMemory.metadata {O : Type} {exclusive description : ℕ} {origin : ℕ → ℕ}
    (owned : Supplement.Batch.Owned O) (h : CellMemory owned.placed owned.geometry exclusive origin)
    {w : ℕ} (m : Memory w)
    (descKept : ∀ i : Fin (descriptors (Supplement.prefixChunks owned.placed)).length,
      readings m (owned.placed.descriptorBase+i.val)=origin (owned.placed.descriptorBase+i.val))
    (pubKept : ∀ i : Fin ((Supplement.prefixParts owned.placed).flatMap Part.publicBuffer).length,
      readings m (owned.placed.publicBase+i.val)=origin (owned.placed.publicBase+i.val))
    (geomKept : ∀ i : Fin (fieldList record owned.placed.rows++fieldList vector owned.placed.reports).length,
      readings m (owned.geometry+i.val)=origin (owned.geometry+i.val))
    (delivered : ∀ j, Part.original j∈Supplement.prefixParts owned.placed →
      Delivered (description := description) (readings m) (owned.placed.slot j) owned.placed.headerWidth (owned.placed.factors j))
    (room : ∀ j, owned.placed.headerWidth+(boxBody (owned.placed.factors j)).length ≤ description)
    (fits : ∀ j, (boxBody (owned.placed.factors j)).length<2^owned.placed.headerWidth)
    (newRows : WordsAt (readings m) owned.layout.supplement (owned.extra.flatMap record)) :
    Supplement.Batch.Original owned.metadata owned.layout owned.geometry owned.extra m := by
  apply Supplement.Batch.metadataOriginal
  · exact keep_words h.prefixDescriptors descKept
  · exact chunks_stored _ _ _ _ _ _ delivered room fits (keep_words h.prefixWords pubKept)
  · exact keep_words h.geometry geomKept
  · exact newRows

end CellPacketGeometry.History.Native

end BorderVNP
end Computability
end OAI
