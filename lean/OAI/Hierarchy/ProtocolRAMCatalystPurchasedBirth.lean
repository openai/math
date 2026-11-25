import OAI.Hierarchy.ProbeStripDirectoryCore
import OAI.Hierarchy.ProtocolRAMStoredMarkFlags

namespace OAI
/-! # The retained DFS cells, signed flags and header at a later acquired strip -/
noncomputable section
namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage PurchaseFrozen
open scoped Classical
variable {z d k : ℕ}
namespace StripDirectory

/-- The exact cells read by the later candidate test: the preceding
outer shelf's DFS columns and flags, and the static stratum header. -/
def ArchiveCell (sh : Shelf) (S : PurchaseSampler) (depth start : ℕ) (x : ℕ) : Prop :=
  (∃ key : Key z d k,∃ i : PurchaseDirectory.Index (2^z) S.degree depth,∃ j : Fin (depth+1),
    x=(sh.L S depth key).source.base+(j.val*(sh.L S depth key).candidates+i.val)) ∨
  (∃ key : Key z d k,∃ i : Fin (paths z S.degree depth),x=sh.flagsBase S z d k depth+key.val*paths z S.degree depth+i.val) ∨
  let h:=stratumHeader z d k S.degree depth start
  h.start≤ x ∧ x< h.stop

structure ArchiveReads (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth start : ℕ)
    (phase : PhasePrice) (T : ℝ) (kind : ℕ) (frozen m : Shelf.Mem z d) (k : ℕ) : Prop where
  tiles : ∀ key : Key z d k,ProtocolRAMPurchaseGateColumns.TileRows
    (sh.L S depth key).source (Shelf.pathRows S π depth key) m
  flags : StoredFlags sh S π depth phase T kind frozen m k
  header : (stratumHeader z d k S.degree depth start).Loaded m

theorem ArchiveReads.change {sh : Shelf} {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^z))} {depth start : ℕ}
    {phase : PhasePrice} {T : ℝ} {kind : ℕ} {frozen m n : Shelf.Mem z d}
    (A : ArchiveReads sh S π depth start phase T kind frozen m k)
    (frame : ∀ x,ArchiveCell (z:=z) (d:=d) (k:=k) sh S depth start x→n x=m x) :
    ArchiveReads sh S π depth start phase T kind frozen n k := by
  constructor
  · intro key i j
    exact (frame _ (.inl ⟨key,i,j,rfl⟩)).trans (A.tiles key i j)
  · intro key i
    exact (frame _ (.inr (.inl ⟨key,i,rfl⟩))).trans (A.flags key i)
  · exact A.header.frame (fun x lo hi=>frame x (.inr (.inr ⟨lo,hi⟩)))

end StripDirectory
namespace Calendar.StripChart
open StripDirectory

/-- Native outer-purchase receipt at a later inner entry. Updating the
outer stock pointer matters to its signed decisions. The inner ROM retains
the very same tile and flag addresses after this update. -/
structure PurchasedBirth (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z)))
    (depth start : ℕ) (before : Shelf.Mem z d) (k : ℕ) where
  stock : ℕ
  phase : PhasePrice
  price : ℝ
  kind : ℕ
  frozen : Shelf.Mem z d
  saved : ArchiveReads ({sh with stockBase:=stock}) S π depth start phase price kind frozen before k

end Calendar.StripChart
end Hierarchy.ProtocolRAM
end

end OAI
