import OAI.Hierarchy.ProtocolRAMCatalystArchivePrefix

namespace OAI
/-! # Permanent route directory after the physical reserve and settlement passes -/
noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive.TerminalLayout
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe Calendar
open scoped Classical Fin.CommRing

/-- All four directory columns survive the original reserve and route passes, and any
subsequent forward scan that retains the first six native pages. -/
theorem settled_directory_at {w entries r count : ℕ} (bits start n reserveAmount : ℕ)
    (cat : CatalogueRows.Board) (stock : Bank) (site : Fin entries → Fin count)
    (debit : Fin entries → ℕ) {I J : Type*} [Fintype I] [Fintype J]
    {core : I → List (Fin cat.rows)} {center : J → List (Fin cat.rows)}
    (enum : Fin r ≃ RouteOccurrence core center) (ci : I → ℕ) (cj : J → ℕ)
    (archive out : Memory w) (rows : cat.rows ≤ 2^bits)
    (directory : RouteSettlement.Directory (settlement bits stock) archive enum ci cj) :
    let b := settlement bits stock
    let a := reserve start n bits
    let sink := cat.sink r b (source bits) (table bits) (destination bits)
      (sinkBank start n r cat.rows)
    let settled := sink.output (ReserveUse.output a b reserveAmount site debit archive) enum ci cj
    (∀ x < 6*2^bits, out x = settled x) →
      RouteSettlement.Directory b out enum ci cj := by
  intro b a sink settled kept
  have word (base : ℕ) (lower : 2 ≤ base) (upper : base ≤ 5) (i : Word w) :
      (page bits base).read out i = (page bits base).read archive i := by
    let size := 2^bits
    let j := i.val % size
    have hj : j < size := Nat.mod_lt _ (Nat.two_pow_pos bits)
    have hb : 2*size ≤ base*size := Nat.mul_le_mul_right _ lower
    have he : base*size ≤ 5*size := Nat.mul_le_mul_right _ upper
    have cut : base*size+j < 6*size := by omega
    have head : size+cat.rows ≤ base*size+j := by
      have hs : cat.rows ≤ size := rows
      omega
    change out (base*size+j) = archive (base*size+j)
    exact (kept _ cut).trans (archive_prefix_at bits start n reserveAmount cat stock site
      debit enum ci cj archive _ cut (.inr head))
  exact ⟨fun i => (word 4 (by decide) (by decide) _).trans (directory.headKind i),
    fun i => (word 5 (by decide) (by decide) _).trans (directory.headIndex i),
    fun i => (word 4 (by decide) (by decide) _).trans (directory.tailKind i),
    fun i => (word 5 (by decide) (by decide) _).trans (directory.tailIndex i)⟩

end Hierarchy.ProtocolRAM.CatalystArchive.TerminalLayout
end

end OAI
