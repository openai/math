import OAI.Computability.BorderVNP.DiagonalAssignedRows
import OAI.Computability.BorderVNP.DiagonalPacketTallyBounds

/-! # Multiplicities on the numbered paths of equation (11.2) -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.Assigned

open Crossing Packing _root_.OAI.Computability.BorderVNP.Cube Branch
open scoped BigOperators Classical

set_option synthInstance.maxSize 4000

variable {D n d b h K s exp k size : ℕ} {Team Team' Gadget History Hidden Pin : Type}
    [Fintype Team] [Fintype Team']
    {Port : History → Type} {width : (q : History) → Port q → ℕ}
    (N : (q : History) → Network D (Port q) (width q))
    (packet : ∀ q, PacketPlacement Team n d b h K (N q))
    (tags : ∀ q, Hidden → Tracked Team (PairedParameters k size) Gadget exp (N q))
    (pin : Pin → ∀ q, Ports (width q)) (pos : TableEntry n b h K s → Gadget)
    (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))) (teams : Team ≃ Team')

/-- The scalar word read at any numbered, fully assigned term is bounded
by the expanded payload of that same stored history and the vertices of its
own cube packets. The fine hidden choice changes the values within these
records, while the bound accounts for every original scalar use. -/
theorem numbered_counts_le (payload : ∀ q, (N q).Site → ℕ)
    (bound : ∀ q z, PayloadBound (tags q z).tags (payload q))
    (i : Pin) (a : Path N packet tags pin pos i) (g : Gadget) :
    (∑ t, (numbered N packet tags pin pos ord teams i a).counts t g) ≤
      (∑ v, payload a.1 v) + Fintype.card (Packet n d (packet a.1).blocks × Vertex (n+1)) := by
  rw [numbered,Tally.sum_renumber_counts]
  let p := packet a.1
  let t := tags a.1 a.2.1
  let run := a.2.2.val
  exact Physical.pathTally_count_le p.slot t.tags (pin i a.1) (fun _ => pos) t.words
    p.label (p.team run.2.2.2.1) (bound a.1 a.2.1) run g

end Diagonal.CellEntries.Assigned

end BorderVNP
end Computability
end OAI
