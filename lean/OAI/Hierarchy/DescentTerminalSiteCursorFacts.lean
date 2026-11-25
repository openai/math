import OAI.Hierarchy.DescentTerminalSiteCursorRun
import OAI.Hierarchy.DescentTerminalAddressLayout

namespace OAI
/-! # Paid site owners at the actual input sockets of the terminal emitter -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalLocalPortBook DescentTerminalRecipeRows
open DescentTerminalRowArena DescentTerminalBinPack DescentTerminalSpanBook DescentTerminalVertexFields
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable (S : Shape) (I : Input) (base : ℕ) (O : DescentPrivateExponentRAM.Banks)
local notation "A" => rowArena S I base
local notation "L" => layout S I base O
variable {w W q G V M K a : ℕ}

/-- The published pool reserves at least one whole bin because even the
first reached site has an output row. The row arena therefore supplies the
allocator's carry word without any additional machine-width premise. -/
theorem site_cursor_word_room (fit : (A).finish < 2^w) (sites : Fin S.sites → Site)
    (wp : 0<W) (paid : purchased W (counts (q:=q) sites) ≤ S.terminal.rows) :
    S.terminal.rows+W < 2^w :=
  (A).purchased_word_room S.sites_pos fit sites wp paid

/-- The site-owned spans at the suffix's sockets come from its genuine
allocator, before all packet ranks and relative slots are physically written.
The three dictionaries here are primitive book-column, count, and boundary inputs. -/
theorem site_cursor_facts (m : Memory w) (low : (A).Lower w) (fit : (A).finish < 2^w)
    (sites : Fin S.sites → Site) (f : ∀ i, DescentTerminalLocalPortBook.Room (sites i) G V M K)
    (labels : ∀ i,(sites i).Name → Word a) (refs : ∀ i,(sites i).Arg → Word a)
    (wp : 0<W) (perSite : ∀ i,(sites i).rows q ≤ W)
    (paid : purchased W (counts (q:=q) sites) ≤ S.terminal.rows) (counter : S.terminal.rows+W < 2^w)
    (boundaryRoom : (A).boundaries+((A).rows+1) ≤ (A).start)
    (issued : Book.Issued (A).parts (fun i => issue (sites i) (f i) (labels i) (refs i)) m)
    (countsROM : ∀ j : Fin (Book.Bytes G V M K a),(A).countTable.read m (j.val : Word w) = DescentTerminalLocalPortBook.countTable q j)
    (boundaryROM : ∀ j : Fin ((A).rows+1),m ((A).boundaries+j.val) = (DescentTerminalBinPackCheap.boundaries w W (A).rows)[j.val]'j.isLt)
    (poolRows : S.terminal.pool ≤ S.terminal.rows) (r : Fin S.terminal.pool) :
    (L).directory.span.Facts sites r perSite (Suffix.sockets S L ((A).mount m)) :=
  (A).issued_socket_owner S.sites_pos m low fit sites f labels refs wp perSite paid counter boundaryRoom
    issued countsROM boundaryROM (r.castLE poolRows)

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
