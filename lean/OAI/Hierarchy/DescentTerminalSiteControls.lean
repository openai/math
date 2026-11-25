import OAI.Hierarchy.DescentTerminalSiteCursorFacts
import OAI.Hierarchy.DescentTerminalSiteControlBanks
import OAI.Hierarchy.DescentTerminalSuffixFits
import OAI.Hierarchy.DescentTerminalRowFrames
import OAI.Hierarchy.DescentTerminalReachedPanels

namespace OAI
/-! # Physical primitive decoding controls on the same memory as the terminal emitter -/
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

open DescentTerminalSiteShelves
variable {blocks B t hN nN aN wid verts : ℕ}

/-- The row allocator, endpoint sorter and packet-slot writer preserve every scalar
control page assigned before their common public arena. -/
theorem sockets_prior (F : MaskedShelf blocks) (m : Memory w) (bounds : Suffix.Fits S L F w)
    {j : ℕ} (early : j < base) : Suffix.sockets S L ((A).mount m) j=m j := by
  have band (k : ℕ) : j < (A).atBand k :=
    early.trans_le (Nat.le_add_right base (k*(A).stride))
  have rowLow : DescentTerminalRowPlan.Lower (A).row j :=
    ⟨band 9,band 7,band 6,band 5,band 4,band 3⟩
  have output : j < DescentTerminalPacketSlotRAM.out (A).order S.packets S.sites :=
    ((band 17).trans_le (Nat.le_add_right ..)).trans_le (Nat.le_add_right ..)
  let mounted := (A).mount m
  let planned := DescentTerminalRowPlan.result (A).row S.sites S.terminal.rows mounted
  let pos := DescentTerminalSiteOffsets.result (A).offset S.sites planned
  change DescentTerminalPacketSlotRAM.after (A).order S.packets S.sites
    (DescentTerminalExteriorPackets.sorted (A).homes (A).order S.sites S.packets S.sites_pos pos) j = m j
  rw [DescentTerminalPacketSlotRAM.retained _ _ _ _ _ (.inl output),
    DescentTerminalExteriorPackets.sort_before (A).homes (A).order S.sites S.packets pos S.sites_pos bounds.sort (band 14)]
  exact (DescentTerminalSiteOffsets.early (A).offset S.sites planned (band 13)).trans
    ((DescentTerminalRowPlan.before_publishing (A).row mounted bounds.allocator rowLow (band 2)).trans
      ((A).mount_before m early))

theorem site_controls (m : Memory w) (low : (A).Lower w) (fit : (A).finish < 2^w)
    (sites : Fin S.sites → Site) (f : ∀ i, DescentTerminalLocalPortBook.Room (sites i) G V M K)
    (labels : ∀ i,(sites i).Name → Word a) (refs : ∀ i,(sites i).Arg → Word a)
    (wp : 0 < W) (perSite : ∀ i,(sites i).rows q ≤ W)
    (paid : purchased W (counts (q:=q) sites) ≤ S.terminal.rows)
    (boundaryRoom : (A).boundaries+((A).rows+1) ≤ (A).start)
    (issued : Book.Issued (A).parts (fun i => issue (sites i) (f i) (labels i) (refs i)) m)
    (countsROM : ∀ j : Fin (Book.Bytes G V M K a),(A).countTable.read m (j.val : Word w) = countTable q j)
    (boundaryROM : ∀ j : Fin ((A).rows+1),m ((A).boundaries+j.val) = (DescentTerminalBinPackCheap.boundaries w W (A).rows)[j.val]'j.isLt)
    (poolRows : S.terminal.pool ≤ S.terminal.rows)
    (F : MaskedShelf blocks) (bounds : Suffix.Fits S L F w)
    (bankLow : ∀j,(I.directory j).base+(I.directory j).size ≤ base)
    (banks : DescentTerminalControlProgram.Reads q W B verts sites I.directory m)
    (data : Fin S.sites→Home (q:=q) (t:=t) (H:=hN) (N:=nN) («A»:=aN) (w:=wid) (V:=verts))
    (population : ∀i,(data i).1.val=(sites i).nodes) :
    Controls (B:=B) (n:=S.terminal.pool) (L).directory (Suffix.sockets S L ((A).mount m)) sites perSite data := by
  have cap:=site_cursor_word_room S I base fit sites wp paid
  have heads:=banks.transfer (n:=Suffix.sockets S L ((A).mount m)) (fun j x=>
    sockets_prior S I base O F m bounds
      ((Nat.add_lt_add_left (Nat.mod_lt x.val (Nat.two_pow_pos _)) _).trans_le (bankLow j)))
  refine ⟨fun r=>site_cursor_facts S I base O m low fit sites f labels refs wp perSite paid cap boundaryRoom
    issued countsROM boundaryROM poolRows r,heads.ports,?_,heads.first,heads.skip,heads.countROM,heads.modeROM,
    heads.skipROM,heads.wordROM⟩
  intro i
  rw [population]
  exact heads.nodes i

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
