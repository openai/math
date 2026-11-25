import OAI.Hierarchy.DescentTerminalPlacedCurrent
import OAI.Hierarchy.DescentTerminalTrailingCensus

namespace OAI
/-! # Physical observation addresses at the end of the terminal program -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open DescentTerminalChipRuntime DescentTerminalLast DescentTerminalVertexFields
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM

variable {blocks : ℕ} (V : Home.Format) (cfg : Shape) (I : Input)
    (R : MaskAllocation.Channels blocks) (start header seedAt : ℕ)

theorem readout_seed_below (u : Unit) :
    (observationColumns V cfg I R start header seedAt).seed u < last V cfg I R start := by
  let base := afterMeter V cfg R start
  let C := meter V R start
  let capacity := cohortSize (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords) (N:=V.nodes)
    (A:=V.addresses) (w:=V.piece) (groups:=V.groups) (blocks:=blocks)
  have prior : (registers V cfg R start header).deadBits < base := by
    change C.base+capacity+cfg.sites+cfg.sites+2 < C.base+capacity+cfg.sites+cfg.sites+3
    omega
  obtain ⟨pages,shelf,flight,issue,paid⟩ := stages cfg I base
  exact prior.trans_le (((rowArena cfg I base).start_le 22).trans
    (pages.trans (shelf.trans (flight.trans (issue.trans paid)))))

theorem readout_locations (scanRows : ℕ) (chipFits : scanRows ≤ (chip cfg I (afterMeter V cfg R start)).width)
    (count : 0 < cfg.terminal.plane.headerRows) :
    let cols := observationColumns V cfg I R start header seedAt
    let cpu := chip cfg I (afterMeter V cfg R start)
    let limit := last V cfg I R start
    cols.whole.base < limit ∧ cols.tail.base < limit ∧ cols.exteriorFlag < limit ∧
      cpu.xCheck+scanRows < limit ∧ cpu.yCheck+scanRows < limit := by
  let base := afterMeter V cfg R start
  let O := registers V cfg R start header
  let cpu := chip cfg I base
  let plane := cfg.terminal.plane
  let origin := takeOff cfg I base
  let H := DescentExteriorShelf.span plane.headBits plane.restBits plane.bitLanes plane.exteriors
  have ahead : cpu.first ≤ last V cfg I R start := (stages cfg I base).2.2.2.2
  have before : origin+24*H ≤ cpu.first := by
    apply le_trans (b := DescentTerminalDataPlane.Arena.finish plane origin)
    · change origin+24*H ≤ origin+24*H+_+_+4*_+4*_
      omega
    · exact (stages cfg I base).2.2.2.1
  have n := DescentExteriorShelf.row_room plane.headBits plane.restBits plane.bitLanes plane.exteriors
  change plane.exteriors*2^(plane.headBits+plane.restBits) ≤ H at n
  have pos : 0 < H := Nat.two_pow_pos _
  have flag : (observationColumns V cfg I R start header seedAt).exteriorFlag < cpu.first := by
    change origin+21*H+2*(plane.exteriors*2^(plane.headBits+plane.restBits)) < cpu.first
    omega
  have size : scanRows ≤ cpu.width := chipFits
  have keys : cpu.keys ≤ last V cfg I R start := Nat.le_add_right ..
  have checkedX : cpu.xCheck+scanRows < cpu.keys := by
    change cpu.first+cpu.width+scanRows < cpu.first+4*cpu.width+2
    omega
  have checkedY : cpu.yCheck+scanRows < cpu.keys := by
    change cpu.first+3*cpu.width+1+scanRows < cpu.first+4*cpu.width+2
    omega
  exact ⟨(eof_live cfg I base O false count).2.trans_le ahead,
    (eof_live cfg I base O true count).2.trans_le ahead, flag.trans_le ahead,
    checkedX.trans_le keys, checkedY.trans_le keys⟩

theorem readout_inputs (scanRows : ℕ) (chipFits : scanRows ≤ (chip cfg I (afterMeter V cfg R start)).width)
    (seedPrior : seedAt < last V cfg I R start) (count : 0 < cfg.terminal.plane.headerRows) :
    ∀ b ∈ ((observationColumns V cfg I R start header seedAt).tape
      (chip cfg I (afterMeter V cfg R start)) scanRows).inputs,
        b.base+b.size ≤ trailingCut (last V cfg I R start) cfg.terminal.rows := by
  let cols := observationColumns V cfg I R start header seedAt
  let cpu := chip cfg I (afterMeter V cfg R start)
  let limit := last V cfg I R start
  obtain ⟨whole,tail,exterior,x,y⟩ := readout_locations V cfg I R start header seedAt scanRows chipFits count
  have singleton {addr : ℕ} (h : addr < limit) : addr+1 ≤ trailingCut limit cfg.terminal.rows :=
    (Nat.succ_le_of_lt h).trans (Nat.le_add_right ..)
  intro b member
  simp only [Tape.inputs,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact singleton whole
  · exact singleton tail
  · exact Nat.add_le_add_right (show cpu.keys ≤ limit from Nat.le_add_right ..) (DescentDyadicSpan.span cfg.terminal.rows)
  · exact singleton seedPrior
  · exact singleton exterior
  · exact singleton x
  · exact singleton y

theorem readout_key_cap (scanRows : ℕ) (fit : cfg.terminal.pool ≤ DescentDyadicSpan.span cfg.terminal.rows) :
    cfg.terminal.pool ≤ ((observationColumns V cfg I R start header seedAt).tape
      (chip cfg I (afterMeter V cfg R start)) scanRows).keys.size :=
  fit

end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
