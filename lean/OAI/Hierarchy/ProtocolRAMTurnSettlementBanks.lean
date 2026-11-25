import OAI.Hierarchy.ProtocolRAMCatalystTerminalLower

namespace OAI
/-! # Reading all five physical rank inputs after the settlement has printed its rows -/
noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive.TerminalLayout
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe Calendar Calendar.CatalogueRows RouteSettlement
open scoped Classical Fin.CommRing

variable {w r : ℕ} {I J : Type*} [Fintype I] [Fintype J]
variable (bits : ℕ) (cat : Board) (stock owners : Bank)
    {core : I→List (Fin cat.rows)} {center : J→List (Fin cat.rows)}
    (enum : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→ℕ)
local notation "b" => settlement bits stock
local notation "S" => cat.sink r b (source bits) (table bits) (destination bits) owners

theorem turn_location (c : Bank) (mem : c∈[(b).index,(b).kind,(b).stock,(b).reserved,(b).used])
    (stockFits : stock.base+stock.size≤2^bits) :
    c.base+c.size≤8*2^bits ∧ (c.base+c.size≤2^bits ∨ 4*2^bits≤c.base) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl <;>
    simp only [settlement,page,Bank.size] at * <;> omega

theorem turn_read (m : Memory w) (c : Bank) (mem : c∈[(b).index,(b).kind,(b).stock,(b).reserved,(b).used])
    (stockFits : stock.base+stock.size≤2^bits) (rowsFit : cat.rows≤2^bits) (j : Word w) :
    c.read ((S).output m enum ci cj) j=c.read m j := by
  let p:=c.base+j.val%2^c.bits
  have modlt := Nat.mod_lt j.val (Nat.two_pow_pos c.bits)
  have middle : c.base≤p ∧ p<c.base+c.size := by dsimp [p,Bank.size];omega
  obtain ⟨stop,off⟩:=turn_location bits stock c mem stockFits
  change (S).output m enum ci cj p = m p
  apply ProtocolRAM.sink_prefix
  · change p<1*2^bits ∨ 1*2^bits+cat.rows≤p
    omega
  · change p<9*2^bits
    omega
  · change p<10*2^bits
    omega
  · change p<18*2^bits
    omega

theorem turn_directory (m : Memory w) (d : Directory b m enum ci cj)
    (stockFits : stock.base+stock.size≤2^bits) (rowsFit : cat.rows≤2^bits) :
    Directory b ((S).output m enum ci cj) enum ci cj := by
  have read (c : Bank) (mem : c∈[(b).index,(b).kind,(b).stock,(b).reserved,(b).used]) (j : Word w) :=
    turn_read bits cat stock owners enum ci cj m c mem stockFits rowsFit j
  exact ⟨fun i=>(read _ (by simp) _).trans (d.headKind i),fun i=>(read _ (by simp) _).trans (d.headIndex i),
    fun i=>(read _ (by simp) _).trans (d.tailKind i),fun i=>(read _ (by simp) _).trans (d.tailIndex i)⟩

end Hierarchy.ProtocolRAM.CatalystArchive.TerminalLayout
end

end OAI
