import OAI.Hierarchy.DescentDepotPage
import OAI.Hierarchy.DescentTerminalChipBootPins
import OAI.Hierarchy.DescentExteriorShelf
import OAI.Hierarchy.DescentTerminalPlacedCapacity

namespace OAI
/-! # Physical bounds for the four original data columns and six immutable chip tables -/
namespace Hierarchy.DescentTerminalChipBootWords
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentTerminalBinReaddress DescentTerminalDenseWindow
open scoped Classical BigOperators
variable (K W q p codes base:ℕ)
local notation "d" => q*(W*p)
local notation "c" => DescentTerminalBinFormat.controlBits W q
local notation "R" => 2^d
local notation "m" => Menus q (W*p)

theorem end_le (i:Fin 10) :
    (bank K W q p codes base i).base+(bank K W q p codes base i).size≤base+total K W q p codes := by
  let s:=fun f:Fin 10=>2^(bits K W q p codes f)
  have bound: (∑f:Fin 10,((if f < i then s f else 0)+(if f=i then s i else 0)))≤∑f:Fin 10,s f := by
    apply Finset.sum_le_sum
    intro f _
    by_cases same:f=i
    · subst f;simp
    · by_cases earlier:f < i <;> simp [earlier,same]
  have core:«begin» K W q p codes i+2^(bits K W q p codes i)≤total K W q p codes:=by
    simpa [«begin»,total,s,Finset.sum_add_distrib] using bound
  change base + «begin» K W q p codes i + 2^(bits K W q p codes i) ≤ base + total K W q p codes
  omega

theorem room (h:ℕ) (dense:formatBits q (W*p)+2*d≤h/2) (route:c+sliceWidth W q p≤h/2)
    (stride:codes+1≤2^(h/2)) :
    total K W q p codes≤8*(K*W)+12*2^(h/2)+20 := by
  have table:=DescentTerminalDenseWindow.table_room (bits:=h) dense
  have input:R≤2^(h/2):=Nat.pow_le_pow_right (by decide) (by omega)
  have tags:m≤2^(h/2):=(format_room q (W*p)).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have ptr:2^c≤2^(h/2):=Nat.pow_le_pow_right (by decide) (by omega)
  have planes:2^c*2^(sliceWidth W q p)≤2^(h/2):=by rw [←pow_add];exact Nat.pow_le_pow_right (by decide) route
  have each (f:Fin 10): 2^(bits K W q p codes f)≤2*(need K W q p codes f+1) :=
    (DescentRawCablePanel.DepotRAM.ceilPage _).2
  have sum_:=Finset.sum_le_sum (fun f (_:f∈Finset.univ)=>each f)
  change total K W q p codes≤_ at sum_
  refine sum_.trans ?_
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Nat.add_zero, Fin.val_zero,Fin.val_succ,need,Nat.zero_add,Nat.reduceAdd]
  omega

end Hierarchy.DescentTerminalChipBootWords

end OAI
