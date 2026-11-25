import OAI.Hierarchy.DescentTerminalTrailingCensus
import OAI.Hierarchy.DescentTerminalChipBootExtent
import OAI.Hierarchy.DescentTerminalPublicIdentity
import OAI.Hierarchy.DescentDatedExteriorSources

namespace OAI
/-! # Address width of the complete trailing census on its original input alphabet -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open DescentTerminalPreflightSpace DescentTerminalVertexFields DescentDatedAddressBook
open DescentTerminalLast DescentTerminalChipRuntime.Dated Filter
noncomputable section

/-- Column four contains one entry for each possible data word, column nine
one for each header code. The original raw rows occupy the paid payload. -/
theorem paid_columns (K W q piece codes rows publicRows : ℕ) :
    let words:=DescentTerminalPublicIdentity.total K W q piece codes rows publicRows
    rows≤words ∧ codes*2^(q*(W*piece))≤words*words :=by
  intro words
  let sizes:=DescentTerminalChipBootWords.total K W q piece codes
  have bought : sizes≤words:=by
    change sizes≤ sizes+_+_+_
    omega
  have col (i:Fin 10) : DescentTerminalChipBootWords.need K W q piece codes i≤ sizes:=by
    let k:=DescentTerminalChipBootWords.need K W q piece codes i
    have pad : k≤2^(Nat.clog 2 k):=Nat.le_pow_clog (by decide) _
    apply pad.trans
    exact Finset.single_le_sum (f:=fun j:Fin 10=>2^(DescentTerminalChipBootWords.bits K W q piece codes j))
      (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
  have data : 2^(q*(W*piece))≤ sizes:=col 4
  have header : codes+1≤ sizes:=col 9
  have raw:=DescentTerminalPrimitiveArena.covered rows
  constructor
  · change rows≤_+_+DescentTerminalPrimitiveArena.pad rows+_
    omega
  · exact Nat.mul_le_mul (by omega : codes≤words) (data.trans bought)

theorem readout_measures {blocks : ℕ} (v : Home.Format) (cfg : Shape) (I : Input)
    (R : MaskAllocation.Channels blocks) (start:ℕ) :
    start≤last v cfg I R start ∧ cfg.terminal.rows≤last v cfg I R start ∧ cfg.terminal.pool≤last v cfg I R start :=by
  let base:=afterMeter v cfg R start
  have floor : start≤base:=by
    change start≤ start+_+_+_+_+3
    omega
  obtain ⟨pages,shelf,flight,issue,paid⟩:=stages cfg I base
  have finish : endAddress cfg I base=(done_ cfg I base)+(4*2^(Nat.clog 2 cfg.terminal.rows)+2+cfg.terminal.pool) :=
    terminal_end (done_ cfg I base) cfg.terminal.rows cfg.terminal.pool
  have rows:=Nat.le_pow_clog (by decide : 1<2) cfg.terminal.rows
  exact ⟨floor.trans (((rowArena cfg I base).start_le 22).trans (pages.trans (shelf.trans (flight.trans (issue.trans paid))))),
    show cfg.terminal.rows≤endAddress cfg I base by omega,
    show cfg.terminal.pool≤endAddress cfg I base by omega⟩

theorem paid_census {blocks : ℕ} (v : Home.Format) (cfg : Shape) (I : Input)
    (R : MaskAllocation.Channels blocks) (start K W q piece codes rows publicRows : ℕ)
    (prior : DescentTerminalPublicIdentity.total K W q piece codes rows publicRows≤ start) :
    let high:=last v cfg I R start
    trailingStop (trailingCut high cfg.terminal.rows) rows cfg.terminal.pool (codes*2^(q*(W*piece)))+1≤(high+4)^2 :=by
  intro high
  obtain ⟨a,b,c⟩:=readout_measures v cfg I R start
  have enough:=prior.trans a
  obtain ⟨raw,keys⟩:=paid_columns K W q piece codes rows publicRows
  have small : rows≤high:=raw.trans enough
  have alphabet : codes*2^(q*(W*piece))≤high*high:=keys.trans (Nat.mul_le_mul enough enough)
  have trailing:=trailing_end_bound high cfg.terminal.rows rows cfg.terminal.pool (codes*2^(q*(W*piece)))
  nlinarith

theorem census_word_of_readout {blocks:ℕ} (v:Home.Format) (cfg:Shape) (I:Input)
    (R:MaskAllocation.Channels blocks) (start K W q piece codes rows publicRows h C w:ℕ)
    (prior : DescentTerminalPublicIdentity.total K W q piece codes rows publicRows≤ start)
    (room : last v cfg I R start≤2^(C*h)) (positive : 0<h) (bus : (2*C+7)*h≤w) :
    trailingStop (trailingCut (last v cfg I R start) cfg.terminal.rows) rows cfg.terminal.pool
      (codes*2^(q*(W*piece)))+1<2^w :=by
  have original:=paid_census v cfg I R start K W q piece codes rows publicRows prior
  let a:=2^(C*h)
  have ha: 0<a:=Nat.two_pow_pos _
  have bound : (last v cfg I R start+4)^2<2^((2*C+7)*h):=by
    have shift : 64≤2^(7*h):=(show 64≤2^7 by decide).trans
      (Nat.pow_le_pow_right (by decide : 0<2) (by omega))
    have eqn : 2^((2*C+7)*h)=a*a*2^(7*h):=by
      simp only [Nat.add_mul,Nat.pow_add,a,Nat.mul_assoc,Nat.two_mul]
    rw [eqn]
    have prod:=Nat.mul_le_mul_left (a*a) shift
    change last v cfg I R start≤a at room
    nlinarith [Nat.pow_le_pow_left room 2]
  exact original.trans_lt (bound.trans_le (Nat.pow_le_pow_right (by decide) bus))

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
