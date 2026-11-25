import OAI.Hierarchy.DescentTerminalPreflightRooms
import OAI.Hierarchy.DescentTerminalNativePlacedPorts

namespace OAI
/-! # The terminal input descriptor built from the preflight's actual output banks -/
namespace Hierarchy.DescentTerminalPreflightSpace.Spec
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalCompiledPrefix DescentTerminalRowArena
open DescentTerminalEmitter.Compact DescentTerminalPaidHeaderEvents DescentTerminalHeaderDraft
open DescentTerminalDenseHeaderBoot DescentTerminalScalarPadded DescentTerminalDenseHeader DescentTerminalDenseWindow
open DescentTerminalCompiledPrefix.AddressPlan.HeaderColumns
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
variable (x : Spec) (begin_ rom q grain : ℕ) (peer : Bank) (old : Fin x.scalar.blocks→Fin (2*x.cap)→Bank)
    (total modulo homes : Bank) (boundary : ℕ)
local notation "priv" => (x.cables begin_ peer old).printer
local notation "pub" => (x.publicWidths begin_).widthLayout
local notation "A_" => x.draft begin_ total modulo homes boundary
local notation "lit" => literals (x.literalBase begin_) x.paidRows
local notation "tab" => DescentTerminalHeaderDraft.output A_
variable (cfg : DescentTerminalCompiledPrefix.Shape) (other : AddressPlan.Input)

/-- The two emitted width streams share the same four arithmetic tables. The old
public-sort references, candidate bits and archived count layout keep their input locations. -/
def chipInput : AddressPlan.Input :=
  { other with
    parts:=x.parts begin_,totals:=total,modulo:=modulo,homes:=homes,boundaries:=boundary,
    directory:=x.directory begin_,sources:=columns lit tab (fun _=>.attained (lit).zero),
    indexEvents:=cfg.terminal.rows,formatEvents:=cfg.terminal.rows,
    blank:=(formatIndex q grain (DescentTerminalScalarPadded.blank q grain)).val,
    cable:=sources q grain rom (priv).output,
    exterior:=sources q grain rom (pub).output }

local notation "I_" => chipInput x begin_ rom q grain peer old total modulo homes boundary cfg other

theorem chip_uses : Uses lit tab (I_).sources := by
  intro j hj
  exact ite_eq_left hj

/-- The real width producers can choose their four result banks independently.
Their five input references already match the later flight. -/
theorem same_width_sources (rem whole idx ctl : Bank) :
    inputBanks (DescentTerminalDenseHeaderBoot.layout q grain rom (priv).output rem whole idx ctl)=(I_).cable ∧
    inputBanks (DescentTerminalDenseHeaderBoot.layout q grain rom (pub).output rem whole idx ctl)=(I_).exterior :=
  ⟨rfl,rfl⟩

private theorem width_before (l : DescentTerminalWidthRowsRAM.Layout) :
    l.output.base+l.output.size≤l.stop := by
  change l.sink ≤ l.sink+1+l.groups+l.groups
  omega

theorem ports_before (romTop : rom+extent q grain≤x.literalBase begin_) :
    (∀j,((I_).cable j).base+((I_).cable j).size≤x.literalBase begin_) ∧
      (∀j,((I_).exterior j).base+((I_).exterior j).size≤x.literalBase begin_) := by
  have privateStop := x.cable_end begin_ peer old
  have privateLow : x.cableEnd begin_≤x.literalBase begin_ := (x.layers begin_).2.2.2.2.2.2.1
  exact ⟨source_ends q grain rom _ ((width_before priv).trans (privateStop.le.trans privateLow)) romTop,
    source_ends q grain rom _ (width_before pub) romTop⟩

/-- The header operands refer to existing banks and buy no extra compact ROM words. -/
theorem header_rom_bound : wordsBought (I_).sources=0 := by
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj:j.val<24 <;> simp [chipInput,columns,hj,size]

end
end Hierarchy.DescentTerminalPreflightSpace.Spec

end OAI
