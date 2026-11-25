import OAI.Hierarchy.DescentTerminalFullPins
import OAI.Hierarchy.ProtocolRAMCheapCode
import OAI.Hierarchy.DescentExteriorAppendedWords

namespace OAI
/-! # Observations of the whole guest procedure on a finite binary input -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory
open ThreeFlat.Diagonal ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM
open scoped Fin.CommRing

structure Flight {w:ℕ} {T Ext Candidate:Type} (Q:Procedure w) (S0 ticks:ℕ)
    (pins:Fin S0×Fin (w+1)→(Ext⊕Candidate)⊕Bool) (outer:Ext→Bool) (paint:Candidate→Bool)
    (header:ℕ→Word w) (output:Memory w) (seedFlag exteriorFlag deadBits:ℕ)
    (reading:Option T) (exponent:T→ℕ) : Prop where
  pins_at : ∀i,Sum.elim (Sum.elim outer paint) id (pins i)=TraceWords.bits (TraceBanks.wide (header i.1.val)) i.2
  executed : Q.Exec (initialMemory S0 header) output ticks
  cheap : CheapCode Q
  admitted : (output seedFlag=0 ∧ output exteriorFlag=0) ↔ ∃c,reading=some c
  seed : ∀c,reading=some c→ output deadBits=(exponent c:Word w)

theorem appended_as_input {w:ℕ} (front extra:ℕ) (words trailer:Memory w) :
    initialMemory (front+extra) (DescentExteriorShelf.Root.appended front extra words trailer)=
      DescentExteriorShelf.Root.appended front extra words trailer := by
  funext address
  by_cases inside:address<front+extra <;>
    simp [DescentExteriorShelf.Root.appended,initialMemory,inside]

end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
