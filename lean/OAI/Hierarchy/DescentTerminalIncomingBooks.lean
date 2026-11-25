import OAI.Hierarchy.DescentTerminalPlacedRead
import OAI.Hierarchy.DescentTerminalRouteTablesRead

namespace OAI
/-! # The signed input books survive the literal, index and meter startup before row planning -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalVertexFields DescentTerminalLocalPortBook
open DescentTerminalSpanBook ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
variable {blocks v B bw G V₀ M D a W q:ℕ} (V:Home.Format) (S:Shape) (I:Input) (R:MaskAllocation.Channels blocks)
variable (start header:ℕ) (short:v*span V.publicArity V.roles V.privateWords V.nodes V.addresses V.piece≤B)
variable (literal:DescentTerminalEmitter.Compact.Literals I.sources)
local notation "loaded" => input V S I R start header short literal
local notation "n" => S.terminal.rows

theorem incoming_books (m:Memory bw) (tape:Fin S.sites→Book G V₀ M D a)
    (parts:∀f:Fin 6,(I.parts f).source.base+(I.parts f).source.size≤ start ∧
      (I.parts f).weights.base+(I.parts f).weights.size≤ start)
    (totals:I.totals.base+I.totals.size≤ start) (boundary:I.boundaries+(n+1)≤ start)
    (modulo:I.modulo.base+I.modulo.size≤ start)
    (issued:Book.Issued I.parts tape m)
    (countWords:∀j:Fin (Book.Bytes G V₀ M D a),I.totals.read m (j.val:Word bw)=countTable q j)
    (boundaries:∀j:Fin (n+1),m (I.boundaries+j.val)=(DescentTerminalBinPackCheap.boundaries bw W n)[j.val])
    (modWords:∀i:Fin n,I.modulo.read m (i.val:Word bw)=((i.val%W:ℕ):Word bw)) :
    Book.Issued I.parts tape (loaded m) ∧
    (∀j:Fin (Book.Bytes G V₀ M D a),I.totals.read (loaded m) (j.val:Word bw)=countTable q j) ∧
    (∀j:Fin (n+1),(loaded m) (I.boundaries+j.val)=(DescentTerminalBinPackCheap.boundaries bw W n)[j.val]) ∧
    (∀i:Fin n,I.modulo.read (loaded m) (i.val:Word bw)=((i.val%W:ℕ):Word bw)) := by
  have keep (b:Bank) (h:b.base+b.size≤ start) (u:Word bw): b.read (loaded m) u=b.read m u :=
    input_frame V S I R start header short literal m (.inl
      ((Nat.add_lt_add_left (Nat.mod_lt u.val (Nat.two_pow_pos _)) _).trans_le h))
  exact ⟨⟨fun i f=>(keep _ (parts f).1 _).trans (issued.source i f),
      fun f j=>(keep _ (parts f).2 _).trans (issued.values f j)⟩,
    fun j=>(keep _ totals _).trans (countWords j),
    fun j=>(input_frame V S I R start header short literal m
      (.inl ((Nat.add_lt_add_left j.isLt _).trans_le boundary))).trans (boundaries j),
    fun i=>(keep _ modulo _).trans (modWords i)⟩

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
