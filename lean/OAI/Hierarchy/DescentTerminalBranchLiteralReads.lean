import OAI.Hierarchy.DescentTerminalPlacedBookReads
import OAI.Hierarchy.DescentTerminalPlacedChipInit

namespace OAI
/-! # Five scalar literals in a single placed terminal execution -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalVertexFields DescentTerminalSiteShelves
open DescentTerminalPrintedFields DescentTerminalHeaderScatter DescentTerminalEmitter.Compact
open DescentTerminalChipBootWords
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false


variable {bw : ℕ}

/-- Four public books after routing and the scalar shift pointer before routing. -/
structure BranchLiterals (V : Home.Format) (S : Shape) (initial : Memory bw)
    (E : DescentTerminalEmitter.Layout) (banks : DescentTerminalChipRuntime.Banks)
    (verts W B piece : ℕ) (qp : 0<V.publicArity) : Prop where
  half : ∀(i : Fin S.terminal.pool) (j : Fin 2),
    E.leaf.half.read (DescentTerminalEmitter.routed S.terminal E initial) ((field i j).val:Word bw)=(i.val:Word bw)
  identity : ∀i : Fin S.terminal.pool,
    E.leaf.home.read (DescentTerminalEmitter.routed S.terminal E initial) (i.val:Word bw)=(i.val:Word bw)
  decoder : ∀j : Fin (alphabet verts W B),
    E.leaf.weight.read (DescentTerminalEmitter.routed S.terminal E initial) (j.val:Word bw)=
    (entryBy (DescentTerminalVertexFields.decode (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords) (N:=V.nodes)
      (A:=V.addresses) (w:=V.piece)) qp j:Word bw)
  headerROM : ∀j : Fin (DescentTerminalPrintedFields.capacity V.publicArity V.roles V.privateWords
      V.nodes V.addresses V.piece verts).total,
    E.leaf.table.read (DescentTerminalEmitter.routed S.terminal E initial) (j.val:Word bw)=
      ((DescentTerminalPrintedFields.headerTable V.publicArity V.roles V.privateWords V.nodes V.addresses
        V.piece verts)[j.val]'(by simp [DescentTerminalPrintedFields.headerTable]):Word bw)
  pointer : ∀j : Fin (DescentTerminalScalarHeader.range V.publicArity V.roles V.privateWords V.nodes
      V.addresses V.piece verts),
    initial (banks.scalar.pointer.base+j.val+1)=((j.val*2^(V.publicArity*(W*piece)):ℕ):Word bw)

variable {blocks v B : ℕ} (V : Home.Format) (S : Shape) (J : Input) (R : MaskAllocation.Channels blocks)
    (start header verts W : ℕ) (qp : 0<V.publicArity)
    (short : v*span V.publicArity V.roles V.privateWords V.nodes V.addresses V.piece≤B)
    (vals : Fin 43→ℕ→ℕ) {K piece : ℕ} (front empty : ℕ)
    (z : DescentTerminalChipPins.Inputs K W V.publicArity piece→Bool)
local notation "literalCols" => ScalarLiterals.columns V.publicArity V.roles V.privateWords V.nodes V.addresses V.piece
  verts W B S.terminal.pool J.sources
local notation "J₀" => ({J with sources:=literalCols} : Input)
local notation "printed" => ScalarLiterals.data V.publicArity V.roles V.privateWords V.nodes V.addresses V.piece
  verts W B S.terminal.pool qp J.sources vals
local notation "base" => afterMeter V S R start
local notation "metered" => meter V R start
local notation "em" => (layout S J₀ base (registers V S R start header)).emit
local notation "codes" => DescentTerminalScalarHeader.range V.publicArity V.roles V.privateWords V.nodes
  V.addresses V.piece verts
local notation "b₀" => chipBanks (K:=K) (W:=W) (q:=V.publicArity) (p:=piece) codes em front empty
local notation "snapshot" m => Suffix.events S (layout S J₀ base (registers V S R start header))
  (metered).layout ((rowArena S J₀ base).mount (input V S J₀ R start header short printed m))

/-- Each table is read at the original format address. The scalar pointer
for a code occupies the next word as word zero is reserved. -/
theorem branch_literal_reads (m : Memory bw) (early : Earlier S J₀ base (metered).layout bw)
    (room : last V S J₀ R start<2^bw) (before_ : front+DescentTerminalBoot.total K W V.publicArity piece codes ≤ start)
    (kept : ∀j<DescentTerminalBoot.total K W V.publicArity piece codes, m (front+j)=DescentTerminalBoot.back z bw codes j) :
    BranchLiterals V S (snapshot m) em b₀ verts W B piece qp := by
  obtain ⟨half,home,decoder,table⟩ := placed_book_reads V S J R start header V.publicArity V.roles V.privateWords
    V.nodes V.addresses V.piece verts W qp short vals m early room
  have chip:=chip_started V S J₀ R start header short printed front empty z m early room before_ kept
  refine ⟨half,home,decoder,table,fun j=>?_⟩
  have word:=chip.2.1 j.succ
  simpa [DescentTerminalScalarDispatch.pointers,Nat.add_assoc] using word

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
