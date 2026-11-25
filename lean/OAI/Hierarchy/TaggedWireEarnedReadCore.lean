import OAI.Hierarchy.TaggedWireEarnedPlacementCore
import OAI.Hierarchy.TaggedWireEarnedPhysical
import OAI.Hierarchy.TaggedWireStripPacketReads

namespace OAI
/-! Every native strip operand reads its entry in the physical paid/retained matrix. -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard AdaptiveProbe Strip
open WireTelescope StripPaths PacketTurns ChosenPackets
open LinearAlgebra.SpectralBooks ChordGraph
open scoped Classical Fin.CommRing
variable {S : PurchaseSampler} {h d k n K w Rn : ℕ} {A B Ball : Type} [Fintype A] [Fintype B]
local notation "C" => TreeColumn n
local notation "X" => TreeSite n k
local notation "R" => ColumnWires.Role C (Fin n) (A⊕B) k
local notation "T" => TreeLink n k
local notation "U" => R⊕T
local notation "G" => Commodity (Fin (2^h)) (Stages h d) k
local notation "shift" => Fintype.card G

def EarnedWords (ports : StripPorts S h d k C (Fin n) B) (b : Board) (π : Equiv.Perm (Fin (2^h)))
    (extra : A⊕B→DistinctPair X) (place : Ball×X↪Fin K) (u : Ball)
    (endRow : Fin b.rows→Site h d k×Site h d k) (name : Site h d k↪Fin K) (pad : Chord K)
    (addr : A→G) (site : X→Expr) (stored : A→Expr) (qty : U→Expr)
    (enum : Fin Rn≃U) (bits : Fin Rn→ℕ) (m : Memory w) (reg : Word w) : Prop :=
  ∃idx : R→Fin b.rows, ∃mate : C→Fin k→Fin b.rows,
    let pr:=primaryRow (b:=b) (fun a=>stockRow (p:=b.rows) (stockOrder h d k (addr a))) (Fin.natAdd shift) idx
    let ma:=fun c j=>Fin.natAdd shift (mate c j)
    let tr:=fun j:T=>Fin.natAdd shift (idx (treeRole n k j))
    let target:=Sum.elim (links (horizontal n) extra place u pr ma) (fun j=>[tr j]) ∘ enum
    let own:=Sum.elim (reportedRole place (ColumnWires.ends (horizontal n) extra) u)
      (reportedRole place (treeEnds n k) u) ∘ enum
    Reads own (installedRows π endRow name pad) target bits
      (packetInputs extra place u pr ma tr enum site (readPrimary stored shift (ports.primary b))
        (emitterMate (A:=A) ports b shift) (emitterTree (A:=A) ports b shift) qty) m reg

omit [Fintype A] [Fintype B] in
theorem EarnedPlacement.packet (ports : StripPorts S h d k C (Fin n) B) (b : Board)
    (π : Equiv.Perm (Fin (2^h))) (extra : A⊕B→DistinctPair X) (place : Ball×X↪Fin K) (u : Ball)
    (endRow : Fin b.rows→Site h d k×Site h d k) (name : Site h d k↪Fin K) (pad : Chord K)
    (addr : A→G) (site : X→Expr) (stored : A→Expr) (qty : U→Expr)
    (enum : Fin Rn≃U) (bits : Fin Rn→ℕ) (m : Memory w) (reg : Word w)
    (lookup : Fin b.coreRows≃Edges S h d k) (loaded : CoreLookup.Loaded ports.directory lookup m)
    (wide : b.rows<2^w) (col : C → Columns h d)
    (placed : EarnedPlacement ports b m reg col extra endRow)
    (core : ∀f,endRow (b.coreIndex (lookup.symm f))=CoreBoard.ends π f)
    (mapped : ∀x,place (u,x)=name (Prod.map col id x))
    (goods : ∀a,commodityEnds π (addr a)=(Prod.map col id (extra (.inl a)).left,Prod.map col id (extra (.inl a)).right))
    (room : K≤2^w) (mounted : ∀x,(site x).eval m reg=((place (u,x)).val:Word w))
    (held : ∀a,(stored a).eval m reg=(PurchaseInventory.slot (addr a):Word w))
    (amount : ∀i,(qty (enum i)).eval m reg=(bits i:Word w)) :
    EarnedWords ports b π extra place u endRow name pad addr site stored qty enum bits m reg := by
  obtain ⟨cols,idx,mate,atIndex,atMate,hor,birth⟩:=placed
  refine ⟨idx,mate,?_⟩
  dsimp only
  apply ports.packet_reads (extra:=extra) (place:=place) (u:=u) (b:=b) («shift»:=shift)
    (phys:=installedRows π endRow name pad) m reg lookup loaded wide π col cols endRow core hor birth
    name mapped _ idx mate _ atIndex atMate (installed_paid π endRow name pad) site stored qty enum bits room mounted _ amount
  · intro a
    apply installed_stock π endRow name pad place u (fun a=>extra (.inl a)) a (addr a)
    · rw [mapped,goods]
    · rw [mapped,goods]
  · exact held

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
