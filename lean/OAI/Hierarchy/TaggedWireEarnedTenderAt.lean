import OAI.Hierarchy.TaggedWireEarnedTender
import OAI.Hierarchy.ProtocolRAMPrefixAgreement

namespace OAI
/-! # Read an original installation at a later protected scatter memory -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard AdaptiveProbe Strip WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph Probe ChosenPackets RowRouting StripPaths PacketTurns
open ThreeFlat.Diagonal.MotifOuterTerms
open scoped Classical Fin.CommRing
variable {sam : PurchaseSampler} {h d k n K w : ℕ} {A B Ball : Type} [Fintype A] [Fintype B] [Fintype Ball]
local notation "C" => TreeColumn n
local notation "X" => TreeSite n k
local notation "R" => ColumnWires.Role C (Fin n) (A⊕B) k
local notation "T" => TreeLink n k
local notation "U" => R⊕T
local notation "G" => Commodity (Fin (2^h)) (Stages h d) k
local notation "shift" => Fintype.card G
variable {p : StripPorts sam h d k (TreeColumn n) (Fin n) B} {b : Board} {π : Equiv.Perm (Fin (2^h))}
    {extra : A⊕B→DistinctPair (TreeSite n k)} {place : Ball×TreeSite n k↪Fin K} {u : Ball}
    {endRow : Fin b.rows→Site h d k×Site h d k} {name : Site h d k↪Fin K} {pad : Chord K}
    {addr : A → Commodity (Fin (2^h)) (Stages h d) k} {m : Memory w} {reg : Word w}
local notation "roles" => ColumnWires.ends (horizontal n) extra
local notation "own" => Sum.elim (reportedRole place roles u) (reportedRole place (treeEnds n k) u)
local notation "enum" => treeFirst R T
local notation "order" => (Fintype.equivFin ((i : Fin (Fintype.card U)) × Fin (menuLen (enum i)))).symm

namespace EarnedInstall
variable (g : EarnedInstall p b π extra place u endRow name addr m reg)
local notation "stamp" => g.placed.2.choose_spec.choose_spec
local notation "old" => retained (b:=b) addr
local notation "fwd" => Fin.natAdd shift
local notation "pr" => primaryRow (b:=b) old fwd g.index
local notation "ma" => fun c j=>fwd (g.mate c j)
local notation "tr" => fun j:T=>fwd (g.index (treeRole n k j))
variable {F J : Type} [Field F] [Fintype J] (labels : TreeSite n k≃Fin (Fintype.card (TreeSite n k))) (req : J → ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k)
    (rt : Fin (Fintype.card (TreeSite n k))) (P : Packet F (fun e=>@DistinctPair.chord _ _ ⟨labels⟩ (ColumnWires.ends (Strip.horizontal n) extra e)) req)
    (copies : ℕ)
local notation "row" => Row.packet (stripPacket labels roles req place u rt P) copies


variable (pad : Chord K)
local notation "phys" => installedRows π endRow name pad
local notation "chosen" => g.tender labels req rt P copies pad

/-- The public sites and elected histogram are read at the processing memory.
The physical lane, mate lane and commodity balances retain their original row numbers. -/
theorem tender_reads_at (hist : Histogram (Fin P.terms) copies) (site : X→Expr) (stock : A→Expr) (qty : U→Expr)
    (out : Memory w) (cut : ℕ) (low : PrefixAgreement.Low cut out m)
    (primaryFit : ∀r:R,(p.primary b r).Fits w cut) (stockFit : ∀a,(stock a).Fits w cut)
    (room : K≤2^w) (mounted : ∀x,(site x).eval out reg=((place (u,x)).val:Word w))
    (held : ∀a,(stock a).eval m reg=(PurchaseInventory.slot (addr a):Word w))
    (amount : ∀i,(qty (enum i)).eval out reg=((Sum.elim (histWidth P.count hist)
      (fun _ : T=>copies*P.selectorBits) (enum i) : ℕ) : Word w)) :
    Reads (Installs.starts (source:=(chosen).source) (chosen).order) phys ((chosen).install.steps (chosen).order)
      (Installs.numbered (chosen).order ((chosen).bits hist)) (g.operands site stock qty) out reg := by
  have original (e : Expr) (fit : e.Fits w cut) : e.eval out reg=e.eval m reg :=
    PrefixAgreement.expr e out m cut (PrefixAgreement.inputEnd_of_fits e fit) low reg
  obtain ⟨first,second,tree⟩ := g.faces pad
  have selected (r : R) (good : paidRole r) : (p.primary b r).eval out reg=((g.index r).val:Word w) := by
    rw [original _ (primaryFit r)]
    apply Fin.ext
    exact ((stamp).1 r good).trans (Fin.val_cast_of_lt ((g.index r).isLt.trans g.wide)).symm
  have opposite (c : C) (j : Fin k) :
      (p.mate b (.catalyst c j:R)).eval out reg=((g.mate c j).val:Word w) := by
    have fit : (p.mate b (.catalyst c j:R)).Fits w cut := primaryFit (.radius c j true)
    rw [original _ fit]
    apply Fin.ext
    exact ((stamp).2.1 c j).trans (Fin.val_cast_of_lt ((g.mate c j).isLt.trans g.wide)).symm
  have heldAt (a : A) : (stock a).eval out reg=((old a).val:Word w) :=
    (original _ (stockFit a)).trans (held a)
  apply inputs_read extra place u phys pr ma tr enum site _ _ _ qty _ out reg room mounted amount
    (read_primary b shift stock (p.primary b) old g.index out reg heldAt selected)
  · intro c j
    simp [emitterMate,PacketScan.add_eval,opposite c j,Expr.eval,Nat.cast_add]
  · intro t
    have paid : paidRole (treeRole n k t:R) := by rcases t with i|⟨c,j,b⟩ <;> trivial
    simp [emitterTree,PacketScan.add_eval,selected _ paid,Expr.eval,Nat.cast_add]
  · exact first
  · exact second
  · exact tree

end EarnedInstall
end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
