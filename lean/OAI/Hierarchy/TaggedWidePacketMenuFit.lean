import OAI.Hierarchy.ProbeFixedWidePacketFields
import OAI.Hierarchy.TaggedWireStripPacketBanks
import OAI.Hierarchy.TaggedWidePacketWantedCost

namespace OAI
/-! # Bank residency of every actual gathered field on both packet templates -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open LinearAlgebra.SpectralBooks ChordGraph AdaptiveProbe Strip ProbeStage.CoreBoard.HistoryRoles
open WireTelescope StripPaths ChosenPackets.RowRouting PacketTurns
open scoped Classical
variable {S : ProbeStage.PurchaseSampler} {h d k n D W out : ℕ} {A B : Type} [Fintype A] [Fintype B]
local notation "C" => TreeColumn n
local notation "X" => TreeSite n k
local notation "R" => ColumnWires.Role C (Fin n) (A⊕B) k
local notation "T" => TreeLink n k
local notation "U" => R⊕T
variable (p : StripPorts S h d k (TreeColumn n) (Fin n) B)
    (extra : A⊕B→DistinctPair (TreeSite n k))
    (b : Board) (shift : ℕ) (site : TreeSite n k→Expr) (stock : A→Expr)
    (qty : (ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k ⊕ TreeLink n k)→Expr)
local notation "enum" => treeFirst R T
local notation "pr" => readPrimary stock shift (p.primary b)
local notation "ma" => emitterMate (A:=A) p b shift
local notation "tr" => emitterTree (A:=A) p b shift
local notation "menu" => menuInputs extra enum site pr ma tr qty

theorem StripPorts.menu_resident (src : ∀r:R,(p.primary b r).Fits W out) (sites : ∀x,(site x).Fits W out)
    (stored : ∀a,(stock a).Fits W out) (quantity : ∀u,(qty u).Fits W out) : (menu).Resident W out := by
  have pf (r : R) : (pr r).Fits W out := by
    cases r with
    | catalyst c j=>exact ⟨trivial,src (.catalyst c j)⟩
    | radius c j l=>exact ⟨trivial,src (.radius c j l)⟩
    | cross c j l m=>exact ⟨trivial,src (.cross c j l m)⟩
    | horizontal e l=>exact ⟨trivial,src (.horizontal e l)⟩
    | extra e=>cases e with
      | inl u=>exact stored u
      | inr v=>exact ⟨trivial,src (.extra (.inr v))⟩
  have mf (c : C) (j : Fin k) : (ma c j).Fits W out:=⟨trivial,src (.radius c j true)⟩
  have tf (t : T) : (tr t).Fits W out:=⟨trivial,src (treeRole n k t)⟩
  refine ⟨fun i v=>face_resident site sites _ v,fun i=>quantity _,?_,?_⟩
  · intro i j;exact routed_resident extra site sites _ _ _ pf mf tf _ _
  · intro i j v
    exact routed_resident extra site sites _ _ _ (fun _=>face_resident site sites _ v)
      (fun _ _=>face_resident site sites _ v) (fun _=>face_resident site sites _ v) (enum i) j.val

theorem StripPorts.catalogueControls_fits (M originalRows start shelfSize bits : ℕ) (siteBase : Bank) (participant : X)
    (src : ∀r:R,(p.primary b r).Fits W out) (sites : ∀x,(site x).Fits W out)
    (stored : ∀a,(stock a).Fits W out) (quantity : ∀u,(qty u).Fits W out)
    (room : ∀f : Fin 3,(DatedRoleSheets.bank originalRows start shelfSize bits f).Fits W out)
    (stride : siteBase.Fits W out) (f : Fin ((M*3)*5+D)) :
    (p.catalogueControls extra b shift site stock qty M originalRows start shelfSize bits siteBase participant f).Fits W out := by
  apply Operands.controls_fits _ _ (p.menu_resident extra b shift site stock qty src sites stored quantity)
    _ _ _ _ _ (sites participant)
  all_goals intro q;exact page_fits _ _ _ q (room _) stride (sites _)

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
variable {M D base w out : ℕ} (old : Fin base→Expr) (gate : Fin ((M*3)*5+D)→Expr) (before : Fin D→Expr)
theorem packetFields_fits (a : ∀i,(old i).Fits w out) (b : ∀i,(gate i).Fits w out) (c : ∀i,(before i).Fits w out) :
    ∀i,(packetFields old gate before i).Fits w out := by
  refine Fin.addCases (fun i=>?_) (Fin.addCases (fun i=>?_) (Fin.addCases (fun i=>?_) (fun i=>?_)))
  · simpa only [packetFields_pre] using a i
  · simpa only [packetFields_turn] using b (i.castAdd D)
  · simpa only [packetFields_before] using c i
  · simpa only [packetFields_after] using b (Fin.natAdd ((M*3)*5) i)
end Hierarchy.ProtocolRAM.Calendar.WideCPU

end
end OAI
