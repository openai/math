import OAI.Computability.BorderVNP.DiagonalPublishedHostCables
import OAI.Computability.BorderVNP.DiagonalExternalFragmentHostWords
import OAI.Computability.BorderVNP.DiagonalRoutedSourceReports
import OAI.Computability.BorderVNP.PackedNativeDemandIntervals
import OAI.Computability.BorderVNP.CubeRouteProfileInputs

/-! # Authentic host tables on the signed receiving memories -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.Fragments

open VPVNP BurstRAM Crossing Packing Packing.CellAddresses Packing.CellAddressCircuit Packing.CellAddressPhysical
open Packing.RoutingOutputs BorderVNP.Cube Cube.Physical Cube.NativeIntervals Cube.HostScatter
open RoutingISA RoutingISA.Evaluator FiniteEvaluator ParseBatchSort PackedHistoryCircuit
open scoped Classical
set_option maxHeartbeats 1000000

variable {D R sz n d k b w geo base gap A : ℕ} {P σ : Type} [Fintype P] [Fintype σ]
    {bits : P → ℕ} (task : SignedTaskArena.Layout) (dir : Directory.Layout)

variable (N : Network D P bits) (cell : N.Site → Fin task.cube.cells) (aux : N.Site → ℕ)
    (siteID : N.Site ↪ Fin sz) (edgeID : N.Edge ↪ Fin task.cube.cables) (portID : P ↪ Fin n)
    (F : Fields sz task.cube.cables n task.cube.cells d k b σ) {old : Fin dir.entries → Fin sz} {ports : Fin A → Fin n}
    (pub : Fin (R+1) → Arg → Word w) (profile mid out : Fin (R+1) → Memory w)
    (pp lp : Fin (R+1) → ℕ → ℕ × ℕ) (x : Fin (R+1) → σ → Bool)
    (B : Fin (R+1) → BroadcastFrame) {pin : Fin (R+1) → Pins.Layout}
    (fields : ∀ u, Pins.ProcessorFields (pin u)) {guess : Fin (R+1) → ℕ → Bool}
    {input written : Fin (R+1) → ℕ → ℕ} {controls : Fin (R+1) → ℕ}

local notation3 (prettyPrint := false) "frame(" u ")" => (pub u 0).val
local notation3 (prettyPrint := false) "published(" u ")" => Directory.ISA.publish (mid u) (frame(u)) base (dir.directory (pp u) (lp u))
local notation3 (prettyPrint := false) "pr(" u ")" => privateLayout (frame(u)) geo task.cube.cables task.cube.cells dir.entries dir.description gap

variable (label : Fin task.cube.cells → Label (task.cube.n+1) task.cube.header.d)
    (owners : (Packet task.cube.n task.cube.header.d task.cube.header.blocks → Selector task.cube.n task.cube.K task.cube.h) → Fin task.cube.header.d → Fin (R+1))
    (q : NativeAssignments.Routed (b:=task.cube.b) (s:=task.cube.s) owners)
set_option quotPrecheck false in
local notation "axis" => chosen task.cube.b task.cube.s q.1
local notation3 (prettyPrint := false) "Cables" => Fintype.card (N.CrossingEdge cell)

/-- Use the actual geometry, returned private slots, published packet, chosen cable rows
and retained host directory. Each team's chooser may return its own enumeration;
strict sparse address order forces the same history-only enumeration on all teams. -/
theorem HostTables.ofPublications
    (rep : ∀ u, Represents N cell aux siteID edgeID portID F (x u)) (ids : ∀ c,(F.cells c).val=c.val)
    (fieldRoom : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^b)
    (img : ∀ u, Image F old ports (x u) geo (readings (profile u)))
    (place : ∀ u, (pr(u)).Image (readings (profile u)) dir.entries (readings (mid u)))
    (hdr : ∀ u, Header (frame(u)) geo task.cube.cables task.cube.cells dir.entries (readings (profile u)))
    (first : ∀ u, frame(u)+112 ≤ base) (reserve : base+7*dir.candidates ≤ geo)
    (endGeo : geo+5*task.cube.cables ≤ task.cube.header.header)
    (keep : ∀ u, CubeAllocation.HostRetention task.cube (frame(u)) (readings (published(u))) (written u) (readings (out u)))
    (entry : ∀ u, NativeEntry task.cube (frame(u)) (controls u) axis R (input u) (readings (published(u))) (written u))
    (source : ∀ u, ProfileRouteInputs (fields u) (B u) (pub u) (guess u) (published(u)))
    (team : ∀ u,(B u).team=u.val)
    (selected : ∀ u (c : Fin task.cube.cells), (task.cube.receivingOwner (frame(u)) axis R (input u) c.val).val =
      SignedPrep.routedOwnerWord task.cube owners label q c.val)
    (pointer : ∀ u, readings (published(u)) ((frame(u))+72)=task.cube.hostDirectory)
    {original : Fin dir.entries → N.Site}
    (capacity : ∀ c, suppliedSize N cell c+gap+(∑ j,if cell (original j)=c then dir.description else 0) ≤ task.cube.cellStride)
    (il : NativeIntervals.Layout) (count : il.count=task.cube.cables) (hz : task.cube.header.d^(task.cube.n+1)=il.alphabet)
    (scan : Fin (R+1) → ℕ → ℕ)
    (chooser : ∀ u, ∃ (before : ℕ → ℕ) (ord : N.CrossingEdge cell ≃ Fin Cables) (row : Fin Cables ↪o Fin il.count),
      (∀ e, (row (ord e)).val = (edgeID e.val).val) ∧
      PhysicalRows N cell il before ord row Fin.valEmbedding label (productCode task.cube.n task.cube.header.d il.alphabet hz) ∧
      il.Image before il.count (scan u) ∧
      ResidentRows (hostLayout pub out u) il before (scan u) (readings (out u)) task.cube.n task.cube.header.d task.cube.header.blocks task.cube.b task.cube.h task.cube.K task.cube.s) :
    ∃ (before : Fin (R+1) → ℕ → ℕ) (row : Fin Cables ↪o Fin il.count),
      HostTables (blocks:=task.cube.header.blocks) (b:=task.cube.b) (h:=task.cube.h) (K:=task.cube.K) (s:=task.cube.s)
        N cell edgeID portID il (NativeDemands.cableOrder N cell edgeID) row label axis (owners q.1) Fin.valEmbedding
        pub out task.cube.cellBank task.cube.cellStride before scan hz := by
  classical
  choose before ord row aligned physical interval resident using chooser
  have order (u : Fin (R+1)) : ord u = NativeDemands.cableOrder N cell edgeID :=
    NativeDemands.cableOrder_eq_of_aligned N cell edgeID (ord u)
      ((row u).trans (Fin.castOrderIso count).toOrderEmbedding) (fun e => Fin.ext (aligned u e))
  have rows (u : Fin (R+1)) : row u=row 0 := by
    ext i
    obtain ⟨e,rfl⟩ := (ord u).surjective i
    have h : ord u e=ord 0 e := congrFun (congrArg DFunLike.coe ((order u).trans (order 0).symm)) e
    exact (aligned u e).trans (by rw [h]; exact (aligned 0 e).symm)
  have host (u : Fin (R+1)) : readings (out u) ((frame(u))+72)=task.cube.hostDirectory :=
    ((keep u).open_frame 72 (by decide)).trans (pointer u)
  refine ⟨before,row 0,resident,fun u => ?_,interval,fun u => ?_,fun u c => ?_,fun u => ?_,fun e => ?_,fun u c => ?_,fun c => ?_⟩
  · simpa only [order u,rows u] using physical u
  · have h := (source u).broadcast.1
    have same := (keep u).open_frame 0 (by decide)
    change readings (out u) (frame(u))=u.val
    exact (by simpa only [Nat.add_zero] using same : readings (out u) (frame(u))=readings (published(u)) (frame(u))).trans
      ((by simpa only [frameField,readings,Nat.add_zero] using h : readings (published(u)) (frame(u))=(B u).team).trans (team u))
  · change readings (out u) (readings (out u) ((frame(u))+72)+2*c.val) = _
    obtain ⟨_,_,directory⟩ := (entry u).image
    obtain ⟨_,labels,weights,ownersBefore,pair,hostBefore,_,_⟩ := task.cube.writer_order
    have bound := c.isLt
    have saved := (keep u).tables (task.cube.hostDirectory+2*c.val) (by omega) (by omega)
    have owner := (directory.hostRows c.val bound).1
    rw [host u,saved,Nat.mul_comm 2 c.val,owner,selected u c]
    simp only [SignedPrep.routedOwnerWord,dite_eq_left c.isLt,Fin.valEmbedding_apply]
  · exact CableRows.ofPublished N cell aux siteID edgeID portID F (rep u) ids fieldRoom (img u)
      (pp u) (lp u) (place u) (hdr u) (first u) reserve endGeo (keep u)
  · rw [← order 0]
    exact aligned 0 e
  · change readings (out u) (readings (out u) ((frame(u))+72)+2*c.val+1)=_
    obtain ⟨_,_,directory⟩ := (entry u).image
    obtain ⟨_,labels,weights,ownersBefore,pair,hostBefore,_,_⟩ := task.cube.writer_order
    have bound := c.isLt
    have saved := (keep u).tables (task.cube.hostDirectory+2*c.val+1) (by omega) (by omega)
    rw [host u,saved,Nat.mul_comm 2 c.val,(directory.hostRows c.val bound).2]
  · exact (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans (capacity c))

end Diagonal.ExternalSew.Fragments

end BorderVNP
end Computability
end OAI
