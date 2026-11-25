import OAI.Computability.BorderVNP.FiniteProfilePublishedLabels
import OAI.Computability.BorderVNP.CubeRoutePackedExteriorLayouts

/-! # One common delivery traffic array across positive finite exteriors -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal

open VPVNP BurstRAM Crossing RoutingISA RoutingISA.Evaluator Packing.Directory
open BorderVNP.Cube Cube.Physical Cube.MeanChoice Cube.LabelIndex
open scoped Classical

private theorem transfer_rows {D C : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)
    (cell : N.Site → Fin C) (r q : List Row) (same : r=q) (dest : Fin r.length → Fin C)
    (named : ∀ i,(dest i).val=r[i.val].cell) (l : LabelIndex.Layout) (m : ℕ → ℕ)
    (cn : l.cells=C) (ep : Endpoints l m) :
    (∃ (count : l.cells=C) (endpoints : Endpoints l m) (edges : N.CrossingEdge cell ↪ Fin l.cableCount)
      (data : Fin q.length ≃ Fin l.deliveryCount) (recv : Fin q.length → Fin C),
      (∀ i,(recv i).val=q[i.val].cell) ∧ RowPlacement (networkRows N cell recv (fun i => q[i.val].width))
        (fromTables l m endpoints) (finCongr count.symm) (edges.sumMap data.toEmbedding)) →
    ∃ (edges : N.CrossingEdge cell ↪ Fin l.cableCount) (data : Fin r.length ≃ Fin l.deliveryCount),
      RowPlacement (networkRows N cell dest (fun i => r[i.val].width)) (fromTables l m ep)
        (finCongr cn.symm) (edges.sumMap data.toEmbedding) := by
  subst q
  rintro ⟨_,_,edges,data,recv,atCell,placed⟩
  have eq : dest=recv := funext fun i => Fin.ext ((named i).trans (atCell i).symm)
  exact ⟨edges,data,eq.symm ▸ placed⟩

/-- From the actual publication certificates on arbitrary team/exterior
pairs, obtain a single canonical delivery domain, receiver, width and
slot key. The count casts are the ones consumed by the native group scheduler. -/
theorem common_published_labels {D C : ℕ} {P T I : Type*} {bits : P → ℕ} [Fintype I]
    (N : Network D P bits) (cell : N.Site → Fin C) (dir : Packing.Directory.Layout) (ref : T)
    (pp lp : T → ℕ → ℕ × ℕ) (sc : I → Fin C) (id : I ↪ ℕ) (sw : I → ℕ)
    (place : ∀ u, BankPlacement dir (pp u) (lp u) I sc id sw)
    (keys : ∀ u k,(place u).key k=(place ref).key k) (bounds : dir.DestinationBounds)
    (l : T → LabelIndex.Layout) (m : T → ℕ → ℕ) (count : ∀ u,(l u).cells=C) (ep : ∀ u, Endpoints (l u) (m u)) :
    let rows := fun u => dir.directory (pp u) (lp u)
    (∀ u, ∃ (n : (l u).cells=C) (endpoints : Endpoints (l u) (m u))
      (e : N.CrossingEdge cell ↪ Fin (l u).cableCount) (a : Fin (rows u).length ≃ Fin (l u).deliveryCount)
      (v : Fin (rows u).length → Fin C), (∀ i,(v i).val=(rows u)[i.val].cell) ∧
        RowPlacement (networkRows N cell v (fun i => (rows u)[i.val].width)) (fromTables (l u) (m u) endpoints)
          (finCongr n.symm) (e.sumMap a.toEmbedding)) →
    ∃ (dest : Fin (rows ref).length → Fin C) (edges : ∀ u,N.CrossingEdge cell ↪ Fin (l u).cableCount)
      (data : ∀ u,Fin (rows ref).length ↪ Fin (l u).deliveryCount), ∀ u,
      RowPlacement (networkRows N cell dest (fun i => (rows ref)[i.val].width)) (fromTables (l u) (m u) (ep u))
        (finCongr (count u).symm) ((edges u).sumMap (data u)) := by
  intro rows placed
  obtain ⟨_,_,_,_,dest,base,_⟩ := placed ref
  have same (u : T) : rows ref = rows u := ((place u).directory_eq (place ref) (keys u) bounds).symm
  choose e a localRows using fun u => transfer_rows N cell (rows ref) (rows u) (same u) dest base (l u) (m u)
    (count u) (ep u) (placed u)
  exact ⟨dest,e,fun u => (a u).toEmbedding,localRows⟩

end FiniteDiagonal

end BorderVNP
end Computability
end OAI
