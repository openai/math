import OAI.Computability.BorderVNP.PackedHistoryRouteRows
import OAI.Computability.BorderVNP.CoverDeckProductKey
import OAI.Computability.BorderVNP.PackedLookup

/-! # Numbering the actual final cells from the returned integral site routes

A fixed public table numbers the finite product cover. Each site submits its
returned quaternion residue as a sparse lookup key. There is one table row per
actual product tile, including tiles with no final sites. No rectangular table
over the much larger binary quaternion key space is allocated.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.TerminalCells

open Crossing Cover Cover.AddressCircuit Shortening Shortening.PublicCapacity
open PackedHistogram ParseBatchSort ParseBatchCounts VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open scoped Classical

variable {D q d V E w C b : ℕ} {I : Type} [Fintype I] (enum : Fin q ≃ I)
    (number : (I → Deck (d+1)) ≃ Fin C) (fit : C ≤ 2^b)

private def query {Move : Type*} (v : Fin V) (j : Fin (keyWidth q (d+1))) :
    Expr (RouteRows.Pins Move q (d+1) V E w) :=
  .input (.inr (.inr (.inl (v,(keySlots q (d+1)).symm j))))

/-- The public owner table is indexed by the encoded residue, with its real
finite cell ordinal as payload. -/
noncomputable def frame (Move : Type*) [Fintype Move] :
    Frame (RouteRows.Pins Move q (d+1) V E w) (Fin V × Fin b) :=
  PackedLookup.lookup (layout (Fin q → Deck (d+1)) (Fin V)) (productKey q (d+1))
    (fun a => fixed ((number (a ∘ enum.symm)).castLE fit)) query

variable {P K : Type*} {bits : P → ℕ} (N : Pack D P bits K) {L : ℝ} (r : SiteRoutes N I d L)
    {S : Shape} (rows : Rows S N.layout) (dummy : Fin S.edges → N.layout.Site)
    (x : RouteRows.Pins (allowedMoves I L) q (d+1) S.sites S.edges w → Bool)
    (ready : RouteRows.Ready enum N r rows dummy x)

include ready in
/-- Site ownership is the public ordinal of the original terminal integral route
reduced modulo its actual final cover level. -/
theorem owner_value (v : N.layout.Site) :
    value (fun j => (frame enum number fit (allowedMoves I L)).eval x (rows.site v,j)) =
      (number (reduceMove d (r.origin v))).val := by
  let tile : Fin q → Deck (d+1) := fun i => r.origin v (enum i)
  have key : wordValue x (query (rows.site v)) = (productKey q (d+1) tile).val := by
    change value (fun j => x (.inr (.inr (.inl (rows.site v,(keySlots q (d+1)).symm j))))) = _
    have encoded : (fun j => x (.inr (.inr (.inl (rows.site v,(keySlots q (d+1)).symm j))))) =
        keyWord q (d+1) tile := funext fun j => ready.origins v _
    rw [encoded]
    rfl
  have chosen := PackedLookup.lookup_value (layout (Fin q → Deck (d+1)) (Fin S.sites))
    (productKey q (d+1)) (fun a => fixed ((number (a ∘ enum.symm)).castLE fit)) query x
    (rows.site v) tile key
  have canonical : tile ∘ enum.symm = reduceMove d (r.origin v) := by
    funext i
    simp [tile,reduceMove]
  simpa only [frame,fixed_value,canonical,Fin.val_castLE] using chosen

omit [Fintype I] in
/-- The lookup cost depends on the cell and site counts, plus their binary sort
and encoding widths. -/
theorem frame_size (Move : Type*) [Fintype Move] :
    let h := Nat.clog 2 (C+V)
    let k := keyWidth q (d+1)
    (frame (V:=V) (E:=E) (w:=w) enum number fit Move).size ≤
      2^h*((k+1+b)+((b+h)+1+k)+h^2*(24*((b+h)+1+k)+1)+b*(60*k+16*b+33)+h^2*(24*(b+h)+1)) := by
  have equivalent : (Fin q → Deck (d+1)) ≃ Fin C := (Equiv.arrowCongr enum (Equiv.refl _)).trans number
  have card := Fintype.card_congr equivalent
  rw [Fintype.card_fin] at card
  have bounds := queries_size (layout (Fin q → Deck (d+1)) (Fin V)) (fun z => fixed (productKey q (d+1) z))
    (fun z => fixed ((number (z ∘ enum.symm)).castLE fit)) (query (Move:=Move) (E:=E) (w:=w)) 1
    (by decide) (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
  simpa only [frame,PackedLookup.lookup,Nat.mul_one,card,Fintype.card_fin] using bounds

end PackedHistoryCircuit.TerminalCells

end BorderVNP
end Computability
end OAI
