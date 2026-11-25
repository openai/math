import OAI.Computability.BorderVNP.CellPacketGeometrySignedFields
import OAI.Computability.BorderVNP.CellPacketGeometryTerminalFeeds

/-! # The signed private packet's genuine count slots on the terminal network -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History.Native.SignedFields

open Crossing Packing Packing.Inherited FrozenTape CellSparse Packet CellAddresses CellAddressPhysical
open CellAddressCircuit ParseBatchSort VPVNP.VerifierNetwork FinalReports DiagonalTallyCellReports
open PackedHistoryCircuit.Retained
open private zero_value from OAI.Computability.BorderVNP.PackedInheritedWordCircuit

variable {a m n C k w d entries cap t q : ℕ} {σ H R B U V : Type} [Fintype σ] [Fintype H]
variable (F : Fields a m n C d k w σ) (boxes : Fin a → List (Source.Box (Fin entries))) (entry : Fin entries → Fin a)
variable (arena stride gap desc g digits : ℕ)

/-- Expose the signed real and spare report fields and all genuine original
pointers on the same two-bus input as the final site programs. -/
noncomputable def liveFrame : Frame (σ ⊕ H) (Spare.Field C g digits (Fin entries) × Fin w) :=
  lift (frame F boxes entry arena stride gap desc g digits)

@[simp] theorem liveFrame_size :
    (liveFrame (H := H) F boxes entry arena stride gap desc g digits).size =
      (frame F boxes entry arena stride gap desc g digits).size := by simp [liveFrame]

variable (x : σ → Bool) (h : H → Bool)

theorem liveFrame_eval (p : Spare.Field C g digits (Fin entries)) (j : Fin w) :
    (liveFrame F boxes entry arena stride gap desc g digits).eval (Sum.elim x h) (p,j) =
      (frame F boxes entry arena stride gap desc g digits).eval x (p,j) := lift_eval ..

variable (S : Schema R B) (L : Schema U V) (sh : ∀ r, (S.tags r).length≤cap) (lh : ∀ u, (L.tags u).length≤cap)
variable (y : Pins R B t → Bool) (z : Pins U V q → Bool) (cells : Fin a → Fin C) (off box : Fin a → ℕ)
local notation3 "A₀" => fun (p : Spare.Field C g digits (Fin entries)) =>
  value (fun j => (liveFrame F boxes entry arena stride gap desc g digits).eval (Sum.elim x h) (p,j))
local notation3 (prettyPrint := false) "G₀" => directory S L boxes sh lh Spare.priv Spare.reports A₀ y z cells off box

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits) (cell : N.Site → Fin C)
variable (state : N.Site → Site) (sid : N.Site ↪ Fin a) (edges : N.Edge ↪ Fin m) (ports : P ↪ Fin n)
variable (physical : Represents N cell (fun v => (state v).size) sid edges ports F x)
variable (sizeFit : ∀ c, guessedSize N cell c+siteSize N cell c (fun v => (state v).size)+suppliedSize N cell c<2^w)

include physical sizeFit in
/-- Exact physical count bank of the directory that the signed field-plus-pointer
frame supplies to the site-ordered packet compiler. -/
theorem directory_real (c : Fin C) (room : guessedSize N cell c+siteSize N cell c (fun v => (state v).size)+
    suppliedSize N cell c+g*digits≤2^w) :
    (G₀).privateWires c.castSucc = FinalCell.privateBits N (fun v => (cell v).val) state c.val ∧
      (G₀).reports c.castSucc = countFields (FinalCell.countBase N (fun v => (cell v).val) state c.val) g digits := by
  have args : (A₀) = fun p => value (fun j =>
      (Spare.fields (g := g) (digits := digits) (CellAddressViews.frame F) (pointers F boxes entry arena stride gap desc)).eval x (p,j)) := by
    funext p
    simp only [liveFrame_eval,frame_eval]
  rw [args]
  exact Spare.emitted_real S L boxes sh lh y z cells off box N cell state sid edges ports F x physical sizeFit _ c room

/-- The skipped cell adds exactly one shared false word and an empty report list. -/
theorem directory_spare : (G₀).privateWires (Fin.last C)=0 ∧ (G₀).reports (Fin.last C)=[] := by
  obtain ⟨hp,hr⟩ := Spare.directory_spare S L boxes sh lh y z cells off box (A₀)
  rw [hp]
  refine ⟨?_,hr⟩
  simp only [liveFrame_eval,frame,Frame.subst_eval,Spare.fields_eval,Sum.elim_inl,Option.elim_none]
  exact zero_value

end CellPacketGeometry.History.Native.SignedFields

end BorderVNP
end Computability
end OAI
