import OAI.Computability.BorderVNP.CellPacketGeometryOpaqueTerminal
import OAI.Computability.BorderVNP.PackedFinalReportSpare

/-! # Physical private sizes, signed count addresses, and original one-copy source pointers -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History.Native.SignedFields

open Crossing Packing Packing.Inherited FrozenTape CellSparse Packet CellAddresses CellAddressPhysical
open CellAddressCircuit ParseBatchSort VPVNP.VerifierNetwork FinalReports

variable {a m n C k w d entries : ℕ} {σ O : Type} [Fintype σ]
variable (F : Fields a m n C d k w σ) (boxes : Fin a → List (Source.Box O)) (entry : Fin entries → Fin a)
variable (arena stride gap desc g digits : ℕ)

private noncomputable def view : Frame (σ ⊕ TerminalTable.Outputs a m n C k w) (CellAddressViews.View a m n C × Fin w) :=
  Frame.initial (Sum.inr ∘ Sum.inl)

/-- Both real report fields and source addresses read a single terminal
address bank. The finite-field variant can transpose the two report indices. -/
noncomputable def frame : Frame σ (Spare.Field C g digits (Fin entries) × Fin w) :=
  (Spare.fields view (OpaqueSlots.fromBank F entry arena stride gap desc)).subst (TerminalTable.bank F boxes).withInput

/-- The pointer column alone, useful for comparison with the actual returned
original site metadata. -/
noncomputable def pointers : Frame σ (Fin entries × Fin w) :=
  (OpaqueSlots.fromBank F entry arena stride gap desc).subst (TerminalTable.bank F boxes).withInput

/-- Sharing the terminal view preserves the real report generator and all
received-base pointer values, bit for bit. -/
theorem frame_eval (x : σ → Bool) :
    (frame F boxes entry arena stride gap desc g digits).eval x =
      (Spare.fields (g := g) (digits := digits) (CellAddressViews.frame F)
        (pointers F boxes entry arena stride gap desc)).eval x := by
  have views : (view (σ := σ) (k := k)).eval ((TerminalTable.bank F boxes).withInput.eval x) =
      (CellAddressViews.frame F).eval x := by
    funext p; simp [view,TerminalTable.bank]
  funext p
  rcases p with ⟨(_|f)|j,b⟩
  · simp [frame,Spare.fields_eval]
  · simp only [frame,Frame.subst_eval,Spare.fields_eval,Sum.elim_inl,Option.elim_some,FinalReports.frame,Frame.step_eval,views]
  · simp [frame,Spare.fields_eval,pointers]

/-- Sparse public gate cost, charging the terminal address bank once. -/
theorem frame_size :
    (frame F boxes entry arena stride gap desc g digits).size ≤ (TerminalTable.bank F boxes).size +
      (C+C*g*digits)*w*(100*(w+1)) + (OpaqueSlots.fromBank F entry arena stride gap desc).size+2 := by
  have h := Spare.fields_size (g := g) (digits := digits) (view (σ := σ) (k := k)) (OpaqueSlots.fromBank F entry arena stride gap desc)
  simp only [view,Frame.initial_size,zero_add] at h
  simp only [frame,Frame.subst_size,Frame.withInput_size,view]
  omega

theorem frame_cubic (R W : ℕ) (rows : 1+CellAddressCircuit.count a m n C≤R)
    (originals : C+entries+1≤R) (widths : d≤W ∧ k≤W ∧ w≤W ∧ Nat.clog 2 R≤W) :
    (frame F boxes entry arena stride gap desc g digits).size ≤
      8000*R*(W+1)^3+(C+C*g*digits)*w*(100*(w+1))+2 := by
  have core := frame_size F boxes entry arena stride gap desc g digits
  have one := TerminalTable.bank_cubic F boxes R W rows widths
  have two := OpaqueSlots.fromBank_cubic F entry arena stride gap desc R W originals widths.2
  simp only [Nat.mul_assoc] at one two core ⊢
  omega

/-- The actual original site pointer stored at the packet's public operand pin. -/
theorem pointer_bits (x : σ → Bool) (i : Fin entries) (b : Fin w) :
    (frame F boxes entry arena stride gap desc g digits).eval x (.inr i,b) =
      (OpaqueSlots.fromBank F entry arena stride gap desc).eval ((TerminalTable.bank F boxes).withInput.eval x) (i,b) := by
  simp [frame,Spare.fields_eval]

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable (cell : N.Site → Fin C) (state : N.Site → Site) (sid : N.Site ↪ Fin a) (edges : N.Edge ↪ Fin m) (ports : P ↪ Fin n)
variable (x : σ → Bool) (physical : Represents N cell (fun v => (state v).size) sid edges ports F x)
variable (sizeFit : ∀ c, guessedSize N cell c+siteSize N cell c (fun v => (state v).size)+suppliedSize N cell c < 2^w)

include physical sizeFit in
/-- The public descriptor's payload pointer is the true supplied-bank address
of its retained original, including the address-only gap and earlier originals. -/
theorem pointer_read (host : Fin entries → N.Site) (hosts : ∀ i, entry i=sid (host i))
    (old : ℕ → ℕ) (owners : ∀ i, old i.val=(cell (host i)).val) (hd : desc<2^w)
    (room : ∀ c : Fin C, (∑ i : Fin entries, if cell (host i)=c then desc else 0)<2^w)
    (i : Fin entries)
    (limit : arena+stride*(cell (host i)).val+suppliedSize N cell (cell (host i))+gap+
      RoutingISA.PrivatePlacement.prefixCounts old desc i.val (cell (host i)).val<2^w) :
    value (fun b => (frame F boxes entry arena stride gap desc g digits).eval x (.inr i,b)) =
      arena+stride*(cell (host i)).val+suppliedSize N cell (cell (host i))+gap+
        RoutingISA.PrivatePlacement.prefixCounts old desc i.val (cell (host i)).val := by
  simp only [pointer_bits]
  exact OpaqueSlots.fromBank_live F N cell (fun v => (state v).size) sid edges ports physical sizeFit boxes
    entry host hosts old owners arena stride gap desc hd room i limit

end CellPacketGeometry.History.Native.SignedFields

end BorderVNP
end Computability
end OAI
