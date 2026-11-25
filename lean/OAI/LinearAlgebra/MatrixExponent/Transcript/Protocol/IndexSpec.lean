import OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Machine
import OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.OrderSpec
import OAI.LinearAlgebra.MatrixExponent.Transcript.RAM.Calls

section
/-! # Input-dependent addresses and gated uploads to zero-initialized memory -/

namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Scatter

open Coloring

structure Upload (X I : Type) (w : ℕ) where
  address : I → slots (word w) → X ⊕ Bool
  enabled : I → X ⊕ Bool
  source : I → X ⊕ Bool

namespace Upload

variable {X I : Type} {w : ℕ} (u : Upload X I w) (x : X → Bool)

def addr (i : I) : B w := Control.decode w (Sum.elim x id ∘ u.address i)

/-- Enabled writes may overlap when they agree. Unwritten cells must be zero. -/
structure Fits (m : B w → Bool) : Prop where
  agrees : ∀ i, Sum.elim x id (u.enabled i) = true → m (u.addr x i) = Sum.elim x id (u.source i)
  covers : ∀ z, m z = true → ∃ i, Sum.elim x id (u.enabled i) = true ∧ u.addr x i = z

def write (i : I) (m : B w → Bool) : B w → Bool :=
  if Sum.elim x id (u.enabled i) then Function.update m (u.addr x i) (Sum.elim x id (u.source i))
  else m

noncomputable def load [Fintype I] : ℕ → B w → Bool
  | 0 => fun _ => false
  | n + 1 => if h : n < Fintype.card I then
      u.write x ((Fintype.equivFin I).symm ⟨n, h⟩) (load n)
    else load n

end Upload
end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Scatter
end

/-! # Wire format of a length-bounded message -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Strings

open Coloring

abbrev Body (A : Format) (k : ℕ) := Match.format A (RAM.token k)

/-- The record is occupied. Its data consists of direction, key and length-coded string. -/
abbrev packet (A : Format) (k : ℕ) (row : Bool × A.obj × List Bool) :=
  (Body A k).code (true, row.1, row.2.1, RAM.encodeToken k row.2.2)

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Strings
end

/-! # The charged bits available to an ordered-message reader -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Strings
open Coloring

abbrev Events (A : Format) (k M T : ℕ) := Σ s : Slot M T k, (Body A s.1.val).pins
abbrev Bank (A : Format) (k M T : ℕ) := Events A k M T ⊕ (Slot M T k × (Position M).pins)

variable {I : Type} {A : Format} {n T : I → ℕ} {k M : ℕ}

def bank (row : Rows A n) (p : Layout row M k T) (hm : ∀ i, n i ≤ M) (i : I) :
    Bank A k M (T i) → Bool
  | .inl ⟨s, b⟩ => (Body A s.1.val).code (code row p s.1 ⟨i, s.2⟩) b
  | .inr (s, b) => (Position M).code (order row p hm i s) b

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Strings
end

/-! # Direct addressing of packet fields and payload bits -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Strings

open Coloring

variable (A : Format) (k M : ℕ)

abbrev width := Nat.clog 2 (1 + M) + k + Nat.clog 2 (8 + k + A.width) + 1

def payloadPin (i : B k) : (Body A k).pins := .inr (.inr (.inr (.inr (.inr (i, ())))))

private abbrev Header := Unit ⊕ Unit ⊕ A.pins ⊕ Unit ⊕ slots (word (k + 1))

private def mark : (Body A k).pins → B k × Option (Header A k)
  | .inl i => (0, some (.inl i))
  | .inr (.inl i) => (0, some (.inr (.inl i)))
  | .inr (.inr (.inl i)) => (0, some (.inr (.inr (.inl i))))
  | .inr (.inr (.inr (.inl i))) => (0, some (.inr (.inr (.inr (.inl i)))))
  | .inr (.inr (.inr (.inr (.inl i)))) => (0, some (.inr (.inr (.inr (.inr i)))))
  | .inr (.inr (.inr (.inr (.inr i)))) => (i.1, none)

private theorem mark_injective : Function.Injective (mark A k) := by
  let back : B k × Option (Header A k) → (Body A k).pins
    | (_, some (.inl i)) => .inl i
    | (_, some (.inr (.inl i))) => .inr (.inl i)
    | (_, some (.inr (.inr (.inl i)))) => .inr (.inr (.inl i))
    | (_, some (.inr (.inr (.inr (.inl i))))) => .inr (.inr (.inr (.inl i)))
    | (_, some (.inr (.inr (.inr (.inr i))))) => .inr (.inr (.inr (.inr (.inl i))))
    | (i, none) => payloadPin A k i
  have he : Function.LeftInverse back (mark A k) := by
    rintro (i|i|i|i|i|⟨i, ⟨⟩⟩) <;> rfl
  exact he.injective

private abbrev Tag := Format.addr (Nat.clog 2 (8 + k + A.width))

private def tag : Option (Header A k) ↪ (Tag A k).obj := by
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  change Fintype.card (Option (Header A k)) ≤ Fintype.card (B (Nat.clog 2 (8 + k + A.width)))
  rw [Fintype.card_fin]
  apply le_trans _ (Nat.le_pow_clog (by decide) _)
  simp only [Header, Fintype.card_option, Fintype.card_sum, Fintype.card_unit, MatrixExponent.card_slots,
    wd_word, Format.width]
  omega

private abbrev BankFromPacketAddress := Format.pair (Position M) (.pair (.addr k) (.pair (Tag A k) .bit))

private def layout : slots (word (width A k M)) ≃ (BankFromPacketAddress A k M).pins :=
  Fintype.equivOfCardEq (by
    change (Format.addr (width A k M)).width = (BankFromPacketAddress A k M).width
    rw [Format.width_addr]
    simp only [BankFromPacketAddress, Position, Tag, Format.width_pair, Format.width_addr, width]
    have := Format.width_bit
    omega)

private def pack : (BankFromPacketAddress A k M).obj ≃ B (width A k M) :=
  ((BankFromPacketAddress A k M).code.trans ((layout A k M).symm.arrowCongr (Equiv.refl Bool))).trans
    (Control.decode _)

/-- The ordinal selects a packet. Each header bit has its own tag, and the
payload tag uses a separate offset register. The final bit reserves work space. -/
def address : (Position M).obj × (Body A k).pins ↪ B (width A k M) where
  toFun z := pack A k M (z.1, (mark A k z.2).1, tag A k (mark A k z.2).2, false)
  inj' x y h := by
    obtain ⟨ho, he⟩ := Prod.mk.inj ((pack A k M).injective h)
    obtain ⟨hi, hc⟩ := Prod.mk.inj he
    exact Prod.ext ho (mark_injective A k (Prod.ext hi ((tag A k).injective (Prod.mk.inj hc).1)))

private def workspaceFields : B (width A k M - 1) ≃ (Position M).obj × B k × (Tag A k).obj := by
  apply Fintype.equivOfCardEq
  simp only [Fintype.card_fin, Fintype.card_prod, width]
  rw [← pow_add, ← pow_add]
  congr 1
  omega

/-- The last address bit separates ordinary inputs and scratch space from messages. -/
def workspace : B (width A k M - 1) ↪ B (width A k M) where
  toFun a := let v := workspaceFields A k M a; pack A k M (v.1, v.2.1, v.2.2, true)
  inj' a b h := by
    apply (workspaceFields A k M).injective
    exact congrArg (fun z : (BankFromPacketAddress A k M).obj => (z.1, z.2.1, z.2.2.1)) ((pack A k M).injective h)

theorem workspace_ne (a : B (width A k M - 1)) (m : (Position M).obj × (Body A k).pins) :
    workspace A k M a ≠ address A k M m := by
  intro he
  exact Bool.false_ne_true (congrArg (fun z : (BankFromPacketAddress A k M).obj => z.2.2.2) ((pack A k M).injective he)).symm

/-- The upload reads its ordinal from the input and uses a fixed field. -/
def wire (b : (Body A k).pins) (j : slots (word (width A k M))) : (Position M).pins ⊕ Bool :=
  match layout A k M j with
  | .inl i => .inl i
  | .inr (.inl i) => .inr ((Format.addr k).code (mark A k b).1 i)
  | .inr (.inr (.inl i)) => .inr ((Tag A k).code (tag A k (mark A k b).2) i)
  | .inr (.inr (.inr _)) => .inr false

theorem addr (b : (Body A k).pins) (o : (Position M).obj) :
    Control.decode (width A k M) (Sum.elim ((Position M).code o) id ∘ wire A k M b) =
      address A k M (o, b) := by
  apply congrArg (Control.decode _)
  funext j
  change Sum.elim ((Position M).code o) id (wire A k M b j) =
    (BankFromPacketAddress A k M).code (o, (mark A k b).1, tag A k (mark A k b).2, false) (layout A k M j)
  unfold wire
  generalize layout A k M j = v
  rcases v with i|i|i|i <;> rfl

/-- Both the ordinal and the payload offset can be arbitrary register values. -/
def payloadWire (j : slots (word (width A k M))) :
    (Position M).pins ⊕ (slots (word k) ⊕ Bool) :=
  match layout A k M j with
  | .inl i => .inl i
  | .inr (.inl i) => .inr (.inl i)
  | .inr (.inr (.inl i)) => .inr (.inr ((Tag A k).code (tag A k none) i))
  | .inr (.inr (.inr _)) => .inr (.inr false)

theorem payload_addr (o : (Position M).obj) (i : B k) :
    Control.decode (width A k M)
      (Sum.elim ((Position M).code o) (Sum.elim ((Format.addr k).code i) id) ∘ payloadWire A k M) =
      address A k M (o, payloadPin A k i) := by
  rw [← addr]
  apply congrArg (Control.decode _)
  funext j
  unfold Function.comp payloadWire wire
  generalize layout A k M j = v
  rcases v with l|l|l|l <;> rfl

theorem payload_addr_bits (o : (Position M).pins → Bool) (i : slots (word k) → Bool) :
    Control.decode (width A k M) (Sum.elim o (Sum.elim i id) ∘ payloadWire A k M) =
      address A k M ((Position M).code.symm o, payloadPin A k ((Format.addr k).code.symm i)) := by
  simpa only [Equiv.apply_symm_apply] using
    payload_addr A k M ((Position M).code.symm o) ((Format.addr k).code.symm i)

theorem packet_bit (row : Bool × A.obj × List Bool) (i : B k) (len : row.2.2.length ≤ 2 ^ k) :
    packet A k row (payloadPin A k i) = row.2.2[i.val]?.getD false := by
  have h : row.2.2.length < 2 ^ (k + 1) := by rw [pow_succ]; have := Nat.two_pow_pos k; omega
  simp only [packet, RAM.encodeToken, dite_eq_left h]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Strings
end
