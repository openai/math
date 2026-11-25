import OAI.Computability.BorderVNP.PackedBankPacketCharges
import OAI.Computability.BorderVNP.CellPacketInputSize

/-! # Raw field and stored factor bounds for the seed-site packets

The full private row-ID table is charged even for a term of multiplicity zero.
All words of the public packet, including length prefixes and arithmetic
intermediates, have a uniform bound obtained from the fixed arithmetic tape.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankCharges

open Crossing CellSparse BankPacket Word Shortening Shortening.StaticRows Shortening.CombiningStep
open scoped Classical

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)

/-- Full static mass of the stored one-copy gadget matrix. -/
theorem paid_staticMass (position : e.Entry → ℕ) (a : Fin e.count) (v : (e.net a).Site) :
    (PaidBox.tableFactor e position a v).staticMass =
      (PaidBox.arity e a v + 1)*(2^(PaidBox.arity e a v) + 1) := by
  simp [PaidBox.tableFactor,CellBox.factor,CellBox.rows,Factor.staticMass,PaidBox.arity]

/-- The stored private directory mass at a paid site includes its one-copy
matrix once, for all multiplicities. -/
theorem paid_storedMass (position : e.Entry → ℕ) (a : Fin e.count) (v : (e.net a).Site) (copies : ℕ) :
    Packet.storedMass (PaidBox.siteDirectory e position a v copies) =
      1 + (PaidBox.arity e a v + 1)*(2^(PaidBox.arity e a v) + 1) := by
  simp [PaidBox.siteDirectory,Packet.storedMass,paid_staticMass]

/-- Bounds all relative wire numbers, dimension prefixes, and actual gadget IDs
in the private one-copy table for this site. -/
theorem paid_factorFields (position : e.Entry → ℕ) (a : Fin e.count) (v : (e.net a).Site)
    (U : ℕ) (hw : PaidBox.arity e a v ≤ U) (hr : 2^(PaidBox.arity e a v) ≤ U)
    (hid : ∀ t, position t ≤ U) : Packet.FactorFields (PaidBox.tableFactor e position a v) U := by
  simp only [Packet.FactorFields,Factor.FieldBound,Factor.TableBound,PaidBox.tableFactor,
    CellBox.factor,CellBox.rows,List.length_ofFn,List.forall_mem_ofFn_iff]
  exact ⟨⟨⟨hw,hr⟩,fun i => i.isLt.le.trans hw⟩,fun _ => hid _⟩

/-- Bounds on all serialized natural words imply the raw field conditions of a
sparse record, including histogram entries and all four box operands. -/
theorem recordFields_of_words (r : Record) (U : ℕ)
    (h : ∀ x ∈ Packet.record r, x ≤ U) : Packet.RecordFields r U := by
  cases r <;>
    simp [Packet.RecordFields,Record.GuardBound,CellSparse.Profile.PortBound,Packet.record,
      Packet.port,Packet.fieldList,Packet.vector,Packet.route] at h ⊢ <;> try tauto
  obtain ⟨_,hc,hb,hs,hl,hw,hh,h⟩ := h
  refine ⟨⟨hc,hw,hh,h _ (Or.inr (Or.inl rfl)),⟨hb,hs,hl⟩,fun r hr => ?_⟩,
    fun k hk => h _ (Or.inl hk)⟩
  repeat' apply And.intro
  all_goals apply h; exact Or.inr (Or.inr ⟨r,hr,by tauto⟩)

/-- Static upper coefficient for any nonnegative value computed by a word expression. -/
def coefficient {I : Type*} : WidthExpr I → ℕ
  | .field _ => 1
  | .const k => k
  | .binary _ a b => coefficient a + coefficient b

private theorem op_le (op : Op) (a b : ℕ) : op.apply a b ≤ a+b := by
  cases op <;> simp only [Op.apply] <;> omega

/-- Every intermediate arithmetic value is at most the sum of the scaled leaf bounds. -/
theorem eval_le {I : Type*} (f : WidthExpr I) (x : I → ℕ) {M : ℕ} (hx : ∀ i, x i ≤ M) :
    f.eval x ≤ coefficient f * (M+1) := by
  induction f with
  | field i => exact (hx i).trans (by simp [coefficient])
  | const k => exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  | binary op a b ha hb =>
    rw [coefficient,Nat.add_mul]
    exact (op_le _ _ _).trans (Nat.add_le_add ha hb)

/-- The same static coefficient guarantees that every subexpression fits its installed word. -/
theorem fits_of_coefficient {I : Type*} (f : WidthExpr I) (x : I → ℕ) (w M : ℕ)
    (hx : ∀ i, x i ≤ M) (h : coefficient f * (M+1) < 2^w) : f.Fits w x := by
  induction f with
  | field i => exact ((eval_le (.field i) x hx).trans_lt h)
  | const k => exact ((eval_le (.const k) x hx).trans_lt h)
  | binary op a b ha hb =>
    have hsize := h
    rw [coefficient,Nat.add_mul] at hsize
    exact ⟨ha (by omega),hb (by omega),(eval_le (.binary op a b) x hx).trans_lt h⟩

private theorem entry_le_sum {α : Type*} (f : α → ℕ) (l : List α) (a : α) (ha : a ∈ l) :
    f a ≤ (l.map f).sum := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · simp
    · exact (ih ha).trans (Nat.le_add_left _ _)

/-- Uniform coefficient for all arithmetic subexpressions of a frozen physical site tape. -/
noncomputable def wordCoefficient (first : Fin D × Bool) (v : TemplateSite e) : ℕ :=
  ((tape (format e first v).2).map coefficient).sum

/-- Every serialized public record at the site satisfies the concrete raw-field bound,
including values affected by offsets, merged IDs and the physical bundle addresses. -/
theorem emitted_recordFields (first : Fin D × Bool) (v : TemplateSite e)
    (x : (format e first v).1 → ℕ) (M : ℕ) (hx : ∀ i, x i ≤ M) (r : Record)
    (hr : r ∈ (format e first v).2.map (RecordCode.read x)) :
    Packet.RecordFields r (wordCoefficient e first v * (M+1)) := by
  apply recordFields_of_words
  intro k hk
  let rows := (format e first v).2
  have hm : k ∈ Packet.fieldList Packet.record (rows.map (RecordCode.read x)) :=
    List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨r,hr,hk⟩)
  rw [← tape_eval] at hm
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hm
  exact (eval_le f x hx).trans (Nat.mul_le_mul_right _ (entry_le_sum coefficient (tape rows) f hf))

/-- The frozen frame can be used at this word width simultaneously on every output. -/
theorem emitted_fits (first : Fin D × Bool) (v : TemplateSite e)
    (x : (format e first v).1 → ℕ) (w M : ℕ) (hx : ∀ i, x i ≤ M)
    (h : wordCoefficient e first v * (M+1) < 2^w) :
    ∀ f ∈ tape (format e first v).2, f.Fits w x := by
  intro f hf
  apply fits_of_coefficient f x w M hx
  exact (Nat.mul_le_mul_right _ (entry_le_sum coefficient _ f hf)).trans_lt h

/-- The contribution of a seed site to the full private metadata matrix mass. -/
noncomputable def stored : TemplateSite e → ℕ
  | .inl _ | .inr (.inl _) => 0
  | .inr (.inr ⟨a,v⟩) => 1 + (PaidBox.arity e a v+1)*(2^(PaidBox.arity e a v)+1)

variable [NeZero D] {P : Type*} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K)
    {A : Type} [Fintype A] (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
    (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)

/-- Sum of private matrix masses in any tile of the actual sewn output, charged
once per physical site and uniformly over all multiplicities. -/
theorem stored_tile_le (prior payload : (output e p bin perm positive first q).layout.Site → ℕ)
    (test : (output e p bin perm positive first q).layout.Site → Prop) :
    testedWidth (Sum.elim (fun _ : p.layout.Site => 0)
      (fun z : Σ _ : A, TemplateSite e => stored e z.2)) test ≤
      (∑ v, stored e v) * localRecords (output e p bin perm positive first q).layout
        false prior payload test :=
  static_tile_le e p bin perm positive first q (stored e) false prior payload test

end Packing.BankCharges

end BorderVNP
end Computability
end OAI
