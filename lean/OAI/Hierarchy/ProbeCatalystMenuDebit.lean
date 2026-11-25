import OAI.Hierarchy.ProbeStripMenuDebitFields
import OAI.Hierarchy.ProbeColumnAccounts

namespace OAI
/-! # The catalyst debit selected by a finite strip catalogue

All catalyst coordinates of a catalogue price equal twice the fixed radius.
Only the strictly positive coordinates of that price occur in its packet.
The resulting field width is uniform over the catalyst pairs in a single row.
-/

noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open AdaptiveProbe AdaptiveProbe.ColumnWires LinearAlgebra.SpectralBooks.ChordGraph
open scoped BigOperators Classical

variable {A B C H F I : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype H] [Field F]
  {k sites N : ℕ} [Nonempty (Fin sites)] [Nonempty (Role C H (A⊕B) k)]
  {edge : Role C H (A⊕B) k→Chord sites} {M ε tree : ℝ} {len : H→ℝ} {cap : A→ℝ}

omit [Fintype A] [Fintype B] [Fintype C] [Fintype H] [Nonempty (Role C H (A ⊕ B) k)] in
private theorem primitive_injective :
    Function.Injective (demand (I:=C) (H:=H) (k:=k) (Sum.inl (α:=A) (β:=B))) := by
  rintro (⟨c,j⟩|a) (⟨v,i⟩|b) eq <;> simp_all [demand]

/-- The effective per-copy width includes the possible zero-radius catalogue. -/
def cashRate (M : ℝ) (width : ℕ) := if 0<M then width else 0

theorem cashRate_le (M : ℝ) (width : ℕ) : cashRate M width≤width := by
  unfold cashRate
  split <;> omega

/-- Read off the actual coefficient in the menu; the positive demand filter
is evaluated at the recommendation, whose catalyst coordinates equal 2M. -/
theorem menu_cash (menu : Probe.FixedMenu F edge (demand (Sum.inl (α:=A) (β:=B)))
    ((fun y:A→ℝ => quote (I:=C) (k:=k) M len (LocalCommodity.extraPrice (B:=B) y)) '' Set.Icc 0 cap)
    ε tree N) (i : menu.index) (accountAt : A→I) (v : Role C H (A⊕B) k) :
    (if account accountAt v=none then StripDirectory.useBits menu i v else 0) =
      match v with
      | .catalyst .. => cashRate M (menu.packet i).width
      | _ => 0 := by
  classical
  cases v with
  | catalyst c j =>
    obtain ⟨y,_,price⟩ := i.val.property.1
    have pc : i.val.val (.catalyst c j)=2*M := (congrFun price (.catalyst c j)).symm
    have bit := StripDirectory.useBits_unique menu i primitive_injective (Sum.inl (c,j))
    simp only [demand] at bit
    simp only [account,ite_true,bit,pc,cashRate]
    by_cases pos : 0<M
    · rw [ite_eq_left (by linarith),ite_eq_left pos]
    · rw [ite_eq_right (by linarith),ite_eq_right pos]
  | extra e =>
    cases e with
    | inl a => simp [account]
    | inr e =>
      have unused : ∀ a,demand (I:=C) (H:=H) (k:=k) (Sum.inl (α:=A) (β:=B)) a≠.extra (.inr e) := by
        rintro (⟨c,j⟩|a) <;> simp [demand]
      simp [account,StripDirectory.useBits_unused menu i _ unused]
  | radius c j side =>
    simp only [account,ite_true]
    apply StripDirectory.useBits_unused menu i
    rintro (⟨x,a⟩|d) <;> simp [demand]
  | cross c a side other =>
    simp only [account,ite_true]
    apply StripDirectory.useBits_unused menu i
    rintro (⟨x,u⟩|d) <;> simp [demand]
  | horizontal e l =>
    simp only [account,ite_true]
    apply StripDirectory.useBits_unused menu i
    rintro (⟨x,u⟩|d) <;> simp [demand]

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
