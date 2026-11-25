import OAI.Hierarchy.ProbeBallPrices
import OAI.Hierarchy.ProbeReplacementLedger

namespace OAI
/-! # Ordinary inventory and cash roles in a physical column test -/

namespace Hierarchy.AdaptiveProbe.ColumnWires
open scoped BigOperators Classical
noncomputable section

variable {C H A B I : Type*} {k : ℕ}

/-- Of the local replacement sockets, only ordinary requested wires become new
inventory. Every other socket is settled through a physically available link or
opposite-end catalyst pair at its printed price. -/
def account (address : A → I) : Role C H (A ⊕ B) k → Option I
  | .extra (.inl a) => some (address a)
  | _ => none

def printed (M : ℝ) (len : H → ℝ) := quote (I:=C) (k:=k) M len (LocalCommodity.extraPrice (A:=A) (B:=B) (fun _ => 0))

theorem quote_active (M : ℝ) (len : H → ℝ) (address : A → I) (x : I → ℝ)
    (r : Role C H (A ⊕ B) k) :
    quote M len (LocalCommodity.extraPrice (B:=B) (x ∘ address)) r =
    activePrice (account address) (printed M len) x r := by
  cases r with
  | extra b => cases b <;> rfl
  | catalyst | radius | cross | horizontal => rfl

/-- The accounts for every actual positive demand, even when a physical site pair
or an inventory address occurs repeatedly in the network layout. -/
theorem demand_ordinary (address : A→I) (a : A) : account (C:=C) (H:=H) (B:=B) (k:=k) address
    (demand (Sum.inl (β:=B)) (.inr a))=some (address a) := rfl

theorem demand_catalyst (address : A→I) (i : C) (j : Fin k) : account (H:=H) (B:=B) address
    (demand (Sum.inl (β:=B)) (.inl (i,j)))=none := rfl

/-- Read an ordinary-stock tag back to the unique actual commodity role that
carried it. The signed catalyst rows, radius rows and paid links contribute cash. -/
theorem ordinary_of_some (address : A→I) (r : Role C H (A⊕B) k) {i : I}
    (found : account address r = some i) : ∃ a, r=.extra (.inl a) ∧ address a=i := by
  cases r with
  | catalyst | radius | cross | horizontal => contradiction
  | extra e => cases e with
    | inr b => contradiction
    | inl a => exact ⟨a,rfl,Option.some.inj found⟩

/-- Incidence bound on the actual selected board. Restriction to any subset of
rows preserves this single-reader bound, regardless of the size of padded native banks. -/
theorem selected_incidence {R : Type*} [Fintype R] [Fintype C] [Fintype H] [Fintype A] [Fintype B]
    (selected : Finset R) (address : R×A ↪ I) (i : I) :
    (Finset.univ.filter fun p : ↥selected × Role C H (A⊕B) k =>
      account (fun a => address (p.1.val,a)) p.2=some i).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  rintro ⟨r,e⟩ h ⟨r',e'⟩ h'
  obtain ⟨a,rfl,aa⟩ := ordinary_of_some _ _ (Finset.mem_filter.mp h).2
  obtain ⟨b,rfl,bb⟩ := ordinary_of_some _ _ (Finset.mem_filter.mp h').2
  have both := address.injective (aa.trans bb.symm)
  have row : r=r' := Subtype.ext (congrArg Prod.fst both)
  have ab := congrArg Prod.snd both
  cases row; cases ab; rfl

end
end Hierarchy.AdaptiveProbe.ColumnWires

end OAI
