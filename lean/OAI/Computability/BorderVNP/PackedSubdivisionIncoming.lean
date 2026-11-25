import OAI.Computability.BorderVNP.PackedSubdivisionOriginal
import OAI.Computability.BorderVNP.PackedBankInheritedSiteCharges

/-! # Physical incidence bounds at retained sites after subdivision

A cable can occupy two endpoint rows of an original site precisely when both
ends meet that site and the route has interior relays. All attached exterior
words keep their widths and their names.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Subdivision

open Crossing Placement
open scoped Classical

variable {D : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)
    (routes : N.WireRoutes) (v : N.Site)
local notation "G" => N.subdivide routes

private theorem src_at_old (e : N.Edge) (k : Fin (routes.interior e + 1)) :
    (G).src ⟨e,k⟩ = .inl v ↔ k = 0 ∧ N.src e = v := by
  induction k using Fin.cases with
  | zero => simp [Network.subdivide]
  | succ k => simp [Network.subdivide]

private theorem dst_at_old (e : N.Edge) (k : Fin (routes.interior e + 1)) :
    (G).dst ⟨e,k⟩ = .inl v ↔ k = Fin.last _ ∧ N.dst e = v := by
  induction k using Fin.lastCases with
  | last => simp [Network.subdivide]
  | cast k => simp [Network.subdivide, Fin.castSucc_ne_last]

private theorem original_end (e : Incident G (.inl v)) :
    (e.val.2 = 0 ∧ N.src e.val.1 = v) ∨
    (e.val.2 = Fin.last _ ∧ N.dst e.val.1 = v) :=
  e.property.imp ((src_at_old N routes v _ _).mp) ((dst_at_old N routes v _ _).mp)

/-- Name an old-site cable row by the original cable and whether its hop is nonzero.
A route with no relays uses just the zero-hop slot even for a loop. -/
def hopRows : Incident G (.inl v) ↪ Incident N v × Bool where
  toFun e := (⟨e.val.1, (original_end N routes v e).imp And.right And.right⟩, decide (e.val.2 ≠ 0))
  inj' := by
    rintro ⟨⟨e,k⟩,he⟩ ⟨⟨f,l⟩,hf⟩ h
    have hbase : e = f := congrArg (fun z : Incident N v × Bool => z.1.val) h
    subst f
    have hside : decide (k ≠ 0) = decide (l ≠ 0) := congrArg Prod.snd h
    have hk := original_end N routes v ⟨⟨e,k⟩,he⟩
    have hl := original_end N routes v ⟨⟨e,l⟩,hf⟩
    change (k = 0 ∧ _) ∨ (k = _ ∧ _) at hk
    change (l = 0 ∧ _) ∨ (l = _ ∧ _) at hl
    have eq : k = l := by
      by_cases hz : k = 0
      · have : l = 0 := by simpa [hz] using hside.symm
        exact hz.trans this.symm
      · have : l ≠ 0 := by simpa [hz] using hside.symm
        exact (hk.resolve_left (fun t => hz t.1)).1.trans
          (hl.resolve_left (fun t => this t.1)).1.symm
    subst l
    rfl

/-- Exterior argument rows at a retained site are in bijection with the old rows. -/
def originalPorts : Attached G (.inl v) ≃ Attached N v where
  toFun p := ⟨p.val, Sum.inl.inj p.property⟩
  invFun p := attached N routes v p
  left_inv _ := rfl
  right_inv _ := rfl

/-- Each original cable pays for at most two physical rows of its original width. -/
theorem hop_weight_le (charge : N.Edge → ℕ) :
    (∑ e : Incident G (.inl v), charge e.val.1) ≤ 2 * ∑ e : Incident N v, charge e.val := by
  let f := hopRows N routes v
  calc
    _ ≤ ∑ t : Incident N v × Bool, charge t.1.val :=
      Finset.sum_le_sum_of_injOn f f.injective.injOn (Finset.subset_univ _) (fun _ _ => le_rfl)
        (fun _ _ _ => Nat.zero_le _)
    _ = _ := by simp [Fintype.sum_prod_type, Finset.mul_sum, two_mul]

variable [Fintype P]

/-- Count every incident physical cable and every attached port, including zero-width rows. -/
theorem original_row_count_le :
    Fintype.card (Incident G (.inl v)) + Fintype.card (Attached G (.inl v)) ≤
    2 * (Fintype.card (Incident N v) + Fintype.card (Attached N v)) := by
  have he := Fintype.card_le_of_injective _ (hopRows N routes v).injective
  rw [Fintype.card_prod,Fintype.card_bool] at he
  rw [Fintype.card_congr (originalPorts N routes v)]
  omega

/-- The new incoming bank charges at most twice the original site's incident bits. -/
theorem original_incoming_le : incoming G (.inl v) ≤ 2 * incoming N v := by
  rw [←sum_width G (.inl v), ←sum_width N v]
  simp only [Row,Fintype.sum_sum_type,width,Sum.elim_inl,Sum.elim_inr]
  have he := hop_weight_le N routes v N.width
  have hp : (∑ p : Attached G (.inl v), bits p.val) = ∑ p : Attached N v, bits p.val :=
    (originalPorts N routes v).sum_comp fun p => bits p.val
  change (∑ e : Incident G (.inl v), N.width e.val.1) + _ ≤ _
  rw [hp]
  omega

variable {m n np : ℕ} (oldID : N.Edge ↪ Fin m) (newID : (N.subdivide routes).Edge ↪ Fin n) (portID : P ↪ Fin np)

/-- Actual endpoint-retention programs grow by at most two copies of the old incoming bank.
Their record list adds at most one binding row per old cable or exterior word. -/
theorem original_program_budget (s : Site) :
    let t := originalProgram N routes v oldID newID portID s
    t.size ≤ s.size + 2 * incoming N v ∧
    t.rows.length ≤ s.rows.length + (Fintype.card (Incident N v) + Fintype.card (Attached N v)) := by
  have hr := original_resources N routes v oldID newID portID s
  exact ⟨Nat.add_le_add_left (original_incoming_le N routes v) s.size,hr.2.2.2⟩

/-- Subdivision retains every earlier private table and sweep. Its only static
increase is the serialization and guard cost of the selected whole-word ties. -/
theorem original_program_charges (s : Site) :
    let t := originalProgram N routes v oldID newID portID s
    t.staticNodes ≤ s.staticNodes + 1034 * (Fintype.card (Incident N v) + Fintype.card (Attached N v)) ∧
    t.expandedLoad = s.expandedLoad + s.incoming := by
  dsimp only [originalProgram]
  rw [s.staticNodes_retain, s.expandedLoad_retain]
  exact ⟨Nat.add_le_add_left (Nat.mul_le_mul_left _ (cuts_count N routes v oldID newID portID)) _,rfl⟩

end Packing.Inherited.Subdivision

end BorderVNP
end Computability
end OAI
