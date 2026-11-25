import OAI.Computability.BorderVNP.PackedCellAddressViews
import OAI.Computability.BorderVNP.PackedBankReferences
import OAI.Computability.BorderVNP.PackedBankEmit

/-! # Selecting the true physical fields for every seed packet

The cell address pass produces canonical starts for source and destination
cable ends and the site staging areas. Each bank template reads a static
slot of that pass. Empty rectangle pins use one shared zero gate.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankJoint

open Crossing Shortening.StaticRows VPVNP.VerifierNetwork ParseBatchSort
open scoped Classical

/-- Cell address pass output order: cable/argument ends, site prefixes, then
the three ends of the internal, auxiliary, and supplied regions of each cell. -/
abbrev Views := CellAddressViews.View

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m) {S : Type*} [Fintype S]
variable {n p C : ℕ} (seed : S ↪ Fin n) (oldSites oldEdges : ℕ)

private abbrev V := Views (siteCapacity e oldSites n) (edgeCapacity e oldEdges n) p C

private noncomputable def endPin (s : S) (u : TemplateEdge e) (source : Bool) :
    V (p := p) (C := C) e oldSites oldEdges (n := n) :=
  let k := edgeSlot e oldEdges (seed s) u
  if source then .inl (.inl (.inl k)) else .inl (.inl (.inr k))

variable {σ : Type*} [Fintype σ] {w : ℕ}
variable (counts : Frame σ (S × Option (Fin e.count) × Fin w))
variable (view : Frame σ (V (p := p) (C := C) e oldSites oldEdges (n := n) × Fin w))
variable (ids : Frame σ (Fin (siteCapacity e oldSites n) × Fin w))

/-- Numeric inputs of the bank circuit in terms of true site and cable address views. -/
noncomputable def rawWord (x : σ → Bool) (s : S) : Raw e → ℕ
  | .inl i => value (fun j => counts.eval x (s,i,j))
  | .inr ⟨v,none⟩ => value (fun j => view.eval x (.inr (.inl (siteSlot e oldSites (seed s) v)),j))
  | .inr ⟨v,some none⟩ => value (fun j => ids.eval x (siteSlot e oldSites (seed s) v,j))
  | .inr ⟨v,some (some r)⟩ =>
    match reference e v r with
    | none => 0
    | some (u,source) => value (fun j => view.eval x (endPin e seed oldSites oldEdges s u source,j))

private noncomputable def zero : Frame σ Unit :=
  (Frame.initial (Empty.elim : Empty → σ)).step (fun _ => .const false)

private theorem zero_size : (zero (σ := σ)).size ≤ 1 := by
  simpa [zero] using Frame.step_size_le (Frame.initial (Empty.elim : Empty → σ))
    (fun _ : Unit => .const false) 1 (fun _ => le_rfl)

private theorem false_word {w : ℕ} : value (fun _ : Fin w => false) = 0 := by
  induction w with
  | zero => rfl
  | succ w ih => simpa only [value,Bool.toNat_false,zero_mul,zero_add] using ih

/-- Concrete Boolean pin selection from the public profile, cell-layout, and box-ID frames.
All operands are read from the exact static geometry rows. -/
noncomputable def install : Frame σ (S × Raw e × Fin w) :=
  let all := Crossing.parallelFrame counts (Crossing.parallelFrame view (Crossing.parallelFrame ids zero))
  all.select fun (i : S × Raw e × Fin w) => match i.2.1 with
    | .inl h => .inl (i.1,h,i.2.2)
    | .inr ⟨v,none⟩ => .inr (.inl (.inr (.inl (siteSlot e oldSites (seed i.1) v)),i.2.2))
    | .inr ⟨v,some none⟩ => .inr (.inr (.inl (siteSlot e oldSites (seed i.1) v,i.2.2)))
    | .inr ⟨v,some (some r)⟩ =>
      match reference e v r with
      | none => .inr (.inr (.inr ()))
      | some (u,source) => .inr (.inl (endPin e seed oldSites oldEdges i.1 u source,i.2.2))

/-- The three source programs occur once, and absent rectangular pins share one zero. -/
theorem install_size :
    (install e seed oldSites oldEdges counts view ids).size ≤ counts.size + view.size + ids.size + 1 := by
  simp only [install,Frame.select_size,Crossing.parallelFrame_size]
  have h := zero_size (σ := σ)
  omega

/-- Every actual input word of the complete packet compiler agrees with its assigned
physical source, merged directory ID, or guessed histogram. -/
theorem install_value (x : σ → Bool) (s : S) (r : Raw e) :
    value (fun j => (install e seed oldSites oldEdges counts view ids).eval x (s,r,j)) =
      rawWord e seed oldSites oldEdges counts view ids x s r := by
  rcases r with i | ⟨v,(_ | _ | b)⟩
  · simp [install,rawWord]
  · simp [install,rawWord]
  · simp [install,rawWord]
  · cases hr : reference e v b with
    | none => simp [install,hr,rawWord,zero,false_word,BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit.Expr.eval]
    | some u => rcases u with ⟨u,side⟩; simp [install,hr,rawWord]

/-- The installed circuit emits all tagged seed packet words from the real profile,
address and box ordinal passes, with their source gates shared across the entire batch. -/
theorem installed_packets (first : Fin D × Bool) :
    ∃ f : Frame σ (S × Output e first × Fin w),
      f.size ≤ counts.size + view.size + ids.size + 4 + Fintype.card S *
        ((BankCircuit.headerNodes D e.count m + PaidBox.nodeBound e + nodes e first) * (100*(w+1)^2)) ∧
      ∀ x s, let raw := rawWord e seed oldSites oldEdges counts view ids x s
        Fits e w raw → ∀ z : Output e first, (expr e first z).Fits w (fun i => word e raw (pin e z.1 i)) →
          value (fun j => f.eval x (s,z,j)) =
            (CellSparse.Packet.fieldList CellSparse.Packet.record (emitted e first raw z.1))[z.2.val]?.getD 0 := by
  obtain ⟨f,hf,he⟩ := exists_packetFrame e first w (install e seed oldSites oldEdges counts view ids)
  refine ⟨f,?_,?_⟩
  · have hs := install_size e seed oldSites oldEdges counts view ids
    omega
  · intro x s
    have h := he x s
    dsimp only at h ⊢
    rw [funext (install_value e seed oldSites oldEdges counts view ids x s)] at h
    exact h

end Packing.BankJoint

end BorderVNP
end Computability
end OAI
