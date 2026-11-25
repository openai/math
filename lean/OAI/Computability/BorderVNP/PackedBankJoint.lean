import OAI.Computability.BorderVNP.PackedBankPacketBox
import OAI.Computability.BorderVNP.PackedBankPacketProfiles
import OAI.Computability.BorderVNP.ShortenStaticRowsAccess

/-! # Shared preparation of all sparse packets in one seed bank

The public location columns are the site prefixes, merged box IDs and the bases
of the canonical physical cable words. The matched size and histogram compute
the remaining operands. All sites of a seed share those arithmetic gates.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankJoint

open BankCircuit Shortening.StaticRows Crossing ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)

/-- Actual number of incident physical bundles in a paid site. -/
noncomputable abbrev bundles (a : Fin e.count) (v : (e.net a).Site) :=
  Fintype.card (PaidBox.Bundle (e.net a) v)

/-- Physical bundle-base references needed at a fixed site. -/
noncomputable def Bases : TemplateSite e → Type
  | .inl _ | .inr (.inl _) => Slice D e.count
  | .inr (.inr ⟨a,v⟩) => Fin (bundles e a v)

noncomputable instance (v : TemplateSite e) : Fintype (Bases e v) := by
  rcases v with _ | _ | ⟨a,v⟩ <;> dsimp [Bases] <;> infer_instance

/-- The absent field is the site offset, the second absent field is its merged box ID.
A present physical reference supplies the base of a canonical cable. -/
abbrev Location (v : TemplateSite e) := Option (Option (Bases e v))

/-- Counts and concrete physical addresses supplied by earlier public passes. -/
abbrev Raw := Option (Fin e.count) ⊕ Σ v : TemplateSite e, Location e v

/-- Shared, computed header and paid-box pins, together with the original addresses. -/
abbrev Prepared := Header D e.count ⊕ PaidBox.Pin e ⊕ Σ v : TemplateSite e, Location e v

/-- Numeric semantics of each shared preparation pin. -/
noncomputable def word (raw : Raw e → ℕ) : Prepared e → ℕ
  | .inl h => headerWord m (fun i => raw (.inl i)) h
  | .inr (.inl ⟨a,v,h⟩) => PaidBox.header (PaidBox.widths (e.net a) v) (raw (.inl (some a))) h
  | .inr (.inr z) => raw (.inr z)

/-- The preparation passes use only the physical origin/terminal bank sizes and the
affine input/staging addresses of a one-copy paid table. -/
def Fits (w : ℕ) (raw : Raw e → ℕ) : Prop :=
  HeaderFits (D := D) m w (fun i => raw (.inl i)) ∧
    ∀ u : PaidBox.Pin e, word e raw (.inr (.inl u)) < 2^w

/-- Evaluate all shared preparation gates from the actual source frame, retaining
the address columns without additional gates. -/
theorem exists_prepare {S σ : Type*} [Fintype S] [Fintype σ] (w : ℕ)
    (source : Frame σ (S × Raw e × Fin w)) :
    ∃ f : Frame σ (S × Prepared e × Fin w),
      f.size ≤ source.size + 2 + Fintype.card S *
        ((headerNodes D e.count m + PaidBox.nodeBound e) * (100*(w+1)^2)) ∧
      ∀ x s, let raw := fun r => value (fun j => source.eval x (s,r,j))
        Fits e w raw → ∀ r, value (fun j => f.eval x (s,r,j)) = word e raw r := by
  classical
  let C : Frame (S × Raw e × Fin w) (S × Option (Fin e.count) × Fin w) :=
    Frame.initial (fun i => (i.1,.inl i.2.1,i.2.2))
  let P : Frame (S × Raw e × Fin w) (S × Fin e.count × Fin w) :=
    Frame.initial (fun i => (i.1,.inl (some i.2.1),i.2.2))
  let L : Frame (S × Raw e × Fin w) (S × (Σ v : TemplateSite e, Location e v) × Fin w) :=
    Frame.initial (fun i => (i.1,.inr i.2.1,i.2.2))
  obtain ⟨head,hh,he⟩ := exists_headerFrame D e.count m w C
  obtain ⟨paid,hp,pe⟩ := PaidBox.exists_frame e w P
  let joined := Crossing.parallelFrame head (Crossing.parallelFrame paid L)
  let select (i : S × Prepared e × Fin w) := match i.2.1 with
    | .inl h => Sum.inl (i.1,h,i.2.2)
    | .inr (.inl p) => Sum.inr (Sum.inl (i.1,p,i.2.2))
    | .inr (.inr l) => Sum.inr (Sum.inr (i.1,l,i.2.2))
  refine ⟨(joined.select select).subst source, ?_, ?_⟩
  · simp only [Frame.subst_size,Frame.select_size,joined,Crossing.parallelFrame_size,L,Frame.initial_size,add_zero]
    simp only [C,P,Frame.initial_size,zero_add] at hh hp
    rw [Nat.add_mul,Nat.mul_add]
    omega
  · intro x s raw hfit r
    let input := source.eval x
    have hraw : (fun i => value (fun j => C.eval input (s,i,j))) = (fun i => raw (.inl i)) := by
      funext i
      simp [C,input,raw]
    rcases r with h | u | v
    · have hv : (fun j => ((joined.select select).subst source).eval x (s,.inl h,j)) =
          (fun j => head.eval input (s,h,j)) := by funext j; simp [joined,select,input]
      rw [hv]
      have h := he input s (hraw.symm ▸ hfit.1) h
      rw [hraw] at h
      exact h
    · have hv : (fun j => ((joined.select select).subst source).eval x (s,.inr (.inl u),j)) =
          (fun j => paid.eval input (s,u,j)) := by funext j; simp [joined,select,input]
      rw [hv]
      have hpin : value (fun j => P.eval input (s,u.1,j)) = raw (.inl (some u.1)) := by simp [P,input,raw]
      have h := pe input s u
      dsimp only at h
      rw [hpin] at h
      exact h (hfit.2 u)
    · simp [joined,select,L,word,raw]

/-- Operand type of a physical site's sparse packet. -/
noncomputable def Operands : TemplateSite e → Type
  | .inl _ | .inr (.inl _) => BankPacket.SiteInput D e.count
  | .inr (.inr ⟨a,v⟩) => BankPacket.Paid.Input (bundles e a v) (PaidBox.arity e a v)

noncomputable instance (v : TemplateSite e) : Fintype (Operands e v) := by
  rcases v with _ | _ | ⟨a,v⟩ <;> dsimp [Operands] <;> infer_instance

/-- Static word tape shape selected by the actual site tag of a paid seed bank. -/
noncomputable def rows (first : Fin D × Bool) : (v : TemplateSite e) → List (BankPacket.RecordCode (Operands e v))
  | .inl _ => BankPacket.origin m first
  | .inr (.inl _) => BankPacket.terminal m
  | .inr (.inr ⟨a,v⟩) => BankPacket.Paid.rows (PaidBox.widths (e.net a) v)

private def profilePin (v : TemplateSite e) (p : Slice D e.count → Bases e v) :
    BankPacket.SiteInput D e.count → Prepared e
  | none => .inr (.inr ⟨v,none⟩)
  | some (.inl h) => .inl h
  | some (.inr b) => .inr (.inr ⟨v,some (some (p b))⟩)

/-- Input pin wiring of the particular site template. It involves no query or search
over a histogram branch. -/
noncomputable def pin : (v : TemplateSite e) → Operands e v → Prepared e
  | .inl u => profilePin e (.inl u) id
  | .inr (.inl u) => profilePin e (.inr (.inl u)) id
  | .inr (.inr ⟨a,v⟩) => fun i => match i with
    | .inl _ => .inr (.inr ⟨.inr (.inr ⟨a,v⟩),none⟩)
    | .inr (.inl _) => .inr (.inr ⟨.inr (.inr ⟨a,v⟩),some none⟩)
    | .inr (.inr (.inl h)) => .inr (.inl ⟨a,v,h⟩)
    | .inr (.inr (.inr z)) => .inr (.inr ⟨.inr (.inr ⟨a,v⟩),some (some z)⟩)

end Packing.BankJoint

end BorderVNP
end Computability
end OAI
