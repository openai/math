import OAI.Computability.BorderVNP.PackedBankInstalledAddresses
import OAI.Computability.BorderVNP.PackedBankEmitBound
import OAI.Computability.BorderVNP.PackedBankBoxOrdinal

/-! # End-to-end packet stage on the public geometry directory

The preceding public passes expose the checked count fields and successor
directory. This stage resolves the actual shared/supplied word starts, computes
merged box numbers from the per-site box counts, and emits every tagged sparse
seed-site packet. The earlier gates and the branch-validity wire are shared.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankJoint

open Crossing Shortening.StaticRows CellAddressCircuit ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m) {S : Type*} [Fintype S]
variable {n u C d k w : ℕ} (seed : S ↪ Fin n) (oldSites oldEdges : ℕ)
variable {τ σ : Type*} [Fintype τ] [Fintype σ]
variable (F : Fields (siteCapacity e oldSites n) (edgeCapacity e oldEdges n) u C d k w τ)
variable (boxCount : Fin (siteCapacity e oldSites n) → Fin w → τ)

private def boxPins (i : BankBoxOrdinal.Input (siteCapacity e oldSites n) k w) : τ :=
  i.2.elim (F.owner i.1) (boxCount i.1)

/-- Exclusive owner-bucket box prefix on the actual successor directory, with the
same site cells as the physical wire/staging address pass. -/
noncomputable def directoryIDs : Frame τ (Fin (siteCapacity e oldSites n) × Fin w) :=
  (BankBoxOrdinal.frame _ _ _).subst (Frame.initial (boxPins e oldSites oldEdges F boxCount))

set_option maxHeartbeats 1000000 in
/-- The first box of a site is exactly the box selected by its merged directory ID.
This also covers inherited sites with several entries and sites contributing an empty list. -/
theorem directory_get {α : Type*} (x : τ → Bool) (boxes : Fin (siteCapacity e oldSites n) → List α)
    (hcount : ∀ v, value (x ∘ boxCount v) = (boxes v).length)
    (room : ∀ c, (BankBoxOrdinal.table (fun v => value (x ∘ F.owner v)) boxes c).length < 2^w)
    (v : Fin (siteCapacity e oldSites n)) (j : Fin (boxes v).length) (default : α) :
    (BankBoxOrdinal.table (fun v => value (x ∘ F.owner v)) boxes (value (x ∘ F.owner v))).getD
      (value (fun b => (directoryIDs e oldSites oldEdges F boxCount).eval x (v,b))+j.val) default =
      (boxes v).get j := by
  let z := (Frame.initial (boxPins e oldSites oldEdges F boxCount)).eval x
  have ho (v) : BankBoxOrdinal.ownerWord z v = value (x ∘ F.owner v) := by
    simp [BankBoxOrdinal.ownerWord,z,boxPins,Function.comp_def]
  have hc (v) : BankBoxOrdinal.countWord z v = (boxes v).length := by
    simpa [BankBoxOrdinal.countWord,z,boxPins,Function.comp_def] using hcount v
  have hv : (fun b => (directoryIDs e oldSites oldEdges F boxCount).eval x (v,b)) =
      (fun b => (BankBoxOrdinal.frame (siteCapacity e oldSites n) k w).eval z (v,b)) :=
    funext fun b => Frame.subst_eval _ _ x (v,b)
  rw [hv]
  exact BankBoxOrdinal.frame_getD z _ boxes ho hc room v j default

variable (countPin : S × Option (Fin e.count) × Fin w → τ)

/-- Actual raw word values at all installed locations on the successor's public bits. -/
noncomputable def directoryRaw (x : τ → Bool) (s : S) : Raw e → ℕ :=
  rawWord e seed oldSites oldEdges (Frame.initial countPin) (CellAddressViews.frame F)
    (directoryIDs e oldSites oldEdges F boxCount) x s

/-- Complete fixed seed-site packet stage, including the branch-validity return wire.
The polynomial bounds of the cell address, box scan and packet arithmetic phases are
charged once in addition to the previous public directory frame. -/
theorem pipeline (first : Fin D × Bool) (prior : Frame σ τ) (valid : τ) :
    ∃ f : Frame σ ((S × Output e first × Fin w) ⊕ Unit),
      f.size ≤ prior.size + (CellAddressViews.frame F).size +
        (2+2*(siteCapacity e oldSites n+1)*BankBoxOrdinal.laneCost (Nat.clog 2 (siteCapacity e oldSites n)) k w) +
        4 + Fintype.card S * ((BankCircuit.headerNodes D e.count m + PaidBox.nodeBound e + nodes e first) * (100*(w+1)^2)) ∧
      (∀ x, f.eval x (.inr ()) = prior.eval x valid) ∧
      ∀ x s, let raw := directoryRaw e seed oldSites oldEdges F boxCount countPin (prior.eval x) s
        Fits e w raw → ∀ z : Output e first, (expr e first z).Fits w (fun i => word e raw (pin e z.1 i)) →
          value (fun j => f.eval x (.inl (s,z,j))) =
          (CellSparse.Packet.fieldList CellSparse.Packet.record (emitted e first raw z.1))[z.2.val]?.getD 0 := by
  obtain ⟨pack,hsize,hpacket⟩ := installed_packets e seed oldSites oldEdges (Frame.initial countPin)
    (CellAddressViews.frame F) (directoryIDs e oldSites oldEdges F boxCount) first
  let flag : Frame τ Unit := Frame.initial (fun _ => valid)
  let full := (Crossing.parallelFrame pack flag).subst prior
  refine ⟨full,?_,fun x => by simp [full,flag],?_⟩
  · have hs := BankBoxOrdinal.frame_size (siteCapacity e oldSites n) k w
    simp only [Frame.initial_size,zero_add,directoryIDs,Frame.subst_size] at hsize
    simp only [full,flag,Frame.subst_size,Crossing.parallelFrame_size,Frame.initial_size,add_zero]
    omega
  · intro x s raw hfit z hword
    have h := hpacket (prior.eval x) s hfit z hword
    simp only [full,Frame.subst_eval,Crossing.parallelFrame_eval_inl]
    dsimp only [raw,directoryRaw]
    exact h

end Packing.BankJoint

end BorderVNP
end Computability
end OAI
