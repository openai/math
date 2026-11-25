import OAI.Computability.BorderVNP.PackedBankEmit
import OAI.Computability.BorderVNP.PackedBankHooks
import OAI.Computability.BorderVNP.PackedBankSiteProof

/-! # Physical site acceptance for an emitted seed and its clipped hooks

The seed compiler's actual origin packet and terminal packets read the public
site offsets and canonical cable starts. The terminal assignments may belong to
different cells. Each clipped wire supplies its own side of the gathered word.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankJoint

open Crossing Crossing.Profile Crossing.Profile.Cell Shortening Shortening.SeedIntervals
open BankPacket BankCircuit CellSparse
open scoped Classical

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)
variable (raw : Raw e → ℕ)

/-- The public operands of the seed's origin packet. -/
noncomputable def originWords : SiteInput D e.count → ℕ :=
  fun i => word e raw (pin e (.inl ()) i)

/-- The public operands of one actual terminal of the seed. -/
noncomputable def terminalWords (t : Fin D × Bool) : SiteInput D e.count → ℕ :=
  fun i => word e raw (pin e (.inr (.inl t)) i)

variable (first : Fin D × Bool)

/-- The returned origin records test the selector words at the physical bases
and fix all allocated bits behind the emitted origin offset. -/
theorem emitted_origin_accept (j : ℕ) (p : Fin e.count → ℕ)
    (hcount : ∀ i, raw (.inl i) = i.elim j p) (boxes : List (List Factor)) (bank : ℕ → Bool) :
    let x := originWords e raw
    let L := originLayout (Fin D × Bool) j e.count
    let phys := fun u => physicalPort m x (.inl u)
    (∀ r ∈ emitted e first raw (.inl ()),r.Valid boxes bank) ↔
      Stages L (fun t => bank (x none+t)) (fun u i k => bank ((phys u).atBit i k)) ∧
        originTest first p (fun u => selector (j := j) bank (phys u)) := by
  apply origin_accept_iff
  change headerWord (D := D) m (fun i => raw (.inl i)) = _
  rw [funext hcount]

/-- The linear terminal destination addressed by all clipped hooks of this orientation. -/
noncomputable def gatheredPort (j : ℕ) (p : Fin e.count → ℕ) (t : Fin D × Bool) : Port :=
  ((terminalLayout j m p).port (.inr (.inl ()))).shift (terminalWords e raw t none)

variable [NeZero D] {P : Type*} {bits : P → ℕ} (N : Network D P bits)
variable {S : Type} (bin : N.Edge → Option S) (perm : Fin D → Equiv.Perm S)
variable (binName : S → ℕ) (siteName : N.Site → ℕ) (positive : N.Edge → Bool) (a : S)
variable (cuts : Ports ((layout N bin perm m).cutWidths ((partition N bin perm m).part a)))
variable (hooks : ∀ d, {z : N.Edge // bin z = some (perm d a)} → Bool → Port)
variable (boxes : Fin D × Bool → List (List Factor)) (bank : Fin D × Bool → ℕ → Bool)

/-- All emitted terminal packets and all clipped-hook rows accept exactly the
physical terminal predicates on the true gathered exterior words. Each accepted
assignment has the prescribed padded auxiliary bits at every terminal. -/
theorem emitted_terminals_hooks_accept (p : Fin e.count → ℕ)
    (hp : ∑ t, p t = blocks N bin perm m a)
    (hcount : ∀ i, raw (.inl i) = i.elim (blocks N bin perm m a) p)
    (hread : ∀ d z src k, let r := endpointRecord N bin perm m binName siteName positive a d z src
      bank (d,r.side) ((hooks d z src).atBit 0 k.val) = hookBit N bin perm m a cuts d z src k) :
    let j := blocks N bin perm m a
    let L := terminalLayout j m p
    let gathered := (bundle N bin perm m positive a).gather cuts
    ((∀ t r, r ∈ emitted e first raw (.inr (.inl t)) → r.Valid (boxes t) (bank t)) ∧
      ∀ d z src, let r := endpointRecord N bin perm m binName siteName positive a d z src
        (directHook r.wire (hooks d z src) (gatheredPort e raw j p (d,r.side))).Valid
          (boxes (d,r.side)) (bank (d,r.side))) ↔
    ∀ t, let x := terminalWords e raw t
      let phys := fun r => physicalPort m x (.inr r)
      let s := selector (A := e.count) (j := j) (bank t) (phys (.inl ()))
      let f := feeders (b := m) p (bank t) (fun a' => phys (.inr (.inr a')))
      Stages L (fun i => bank t (x none+i)) (terminalData p s f (gathered t)) ∧
        terminalTest p s f (gathered t) := by
  intro j L gathered
  rw [directHooksAt_iff N bin perm m binName siteName positive a cuts hooks
    (gatheredPort e raw j p) boxes bank hread]
  have hh (t : Fin D × Bool) :
      localHeader (terminalWords e raw t) = headerWord m (fun i => i.elim j p) := by
    change headerWord (D := D) m (fun i => raw (.inl i)) = _
    rw [funext hcount]
  have one (t : Fin D × Bool) := terminal_accept_iff m j p (terminalWords e raw t) (hh t)
    (boxes t) (bank t) hp (gathered t)
  constructor
  · rintro ⟨hrec,hhook⟩ t
    exact (one t).mp ⟨hrec t,hhook t⟩
  · intro h
    exact ⟨fun t => ((one t).mpr (h t)).1,fun t => ((one t).mpr (h t)).2⟩

end Packing.BankJoint

end BorderVNP
end Computability
end OAI
