import OAI.Computability.BorderVNP.PackedBankSiteProof

/-! # Locality of the complete native profile packets

The origin and terminal acceptance proofs reduce the record list to its
allocated auxiliary slab and physical cable lanes. Consequently two bank
assignments that agree on precisely these addresses give the same verdict.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankPacket

open Crossing.Profile Crossing.Profile.Cell BankCircuit CellSparse
open scoped Classical

variable {D A : ℕ} (b j : ℕ) (p : Fin A → ℕ) (x : SiteInput D A → ℕ)
variable (hx : localHeader x = headerWord b (fun i => i.elim j p)) (boxes : List (List Factor)) (f g : ℕ → Bool)

private theorem stages_congr {R : Type*} [Fintype R] (L : BankLayout R) (data : L.Data)
    (off : ℕ) (h : ∀ k : Fin (Fintype.card R * L.stride), f (off+k.val) = g (off+k.val)) :
    Stages L (fun k => f (off+k)) data ↔ Stages L (fun k => g (off+k)) data :=
  forall_congr' fun k => by dsimp only; rw [h k]

include hx in
/-- All possible origin checks agree when the auxiliary slab and source spokes agree. -/
theorem origin_congr (first : Fin D × Bool)
    (slab : ∀ k : Fin (Fintype.card (Fin D × Bool)*(originLayout (Fin D × Bool) j A).stride),
      f (x none+k.val) = g (x none+k.val))
    (cables : ∀ t (i : Fin j) (k : Fin (Nat.clog 2 A)),
      f ((physicalPort b x (.inl t)).atBit i k) = g ((physicalPort b x (.inl t)).atBit i k)) :
    (∀ r ∈ (origin (A := A) b first).map (RecordCode.read x),r.Valid boxes f) ↔
      ∀ r ∈ (origin (A := A) b first).map (RecordCode.read x),r.Valid boxes g := by
  apply (origin_accept_iff b j p x hx boxes f first).trans
  apply Iff.trans _ (origin_accept_iff b j p x hx boxes g first).symm
  let L := originLayout (Fin D × Bool) j A
  let bits (bank : ℕ → Bool) : L.Data := fun t i k => bank ((physicalPort b x (.inl t)).atBit i k)
  let s (bank : ℕ → Bool) := fun t => selector (A := A) (j := j) bank (physicalPort b x (.inl t))
  have hbits : bits f = bits g := funext fun t => funext fun i => funext (cables t i)
  have hs : s f = s g := funext fun t => funext fun i => funext fun k => congrArg finTwoEquiv.symm (cables t i k)
  change Stages L _ (bits f) ∧ originTest first p (s f) ↔ Stages L _ (bits g) ∧ originTest first p (s g)
  rw [hbits,hs]
  exact and_congr_left' (stages_congr f g L (bits g) (x none) slab)

/-- A linear bit of the staged original terminal word is inside its allocated slab. -/
theorem inputBit_lt (k : Fin (j*b)) :
    let L := terminalLayout j b p
    (L.port (.inr (.inl ()))).atBit 0 k.val < Fintype.card (Unit ⊕ Unit ⊕ Fin A)*L.stride := by
  intro L
  obtain ⟨⟨i,l⟩,rfl⟩ := finProdFinEquiv.surjective k
  rw [← input_address b j p i l]
  exact L.atBit_lt (.inr (.inl ())) i l

include hx in
/-- Terminal packet validity depends only on the allocated slab, the physical
selector and the compact feeders. Its staged input can be arbitrary. -/
theorem terminal_congr (hp : ∑ a,p a = j)
    (slab : ∀ k : Fin (Fintype.card (Unit ⊕ Unit ⊕ Fin A)*(terminalLayout j b p).stride),
      f (x none+k.val) = g (x none+k.val))
    (spoke : ∀ (i : Fin j) (k : Fin (Nat.clog 2 A)),
      f ((physicalPort b x (.inr (.inl ()))).atBit i k) = g ((physicalPort b x (.inr (.inl ()))).atBit i k))
    (feed : ∀ a (i : Fin (p a)) (k : Fin b), f ((physicalPort b x (.inr (.inr (.inr a)))).atBit i k) =
      g ((physicalPort b x (.inr (.inr (.inr a)))).atBit i k)) :
    (∀ r ∈ (terminal (D := D) (A := A) b).map (RecordCode.read x),r.Valid boxes f) ↔
      ∀ r ∈ (terminal (D := D) (A := A) b).map (RecordCode.read x),r.Valid boxes g := by
  let L := terminalLayout j b p
  let t := ((L.port (.inr (.inl ()))).shift (x none))
  let orig := fun k : Fin (j*b) => f (t.atBit 0 k)
  have hf (k : Fin (j*b)) : f (t.atBit 0 k) = orig k := rfl
  have hg (k : Fin (j*b)) : g (t.atBit 0 k) = orig k := by
    dsimp only [orig,t]
    rw [Port.atBit_shift]
    exact (slab ⟨_,inputBit_lt b j p k⟩).symm
  have htF := terminal_accept_iff b j p x hx boxes f hp orig
  have htG := terminal_accept_iff b j p x hx boxes g hp orig
  dsimp only at htF htG
  rw [and_iff_left hf] at htF
  rw [and_iff_left hg] at htG
  rw [htF,htG]
  let s (bank : ℕ → Bool) := selector (j := j) (A := A) bank (physicalPort b x (.inr (.inl ())))
  let y (bank : ℕ → Bool) := feeders (b := b) p bank (fun a => physicalPort b x (.inr (.inr (.inr a))))
  have hs : s f = s g := funext fun i => funext fun k => congrArg finTwoEquiv.symm (spoke i k)
  have hy : y f = y g := funext fun a => funext fun i => funext (feed a i)
  change Stages L _ (terminalData p (s f) (y f) orig) ∧ terminalTest p (s f) (y f) orig ↔
    Stages L _ (terminalData p (s g) (y g) orig) ∧ terminalTest p (s g) (y g) orig
  rw [hs,hy]
  exact and_congr_left' (stages_congr f g L _ (x none) slab)

end Packing.BankPacket

end BorderVNP
end Computability
end OAI
