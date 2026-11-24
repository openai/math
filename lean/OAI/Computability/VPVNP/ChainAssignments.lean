import OAI.Computability.VPVNP.PairedChain

/-! # Reindexing all shared bits of the live and primed chains

Groups and cuts are indexed consecutively. A bit on an even cut is an exterior
bit of the adjacent pairs. Bits on an odd cut and the send bits of its two
groups belong to just one pair. The bijection below makes the regrouping in
(9.2)–(9.5) independent of the bit values and the site computations.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ChainAssignments

open CutSchedule ExponentTrace
open scoped Classical

/-- Identify pair `i` and side `g` with group `2*i+g` in the chain of `2^(h+1)` groups. -/
def group (h : ℕ) : Fin (2^h) × Fin 2 ≃ Fin (2^(h+1)) where
  toFun a := ⟨2 * a.1.val + a.2.val, by have := a.1.isLt; have := a.2.isLt; rw [pow_succ]; omega⟩
  invFun j := (⟨j.val / 2, by have := j.isLt; have := pow_succ (2 : ℕ) h; omega⟩, ⟨j.val % 2, by omega⟩)
  left_inv a := by
    obtain ⟨i, j⟩ := a
    apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega
  right_inv j := by apply Fin.ext; dsimp; omega

/-- Index `2*i` of exterior cut `i` after grouping the chain into adjacent pairs, including the
two end cuts. -/
def evenCut (h : ℕ) (i : Fin (2^h+1)) : Fin (2^(h+1)+1) :=
  ⟨2*i.val, by have := i.isLt; rw [pow_succ]; omega⟩

/-- Index `2*i+1` of the cut between the two groups of pair `i`. -/
def oddCut (h : ℕ) (i : Fin (2^h)) : Fin (2^(h+1)+1) :=
  ⟨2*i.val+1, by have := i.isLt; rw [pow_succ]; omega⟩

/-- Partition all cuts of the unpaired chain into the even cuts bounding pairs and the odd cuts
internal to individual pairs. -/
def cut (h : ℕ) : Fin (2^h+1) ⊕ Fin (2^h) ≃ Fin (2^(h+1)+1) where
  toFun := Sum.elim (evenCut h) (oddCut h)
  invFun j := if hj : j.val % 2 = 0 then .inl ⟨j.val/2, by have := j.isLt; have := pow_succ (2 : ℕ) h; omega⟩
    else .inr ⟨j.val/2, by have := j.isLt; have := pow_succ (2 : ℕ) h; omega⟩
  left_inv a := by
    rcases a with i | i
    · simp [evenCut]
    · simp [oddCut, Nat.mul_add_div]
  right_inv j := by
    dsimp only
    split <;> apply Fin.ext <;> dsimp [evenCut, oddCut] <;> omega

/-- An assignment of a bit string of the prescribed width to each of the `2^(h+1)+1` cuts of
the chain. -/
abbrev AllCuts (h Δ : ℕ) := (j : Fin (2^(h+1)+1)) → Bits (width (h+1) Δ j.val)

/-- A full assignment of chain cut strings together with a Boolean value for every shared RAM
bit of every group. -/
abbrev Shared (h Δ r bucket w : ℕ) :=
  AllCuts h Δ × (Fin (2^(h+1)) → RAMLayout.SharedBit r bucket w → Bool)

variable {h Δ a r bucket w n : ℕ}

private def cutFields : AllCuts h Δ ≃ Exterior h Δ ×
    ((i : Fin (2^h)) → Bits (width (h+1) Δ (2*i.val+1))) :=
  (Equiv.piCongrLeft (fun j : Fin (2^(h+1)+1) => Bits (width (h+1) Δ j.val))
    (cut h)).symm.trans (Equiv.sumPiEquivProdPi _)

private def groupFields :
    (Fin (2^(h+1)) → RAMLayout.SharedBit r bucket w → Bool) ≃
    ((i : Fin (2^h)) → Fin 2 → RAMLayout.SharedBit r bucket w → Bool) :=
  ((group h).symm.arrowCongr (Equiv.refl _)).trans (Equiv.curry _ _ _)

private def pairFields : (((i : Fin (2^h)) → Bits (width (h+1) Δ (2*i.val+1))) ×
    ((i : Fin (2^h)) → Fin 2 → RAMLayout.SharedBit r bucket w → Bool)) ≃
    ((i : Fin (2^h)) → PairedChain.PairBits h Δ a r bucket w i) where
  toFun x i := Sum.elim (x.1 i) fun p => x.2 i p.1 p.2
  invFun x := (fun i b => x i (.inl b), fun i g b => x i (.inr (g,b)))
  left_inv _ := rfl
  right_inv x := by funext i b; rcases b with b | ⟨g,b⟩ <;> rfl

/-- Each physical assignment supplies exactly one exterior assignment and one
independent internal assignment per pair, and conversely. -/
def split : Shared h Δ r bucket w ≃
    Exterior h Δ × ((i : Fin (2^h)) → PairedChain.PairBits h Δ a r bucket w i) :=
  (cutFields.prodCongr groupFields).trans ((Equiv.prodAssoc _ _ _).trans
    ((Equiv.refl _).prodCongr pairFields))

@[simp] theorem split_even (data : Shared h Δ r bucket w) (i : Fin (2^h+1)) :
    ((split (a := a)) data).1 i = data.1 (evenCut h i) := rfl

@[simp] theorem split_odd (data : Shared h Δ r bucket w) (i : Fin (2^h))
    (b : Fin (width (h+1) Δ (2*i.val+1))) :
    ((split (a := a)) data).2 i (.inl b) = data.1 (oddCut h i) b := rfl

@[simp] theorem split_send (data : Shared h Δ r bucket w) (i : Fin (2^h))
    (g : Fin 2) (b : RAMLayout.SharedBit r bucket w) :
    ((split (a := a)) data).2 i (.inr (g,b)) = data.2 (group h (i,g)) b := rfl

/-- Read an index, advice, or cut field at the site address. Unused
endpoints and addresses beyond the field length are clamped to zero. -/
def distributedBit {d : ℕ} (bits : Bits d) (addr : ℕ) : Bool :=
  if h : addr < d then bits ⟨addr, h⟩ else false

/-- Form processor `v`'s header for group `j` from its distributed bits of the one-based group
number, advice, and left and right cut strings. -/
def physicalHeader (advice : Bits a) (cuts : AllCuts h Δ)
    (j : Fin (2^(h+1))) (v : Fin (2^r)) : BurstRAM.ProcessorInput.Header :=
  let number : BurstRAM.Word (h+2) := ⟨j.val + 1, by
    have := j.isLt
    have : 2^(h+2) = 2^(h+1) * 2 := pow_succ 2 (h+1)
    have := Nat.two_pow_pos (h+1)
    omega⟩
  BurstRAM.ProcessorInput.header
    (distributedBit (RAMSerialization.wordBits _ number) v.val)
    (distributedBit advice v.val)
    (distributedBit (cuts j.castSucc) v.val)
    (distributedBit (cuts j.succ) v.val)

/-- An actual tape in the unpaired chain. Consecutive groups read the same
cut field, and a receive port reads the bit of its physical send endpoint. -/
def physicalInput (p : UniversalMachine.Program)
    (hf : BurstRAM.ProcessorInput.Fits p n r bucket w) (advice : Bits a)
    (data : Shared h Δ r bucket w) (j : Fin (2^(h+1))) (v : Fin (2^r)) : Fin n → Bool :=
  BurstRAM.ProcessorInput.encode p n v (physicalHeader advice data.1 j v)
    (fun u => (RAMLayout.assignmentEquiv r bucket w (data.2 j)).val
      (v, (RAMLayout.offset r bucket w).symm u)) hf

theorem physicalInput_at_pair (p : UniversalMachine.Program)
    (hf : BurstRAM.ProcessorInput.Fits p n r bucket w) (advice : Bits a)
    (data : Shared h Δ r bucket w) (i : Fin (2^h)) (g : Fin 2) (v : Fin (2^r)) :
    physicalInput p hf advice data (group h (i,g)) v =
    PairedChain.siteInput p hf advice ((split (a := a)) data).1 i
      (((split (a := a)) data).2 i) (g,v) := by
  unfold physicalInput PairedChain.siteInput PrimedInputRAM.input
  congr 1
  funext j
  fin_cases g <;> fin_cases j <;>
    simp [physicalHeader, BurstRAM.ProcessorInput.header, PrimedInputRAM.siteHeader,
      PrimedInputRAM.headerRef, PairedChain.lengths, distributedBit,
      PrimedInputRAM.Ref.value, PairedChain.headers, group, evenCut, PairedChain.groupIndex,
      Nat.mul_succ] <;>
    split_ifs <;> simp only [*, ↓reduceDIte] <;> rfl

/-- The full contraction written with one variable for each physical shared bit,
one factor per group, and one factor per site in the group. -/
noncomputable def unpaired (p : UniversalMachine.Program)
    (hf : BurstRAM.ProcessorInput.Fits p n r bucket w) (advice : Bits a) : ℕ :=
  ∑ data : Shared h Δ r bucket w, ∏ j : Fin (2^(h+1)), ∏ v : Fin (2^r),
    acceptingCount (physicalInput p hf advice data j v)

/-- Pairing consecutive factors preserves the integer contraction. -/
theorem unpaired_eq_original (p : UniversalMachine.Program)
    (hf : BurstRAM.ProcessorInput.Fits p n r bucket w) (advice : Bits a) :
    unpaired (h := h) (Δ := Δ) p hf advice = PairedChain.original (h := h) (Δ := Δ) p hf advice := by
  unfold unpaired PairedChain.original Diagonal.originalContraction
  rw [← (split (h := h) (Δ := Δ) (a := a) (r := r) (bucket := bucket) (w := w)).symm.sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ξ _
  apply Finset.sum_congr rfl
  intro b _
  rw [← (group h).prod_comp]
  simp only [Fintype.prod_prod_type, physicalInput_at_pair, Equiv.apply_symm_apply]

end ChainAssignments

end VPVNP
end Computability
end OAI
