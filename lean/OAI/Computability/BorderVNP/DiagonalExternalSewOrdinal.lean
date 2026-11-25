import OAI.Computability.BorderVNP.DiagonalExternalSewFourSlotLive
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Stable public row ordinals of all four-slot exterior cable candidates -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.FourSlot

/-- The two probe bits are stored in high/low order. -/
def bitPair : Bool × Bool ≃ Fin 4 :=
  (Equiv.prodCongr finTwoEquiv.symm finTwoEquiv.symm).trans finProdFinEquiv

/-- Row-major ordering with the team varying slowest and the probe bits fastest. -/
def slotOrdinal (teams sites : ℕ) : (Fin teams × Fin sites × (Bool×Bool)) ≃ Fin (4*teams*sites) :=
  (((Equiv.prodCongr (Equiv.refl _) ((Equiv.prodCongr (Equiv.refl _) bitPair).trans finProdFinEquiv)).trans
    finProdFinEquiv).trans (finCongr (by ring)))

/-- Numeric form of the stable ordinal. -/
theorem slotOrdinal_val {teams sites : ℕ} (u : Fin teams) (s : Fin sites) (a b : Bool) :
    (slotOrdinal teams sites (u,s,a,b)).val = (u.val*sites+s.val)*4 + 2*a.toNat + b.toNat := by
  cases a <;> cases b <;> change _ + (sites*4)*u.val = _ <;>
    simp [bitPair,finTwoEquiv,finProdFinEquiv] <;> ring

/-- The stable exterior directory is appended after the fixed old cable rectangle. -/
def appendedSlot (old teams sites : ℕ) (x : Fin teams × Fin sites × (Bool×Bool)) : Fin (old+4*teams*sites) :=
  Fin.natAdd old (slotOrdinal teams sites x)

/-- Decoding by quotient and remainder returns the original team, site and both probes. -/
theorem appendedSlot_decode (old : ℕ) {teams sites : ℕ} (u : Fin teams) (s : Fin sites) (a b : Bool) :
    let idx := (appendedSlot old teams sites (u,s,a,b)).val - old
    idx/4/sites = u.val ∧ idx/4%sites = s.val ∧ idx%4/2 = a.toNat ∧ idx%4%2 = b.toNat := by
  have hs : 0 < sites := Nat.zero_lt_of_lt s.isLt
  dsimp only
  have addr : (appendedSlot old teams sites (u,s,a,b)).val = old+(slotOrdinal teams sites (u,s,a,b)).val := rfl
  rw [addr,Nat.add_sub_cancel_left,slotOrdinal_val]
  have digit : 2*a.toNat+b.toNat < 4 := by cases a <;> cases b <;> decide
  have parts : (2*a.toNat+b.toNat)/2 = a.toNat ∧ (2*a.toNat+b.toNat)%2 = b.toNat := by
    cases a <;> cases b <;> decide
  rw [Nat.add_assoc,Nat.mul_comm _ 4,Nat.mul_comm u.val sites]
  simp only [Nat.mul_add_div (by decide : 0 < 4),Nat.div_eq_of_lt digit,Nat.add_zero,
    Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt digit,Nat.mul_add_div hs,Nat.div_eq_of_lt s.isLt,Nat.mod_eq_of_lt s.isLt,
    parts.1,parts.2,true_and]

/-- Each physical nonempty interval has its actual unique row in the appended
directory. All reserved probe positions fit even when no interval occupies them. -/
def pieceOrdinal {R r literal stride link g : ℕ} (old sites : ℕ) (hg : 0 < g)
    (small : g ≤ link) (fit : literal+R*link ≤ stride) (room : r*stride ≤ sites*g) :
    Pieces (fieldStart (R := R) (r := r) literal stride link) g link ↪ Fin (old+4*(R+1)*sites) where
  toFun c := appendedSlot old (R+1) sites (index sites hg fit room c)
  inj' := by
    intro a b eq
    apply index_injective sites hg small fit room
    apply (slotOrdinal (R+1) sites).injective
    apply Fin.ext
    have h := congrArg Fin.val eq
    change old+_ = old+_ at h
    exact Nat.add_left_cancel h

end Diagonal.ExternalSew.FourSlot

end BorderVNP
end Computability
end OAI
