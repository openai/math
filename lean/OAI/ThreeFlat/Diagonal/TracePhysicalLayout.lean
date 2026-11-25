import OAI.ThreeFlat.Diagonal.TracePhysicalAddress
import OAI.ThreeFlat.Diagonal.TraceRowMasks

namespace OAI
/-! # XOR reachability of the addressed physical trace rows -/

namespace ThreeFlat.Diagonal.TracePhysical

open Computability.VPVNP
variable {w r S f d : ℕ}

private theorem packedFits (h : S+f ≤ 2^(1+d)) : S+f ≤ 2*2^d := by
  simpa [pow_add] using h

/-- The instruction with index t is stored in the row containing logical slot S+t. -/
def sharedOwner (fits : S+f ≤ 2^(1+d)) : Shared w r f d → Fin (2^d)
  | .inl (t,_) => ⟨(S+t.val)/2, by have := packedFits fits; have := t.isLt; omega⟩
  | .inr (.inl (_,v,_,_)) => v
  | .inr (.inr (v,_)) => ⟨v.val, by have := v.isLt; omega⟩

/-- Header bits belong to the site of the header's uncompressed address. -/
def headerOwner (fits : S+f ≤ 2^(1+d)) (j : Fin (S*w)) : Fin (2^d) :=
  let a := (finProdFinEquiv.symm j : Fin S × Fin w).1
  ⟨a.val/2, by have := a.isLt; have := packedFits fits; omega⟩

def hiddenOwner (fits : S+f ≤ 2^(1+d))
    (j : Fin (Fintype.card (Shared w r f d))) : Fin (2^d) :=
  sharedOwner fits ((sharedOrdinal w r f d).symm j)

def owner (fits : S+f ≤ 2^(1+d)) (v : Fin (2^d)) :
    BitSource (Fintype.card (Shared w r f d)) (S*w) → Fin (2^d)
  | .constant _ => v
  | .pin j => headerOwner fits j
  | .hidden j => hiddenOwner fits j

/-- The public list consists of zero, each single set bit, and each nonempty
low-bit prefix. It has exactly 1+2d entries for d binary row coordinates. -/
def offset (d : ℕ) : Fin (1+(d+d)) → Fin (2^d) :=
  Fin.addCases (fun _ => 0) (Fin.addCases
    (fun j => ⟨2^j.val, Nat.pow_lt_pow_right (by decide : 1 < 2) j.isLt⟩)
    (fun j => ⟨2^(j.val+1)-1, by
      have h := Nat.pow_le_pow_right (by decide : 0 < 2) j.isLt
      have := Nat.two_pow_pos (j.val+1)
      omega⟩))

theorem offset_zero (d : ℕ) : (offset d 0).val = 0 := by
  change (offset d (Fin.castAdd (d+d) (0 : Fin 1))).val = 0
  simp [offset]

theorem offset_single (j : Fin d) :
    (offset d (Fin.natAdd 1 (Fin.castAdd d j))).val = 2^j.val := by
  unfold offset
  rw [Fin.addCases_right, Fin.addCases_left]

theorem offset_low (j : Fin d) :
    (offset d (Fin.natAdd 1 (Fin.natAdd d j))).val = 2^(j.val+1)-1 := by
  unfold offset
  rw [Fin.addCases_right, Fin.addCases_right]

def Reached (v u : Fin (2^d)) : Prop :=
  ∃ k, u.val ^^^ v.val = (offset d k).val

theorem sameSite (v : Fin (2^d)) : Reached v v := ⟨0, by simp [offset_zero]⟩

theorem consecutive (v u : Fin (2^d)) (h : u.val = v.val+1 ∨ v.val = u.val+1) :
    Reached v u := by
  have step (a b : Fin (2^d)) (he : b.val = a.val+1) :
      ∃ k, a.val ^^^ b.val = (offset d k).val := by
    obtain ⟨k,hk,hd,hm⟩ := TraceRowMasks.adjacent_mask (d := d) (r := a.val) (he ▸ b.isLt)
    let j : Fin d := ⟨k-1, by omega⟩
    refine ⟨Fin.natAdd 1 (Fin.natAdd d j), ?_⟩
    have eq : j.val+1=k := by dsimp [j]; omega
    rw [offset_low, he, eq]
    exact hm
  rcases h with hn | hn
  · simpa [Reached, Nat.xor_comm] using step v u hn
  · exact step u v hn

private theorem xorGate (l : RAMLayout.Layer d) (v : Fin (2^d)) : Reached v (l.partner v) := by
  refine ⟨Fin.natAdd 1 (Fin.castAdd d ⟨l.siteBit, l.siteBit_lt⟩), ?_⟩
  change (v.val ^^^ 2^l.siteBit) ^^^ v.val = _
  rw [Nat.xor_comm v.val (2^l.siteBit), Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  exact (offset_single ⟨l.siteBit,l.siteBit_lt⟩).symm

/-- Every addressed port stays local, crosses one successor edge, or reads
the XOR partner indexed by that sort layer. -/
theorem reachable (hw : 2 ≤ w+1) (fits : S+f ≤ 2^(1+d)) (v : Fin (2^d)) (port : Port w r d) :
    ∃ k, (owner fits v (address hw S f v port)).val ^^^ v.val = (offset d k).val := by
  change Reached _ _
  have hs (i : Shared w r f d) : owner fits v (.hidden (sharedOrdinal w r f d i)) = sharedOwner fits i := by
    simp [owner, hiddenOwner]
  rcases port with ⟨c,j⟩ | (⟨s,k⟩ | (⟨l,own,s,j⟩ | ⟨out,j⟩))
  · simp only [address]
    split
    · rename_i hlow
      split
      · rename_i him
        change Reached v (owner fits v (.hidden (sharedOrdinal w r f d
          (.inl (⟨2*v.val+c.val-S,him⟩,j) : Shared w r f d))))
        rw [hs]
        let u := sharedOwner fits (.inl (⟨2*v.val+c.val-S,him⟩,j) : Shared w r f d)
        have hu : u.val = (2*v.val+c.val)/2 := by
          change (S+(2*v.val+c.val-S))/2 = _; congr 1; omega
        have hc := c.isLt
        by_cases hc2 : c.val=2
        · exact consecutive v u (Or.inl (by omega))
        · have he : u = v := Fin.ext (by omega)
          change Reached v u
          rw [he]
          exact sameSite _
      · exact sameSite _
    · exact sameSite _
  · simp only [address]
    split
    · rename_i h
      change Reached v (headerOwner (w := w) fits (finProdFinEquiv (⟨2*v.val+s.val,h⟩,k)))
      have eq : headerOwner (w := w) fits (finProdFinEquiv (⟨2*v.val+s.val,h⟩,k)) = v := by
        apply Fin.ext
        simp only [headerOwner, Equiv.symm_apply_apply]
        have := s.isLt
        omega
      rw [eq]
      exact sameSite _
    · exact sameSite _
  · cases own <;> simp only [address, Bool.false_eq_true, ite_false, ite_true]
    · change Reached v (owner fits v (.hidden (sharedOrdinal w r f d
        (.inr (.inl (l,_,s,j)) : Shared w r f d))))
      rw [hs]
      exact xorGate _ _
    · change Reached v (owner fits v (.hidden (sharedOrdinal w r f d
        (.inr (.inl (l,_,s,j)) : Shared w r f d))))
      rw [hs]
      exact sameSite _
  · cases out <;> simp only [address, Bool.false_eq_true, ite_false, ite_true] <;> split
    · rename_i h
      change Reached v (owner fits v (.hidden (sharedOrdinal w r f d
        (.inr (.inr (⟨v.val-1,_⟩,j)) : Shared w r f d))))
      rw [hs]
      exact consecutive _ _ (Or.inr (by change v.val = v.val-1+1; omega))
    · exact sameSite _
    · change Reached v (owner fits v (.hidden (sharedOrdinal w r f d
        (.inr (.inr (⟨v.val,_⟩,j)) : Shared w r f d))))
      rw [hs]
      exact sameSite _
    · exact sameSite _

/-- The least matching public displacement. The search visits only the
1+2d published offsets. -/
def code (hw : 2 ≤ w+1) (fits : S+f ≤ 2^(1+d)) (v : Fin (2^d)) (port : Port w r d) :
    Fin (1+(d+d)) :=
  Fin.find (fun k => (owner fits v (address hw S f v port)).val ^^^ v.val = (offset d k).val)
    (reachable hw fits v port)

theorem code_reaches (hw : 2 ≤ w+1) (fits : S+f ≤ 2^(1+d)) (v : Fin (2^d)) (port : Port w r d) :
    v.val = (owner fits v (address hw S f v port)).val ^^^ (offset d (code hw fits v port)).val := by
  have h := Fin.find_spec (reachable hw fits v port)
  change _ ^^^ _ = (offset d (code hw fits v port)).val at h
  rw [← h]
  simp

end ThreeFlat.Diagonal.TracePhysical

end OAI
