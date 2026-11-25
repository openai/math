import OAI.Computability.BorderVNP.DiagonalTallyReportWrites
import OAI.Computability.BorderVNP.DiagonalTallyCountChecked

/-! # Absolute readback and uniqueness of the compact report choice bits -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open RoutingISA VPVNP.BurstRAM VPVNP.TapeWord

/-- Each physical raw bit in a list occupies one ordinary word. -/
def literalBitsAt (m : ℕ → ℕ) (p : ℕ) (bs : List Bool) := CellPacket.WordsAt m p (bs.map Bool.toNat)

/-- Read a list of bundles in the same order as the actual use report tail. -/
def useBitsAt (m : ℕ → ℕ) : ℕ → List ReportBundle → Prop
  | _,[] => True
  | p,b::bs => (∀ i : Fin b.useCount,m (p+i.val)=(b.uses i).toNat) ∧
    useBitsAt m (p+b.useCount) bs

private theorem ofFn_bits {n : ℕ} (m : ℕ → ℕ) (p : ℕ) (f : Fin n → Bool)
    (h : literalBitsAt m p (List.ofFn f)) (i : Fin n) : m (p+i.val)=(f i).toNat := by
  simpa using h ⟨i.val,by simp⟩

private theorem count_bits {u H : ℕ} (m : ℕ → ℕ) (p : ℕ) (f : Fin u → Fin H → Bool)
    (h : literalBitsAt m p (List.ofFn fun g => List.ofFn (f g)).flatten) :
    ∀ g j, m (p+g.val*H+j.val)=(f g j).toNat := by
  induction u generalizing p with
  | zero => exact fun g => g.elim0
  | succ u ih =>
    rw [literalBitsAt,List.ofFn_succ,List.flatten_cons,List.map_append] at h
    intro g
    refine Fin.cases ?_ (fun i j => ?_) g
    · intro j
      simpa using ofFn_bits m p (f 0) h.left j
    · have hr : literalBitsAt m (p+H) (List.ofFn fun g => List.ofFn (f g.succ)).flatten := by
        simpa only [literalBitsAt,List.length_map,List.length_ofFn] using h.right
      simpa [Nat.succ_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ih (p+H) (fun g => f g.succ) hr i j

private theorem use_bits (m : ℕ → ℕ) (p : ℕ) (bs : List ReportBundle)
    (h : literalBitsAt m p (bs.flatMap fun b => List.ofFn b.uses)) : useBitsAt m p bs := by
  induction bs generalizing p with
  | nil => trivial
  | cons b bs ih =>
    rw [literalBitsAt,List.flatMap_cons,List.map_append] at h
    exact ⟨ofFn_bits m p b.uses h.left,ih (p+b.useCount) (by
      simpa only [literalBitsAt,List.length_map,List.length_ofFn,ReportBundle.useCount] using h.right)⟩

/-- Any later memory retaining the genuine contiguous choice words supplies the checked
gadget fields and exactly one use bit per represented marked copy. -/
theorem ReportCell.readBits {l : ReportLayout} (c : ReportCell l) (m : ℕ → ℕ)
    (h : literalBitsAt m (c.external+c.supplied) c.bits) :
    (∀ g j, m (c.external+c.supplied+g.val*l.countWidth+j.val)=(c.counts g j).toNat) ∧
    useBitsAt m (c.external+c.supplied+l.gadgets*l.countWidth) c.bundles := by
  rw [literalBitsAt,bits,List.map_append] at h
  refine ⟨count_bits _ _ _ h.left,use_bits _ _ _ ?_⟩
  simpa [literalBitsAt,List.length_flatten,List.map_ofFn,Function.comp_def,List.ofFn_const] using h.right

/-- Checking a fixed-width gadget multiplicity forces every physically guessed digit of it. -/
theorem countBits_unique {n : ℕ} (a b : Fin n → Bool)
    (h : value (List.ofFn a)=value (List.ofFn b)) : a=b :=
  List.ofFn_injective (eq_of_length_value (by simp) h)

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
