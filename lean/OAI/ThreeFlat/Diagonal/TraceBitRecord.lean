import OAI.ThreeFlat.Diagonal.TraceBitRecordData
import OAI.ThreeFlat.Diagonal.TraceBitHeader

namespace OAI
/-! # Numerical source addresses with one open input bit per header word -/

namespace ThreeFlat.Diagonal.TraceAddressRecord

open Computability.VPVNP TracePhysical TraceUniformRow TraceBitHeader RAM.BitLayout
variable {w p r k d S f : ℕ}

private def active (R : Record) (v : ℕ) := R.lo ≤ R.test v ∧ R.test v < R.hi
private instance (R : Record) (v : ℕ) : Decidable (active R v) := by unfold active; infer_instance

private theorem changed {n S w : ℕ} (R : Record) (v : ℕ) (s : BitSource n (S*w))
    (hw : 0<w) (noBit : R.bit=none) (orig : R.eval v = sourceAddress s)
    (tag : if active R v then ∃ i, s = .hidden i else ∃ b, s = .constant b) :
    (changeBase R (S*w-S)).eval v = sourceAddress (relabel bitPin s) := by
  have lower : S≤S*w := Nat.le_mul_of_pos_right _ hw
  by_cases h : active R v
  · rw [ite_eq_left h] at tag
    obtain ⟨i,rfl⟩ := tag
    unfold active at h
    rw [Record.eval,ite_eq_left h] at orig
    simp only [noBit,Record.result,sourceAddress] at orig
    simp only [changeBase,Record.eval,Record.test,Record.result,Record.numerator,noBit,
      relabel,sourceAddress]
    change (if R.lo ≤ R.test v ∧ R.test v < R.hi then R.numerator v-(R.sub+(S*w-S))
      else R.fallback) = hiddenBase S+i.val
    rw [ite_eq_left h,← Nat.sub_sub,orig]
    unfold hiddenBase
    omega
  · rw [ite_eq_right h] at tag
    obtain ⟨b,rfl⟩ := tag
    unfold active at h
    simp only [Record.eval,h,ite_false,sourceAddress] at orig
    change (if R.lo ≤ R.test v ∧ R.test v < R.hi then _ else R.fallback) = b.toNat
    rwa [ite_eq_right h]

theorem bitPort_eval (hw : 3≤w+1) (base S f : ℕ) (v : Fin (2^d)) (z : TraceUniformRow.Port w p r k d) :
    (bitPort hw base S f z).eval v.val = sourceAddress (relabel bitPin (addresses (by omega) S f v z)) := by
  have pos : 0<w := by omega
  let : Nonempty (Fin (SharedCount w p r k d f)) :=
    ⟨⟨0,by unfold SharedCount CopyCount; positivity⟩⟩
  rcases z with (⟨c,j⟩ | (⟨s,j⟩ | (⟨l,own,s,j⟩ | ⟨out,j⟩))) | ⟨future,j⟩
  · apply changed _ _ _ pos rfl (portRecord_eval _ _ _ _ _)
    by_cases lo : S≤2*v.val+c.val <;> by_cases hi : 2*v.val+c.val-S < f
    all_goals have eq : (S≤2*v.val+c.val ∧ 2*v.val+c.val<S+f) ↔
        (S≤2*v.val+c.val ∧ 2*v.val+c.val-S<f) := by omega
    all_goals simp [active,Record.test,portRecord,ordinary,addresses,TracePhysical.address,
      keepSource,shared,lo,hi]
    all_goals omega
  · by_cases h : 2*v.val+s.val<S <;> by_cases low : j.val=0
    all_goals simp [bitPort,bitHeader,Record.eval,Record.test,Record.result,Record.numerator,
      addresses,TracePhysical.address,keepSource,relabel,bitPin,sourceAddress,h,low]
    all_goals omega
  · apply changed _ _ _ pos rfl (portRecord_eval _ _ _ _ _)
    simp [active,Record.test,portRecord,ordinary,addresses,TracePhysical.address,keepSource,shared]
  · cases out with
    | false =>
      apply changed _ _ _ pos rfl (portRecord_eval _ _ _ _ _)
      by_cases h : 0<v.val
      · have lo : 1≤v.val := h
        simp [active,Record.test,portRecord,ordinary,addresses,TracePhysical.address,keepSource,
          shared,lo,h,v.isLt]
      · have lo : ¬1≤v.val := h
        simp [active,Record.test,portRecord,ordinary,addresses,TracePhysical.address,keepSource,
          h,lo]
    | true =>
      apply changed _ _ _ pos rfl (portRecord_eval _ _ _ _ _)
      have eq : v.val<2^d-1 ↔ v.val+1<2^d := by omega
      by_cases h : v.val+1<2^d <;>
        simp [active,Record.test,portRecord,ordinary,addresses,TracePhysical.address,keepSource,
          shared,eq,h]
  · cases future with
    | false =>
      apply changed _ _ _ pos rfl (portRecord_eval _ _ _ _ _)
      simp [active,Record.test,portRecord,addresses]
    | true =>
      apply changed _ _ _ pos rfl (portRecord_eval _ _ _ _ _)
      have eq : v.val<2^d-1 ↔ v.val+1<2^d := by omega
      by_cases h : v.val+1<2^d <;> simp [active,Record.test,portRecord,addresses,eq,h]

end ThreeFlat.Diagonal.TraceAddressRecord

end OAI
