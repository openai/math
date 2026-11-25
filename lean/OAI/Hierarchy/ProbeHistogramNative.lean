import OAI.Hierarchy.ProbeBatchReplacement
import OAI.ThreeFlat.Diagonal.MotifSelectorChecks
import OAI.ThreeFlat.Diagonal.MotifBinaryPacking
import OAI.ThreeFlat.Routing.StableCompactNative
import OAI.ThreeFlat.Routing.StableCompactionPadRows

namespace OAI
/-! # The trivalent network for checking a finite packet selector histogram

One bounded LUT per copy rejects unused binary codes and writes its
one-hot symbol mask. One stable compactor per letter counts the mask,
whose target count is fixed by the outer histogram. -/

noncomputable section
namespace Hierarchy.Probe.NativeHistogram

open scoped Classical BigOperators
open ThreeFlat
open Diagonal Diagonal.MotifOuterTerms Routing Routing.StableCompaction
open Diagonal.TraceCircuit

variable {F : Type*} [CommRing F] {H s r : ℕ}

private def dyadic (r : ℕ) := Nat.log 2 (r+1) + 1

private theorem room (r : ℕ) : r ≤ 2^(dyadic r) :=
  (Nat.le_succ _).trans (Nat.lt_pow_succ_log_self (by decide : 1 < 2) _).le

private theorem dyadic_le (r : ℕ) : 2^(dyadic r) ≤ 2*(r+1) := by
  rw [dyadic,pow_succ,Nat.mul_comm]
  exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (Nat.succ_ne_zero _))

def compactor (F : Type*) [CommRing F] (r : ℕ) : BitNetwork F (r+(r+r)) :=
  restrictRows (StableCompactNative.network F (dyadic r)) r

theorem compactor_run (F : Type*) [CommRing F] (r : ℕ) (mask data out : Fin r→Bool) :
    (compactor F r).eval (Fin.append mask (Fin.append data out))=
      if out=compact mask data then 1 else 0 :=
  restrictRows_eval (room r) _ (StableCompactNative.network_eval (dyadic r)) mask data out

theorem compactor_size (F : Type*) [CommRing F] (r : ℕ) :
    (compactor F r).cells+(compactor F r).internal≤128000*(r+1)*(Nat.log 2 (r+1)+2)^3 := by
  have up := Nat.mul_le_mul_right (32000*(dyadic r+1)^3) (dyadic_le r)
  have c : (compactor F r).cells≤2*(r+1)*(32000*(dyadic r+1)^3) :=
    (StableCompactNative.network_cells F (dyadic r)).trans up
  have i : (compactor F r).internal≤2*(r+1)*(32000*(dyadic r+1)^3) :=
    (StableCompactNative.network_internal F (dyadic r)).trans up
  exact (Nat.add_le_add c i).trans_eq (by unfold dyadic;ring)

def valid (H : ℕ) (v : Fin s → Bool) : Prop := (MotifBinaryPacking.word s v).val < H

def letter {H : ℕ} (positive : 0 < H) (v : Fin s → Bool) : Fin H :=
  if ok : valid H v then ⟨(MotifBinaryPacking.word s v).val,ok⟩ else ⟨0,positive⟩

/-- The full header checker, with public word bits at its pins. -/
def network (F : Type*) [CommRing F] {H : ℕ} (positive : 0 < H) (s : ℕ)
    (target : Histogram (Fin H) r) : BitNetwork F (r*s) :=
  MotifSelectorChecks.network (valid H) (letter positive) (compactor F r) target

/-- Arbitrary input bits pass exactly when every letter code is valid and
the counted histogram is the prescribed one. -/
theorem eval (positive : 0 < H) (target : Histogram (Fin H) r)
    (v : Fin r → Fin s → Bool) :
    (network F positive s target).eval (blocks r s v) =
      if (∀ i, (MotifBinaryPacking.word s (v i)).val < H) ∧
        target = histogram (fun i => letter positive (v i)) then 1 else 0 := by
  have checked:=MotifSelectorChecks.eval (valid H) (letter positive) (compactor F r) target
    (compactor_run F r) v
  change (MotifSelectorChecks.network (valid H) (letter positive) (compactor F r) target).eval _=_
  by_cases ok : (∀i,valid H (v i)) ∧ target=histogram (fun i=>letter positive (v i))
  · rw [ite_eq_left ok] at checked
    exact checked.trans (ite_eq_left ok).symm
  · rw [ite_eq_right ok] at checked
    exact checked.trans (ite_eq_right ok).symm

/-- On the packet's actual alphabet the trivalent checker selects its one
correct histogram with coefficient one, in every characteristic. -/
theorem eval_word (positive : 0 < H) (capacity : H ≤ 2^s)
    (target : Histogram (Fin H) r) (w : Fin r → Fin H) :
    (network F positive s target).eval (blocks r s
      (fun i => (MotifBinaryPacking.word s).symm ((w i).castLE capacity))) =
        if target = histogram w then 1 else 0 := by
  rw [eval]
  have letter_eq (i : Fin r) :
      letter positive ((MotifBinaryPacking.word s).symm ((w i).castLE capacity)) = w i := by
    simp [letter,valid,(w i).isLt]
  have all : ∀ i, (MotifBinaryPacking.word s ((MotifBinaryPacking.word s).symm ((w i).castLE capacity))).val<H := by
    intro i
    simpa only [Equiv.apply_symm_apply,Fin.val_castLE] using (w i).isLt
  simp only [all,letter_eq]
  by_cases yes : target=histogram w
  · rw [ite_eq_left ⟨fun _=>True.intro,yes⟩,ite_eq_left yes]
  · rw [ite_eq_right (fun h=>yes h.2),ite_eq_right yes]

/-- Cells and hidden wires of the native checker. The constants involving
the alphabet and code width are independent of the number of copies. -/
theorem cost (positive : 0 < H) (s : ℕ) (target : Histogram (Fin H) r) :
    let N := network F positive s target
    N.cells + N.internal ≤
      r*(2^(s+H)*(s+H+1)) + r*H + r*2^(s+H) +
        128000*H*(r+1)*(Nat.log 2 (r+1)+2)^3 := by
  dsimp only [network]
  rw [MotifSelectorChecks.network_cells,MotifSelectorChecks.network_hidden]
  have up := Nat.mul_le_mul_right (32000*(dyadic r+1)^3) (dyadic_le r)
  have cells : (compactor F r).cells ≤ 2*(r+1)*(32000*(dyadic r+1)^3) :=
    (StableCompactNative.network_cells F (dyadic r)).trans up
  have priv : (compactor F r).internal ≤ 2*(r+1)*(32000*(dyadic r+1)^3) :=
    (StableCompactNative.network_internal F (dyadic r)).trans up
  have caps := Nat.add_le_add (Nat.mul_le_mul_left H cells) (Nat.mul_le_mul_left H priv)
  let header := r*(2^(s+H)*(s+H+1)) + r*H + r*2^(s+H)
  calc
    _ = header + (H*(compactor F r).cells + H*(compactor F r).internal) := by dsimp [header]; ring
    _ ≤ header + (H*(2*(r+1)*(32000*(dyadic r+1)^3)) + H*(2*(r+1)*(32000*(dyadic r+1)^3))) :=
      Nat.add_le_add_left caps header
    _ = _ := by dsimp [header,dyadic]; ring

section Packet
open LinearAlgebra.SpectralBooks LinearAlgebra.SpectralBooks.SiteTensor
open LinearAlgebra.SpectralBooks.ChordGraph

variable {K : Type*} [Field K] {k : ℕ} [Nonempty (Fin k)]
  {E A : Type*} [Fintype E] [Fintype A] {edge : E → Chord k} {req : A → E}

/-- Genuine local packets have an inhabited selector alphabet, because their
target equality tensor is nonzero over every field. -/
theorem alphabet_pos (P : Packet K edge req) : 0 < P.terms := by
  by_contra h
  let : IsEmpty (Fin P.terms) := ⟨fun j => h ((Nat.zero_le j.val).trans_lt j.isLt)⟩
  let a := P.width • demandWidths edge req
  have zero : (raw K a).coeff = 0 := by
    funext x
    have seen := congrFun P.identity x
    change (raw K (P.width • demandWidths edge req)).coeff x = (0 : K)
    calc
      _ = (∑j,P.coeff j) x := seen
      _ = ∑j,P.coeff j x := Finset.sum_apply _ _ _
      _ = 0 := by simp
  exact graphClass_ne_zero K a ((ofRaw_raw K a).symm.trans ((ofRaw_eq_zero_iff _).mpr zero))

/-- The private selector fields of an actual saving packet are tested by a
trivalent coefficient, with no multiplicity of successful counter histories. -/
theorem packet_eval (P : Packet K edge req) (target : Histogram (Fin P.terms) r)
    (w : Fin r → Fin P.terms) :
    (network K (alphabet_pos P) P.selectorBits target).eval (blocks r P.selectorBits
      (fun i => (MotifBinaryPacking.word P.selectorBits).symm (P.encode (w i)))) =
        if target = histogram w then 1 else 0 :=
  eval_word (alphabet_pos P) P.encoding target w

/-- Read directly the single word installed on a physical broadcast link. -/
theorem broadcast_eval (P : Packet K edge req) (target : Histogram (Fin P.terms) r)
    (w : Fin r → Fin P.terms) :
    (network K (alphabet_pos P) P.selectorBits target).eval
      ((MotifBinaryPacking.word (r*P.selectorBits)).symm (P.selectorWord r w)) =
        if target = histogram w then 1 else 0 := by
  rw [P.selectorWord_bits]
  exact packet_eval P target w

end Packet


end Hierarchy.Probe.NativeHistogram
end

end OAI
