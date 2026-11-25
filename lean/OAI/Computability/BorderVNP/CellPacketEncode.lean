import OAI.Computability.BorderVNP.CellPacketEncodeRecord

/-! # End-to-end native serialization of the sparse generator input

The complete counted word loop accepts any contiguous source interval. It preserves
all surrounding memory and protected registers and returns the exact encoded bit
length in its destination cursor. Its cost is linear in the source word count
times the physical word width.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellPacketEncode

open VPVNP.BurstRAM RationalHitting.StackLanguage Packing.Directory.ISA

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

/-- Physical source words, in the order in which the sparse generator parses them. -/
def Source (m : Memory w) (src : ℕ) (xs : List ℕ) : Prop :=
  ∀ i (hi : i < xs.length), readings m (src+i) = xs[i]

private theorem encoder_exact (e : Bool) (xs : List ℕ) (s : Bank w) (m : Memory w)
    (c : Constants (readings s)) (endReg : readings s 15 = readings s 14 + xs.length)
    (input : Source m (readings s 14) xs)
    (separate : CompactWrite.Disjoint (readings s 14) xs.length (readings s 20) (tags e (packet xs)).length)
    (fit : readings s 20 + (tags e (packet xs)).length < 2^w) :
    BoundedRun pub macros (encoder e) s m ((11*w+12)*xs.length+1)
      (Effect (.ofWords s m) xs.length (tags e (packet xs))) := by
  induction xs generalizing s m with
  | nil =>
    have guard : ¬ s 14 < s 15 := show ¬ readings s 14 < readings s 15 by simp [endReg]
    rw [show packet [] = [] by rfl, tags_nil]
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add]
    apply loop_done guard
    exact ⟨fun _ _ _ _ _ => rfl, (Nat.add_zero _).symm,
      (Nat.add_zero _).symm,rfl⟩
  | cons a xs ih =>
    let src := readings s 14
    let dst := readings s 20
    let part := recordBits e a
    let suffix := tags e (packet xs)
    have total := packet_chunk e a xs
    rw [total,List.length_append] at fit separate
    change dst+(part.length+suffix.length) < 2^w at fit
    have read : readings m src = a := by
      have h := input 0 (by simp)
      change readings m (src+0) = a at h
      simpa only [Nat.add_zero] using h
    have fitSrc : src+xs.length+1 < 2^w := by
      have h := (endReg.symm.trans_lt (s 15).isLt)
      simpa [src,List.length_cons,Nat.add_assoc] using h
    have hguard : s 14 < s 15 := show readings s 14 < readings s 15 by rw [endReg]; simp
    have word := record_run (pub := pub) (macros := macros) e s m a read c
      (by change src+1 < 2^w; omega) (by change dst+part.length < 2^w; omega)
    have ha : a.bits.length ≤ w := by
      rw [Nat.size_eq_bits_len]
      exact Nat.size_le.mpr (read ▸ (m src).isLt)
    apply (loop_step (f := (11*w+12)*xs.length+1) hguard word
      (Q := Effect (.ofWords s m) (1+xs.length) (part++suffix)) ?_).mono
    · rw [List.length_cons,Nat.mul_add,Nat.mul_one]; omega
    · intro z h
      simpa only [total,List.length_cons,Nat.add_comm 1,part,suffix] using h
    · intro t mt h
      have src' : readings t 14 = src+1 := h.source
      have dst' : readings t 20 = dst+part.length := h.destination
      have mem : readings mt = putDigits (readings m) dst part := h.memory
      have sep : src+(xs.length+1) ≤ dst ∨ dst+(part.length+suffix.length) ≤ src := separate
      have sep' : CompactWrite.Disjoint (readings t 14) xs.length (readings t 20) suffix.length := by
        unfold CompactWrite.Disjoint
        omega
      have input' : Source mt (readings t 14) xs := by
        intro i hi
        have bound : readings t 14+i < dst ∨ dst+part.length ≤ readings t 14+i := by omega
        have a' := input (i+1) (by simpa using hi)
        rw [mem,putDigits_outside _ _ _ _ bound,src']
        simpa [src,Nat.add_assoc,Nat.add_comm 1] using a'
      have end' : readings t 15 = readings t 14+xs.length := by
        have h15 := h.fixed 15 (by decide) (by decide) (by decide) (by decide)
        change readings t 15 = readings s 15 at h15
        rw [h15,endReg,src']
        simp [src,Nat.add_assoc,Nat.add_comm 1]
      apply (ih t mt (h.fixed.constants c) end' input' sep' (by change readings t 20+suffix.length < 2^w; omega)).mono le_rfl
      intro z g
      exact h.append g

/-- The physical RAM encodes every scalar once with one bit iteration per canonical
binary digit. The enclosing form can be concatenated across chunks before emitting
the enclosing terminator and external-wire suffix. -/
theorem encoder_run (e : Bool) (xs : List ℕ) (src dst : ℕ) (s : Bank w) (m : Memory w)
    (c : Constants (readings s)) (source : readings s 14 = src)
    (endReg : readings s 15 = src+xs.length) (destination : readings s 20 = dst)
    (input : Source m src xs)
    (separate : CompactWrite.Disjoint src xs.length dst (tags e (packet xs)).length)
    (fit : dst + (tags e (packet xs)).length < 2^w) :
    BoundedRun pub macros (encoder e) s m (40*(xs.length+1)*(w+1))
      (Effect (.ofWords s m) xs.length (tags e (packet xs))) := by
  subst src dst
  exact (encoder_exact e xs s m c endReg input separate fit).mono (by nlinarith) fun _ h => h

/-- The natural memory effect is the physical writer's consecutive word image,
using one machine word of value zero or one per scratch digit. -/
theorem putDigits_eq_putWords (m : Memory w) (dst : ℕ) (bs : List Bool) (hw : 0 < w) :
    putDigits (readings m) dst bs =
      readings (putWords m dst (bs.map fun b => DiagonalResidueRAM.word w b.toNat)) := by
  induction bs generalizing m dst with
  | nil => rfl
  | cons b bs ih =>
    simp only [putDigits,List.map_cons,putWords]
    have hb : b.toNat < 2^w := by
      have h := Nat.one_lt_two_pow hw.ne'
      cases b <;> simp_all
    have update : Function.update (readings m) dst b.toNat =
        readings (Function.update m dst (DiagonalResidueRAM.word w b.toNat)) := by
      funext i
      by_cases h : i = dst
      · subst i; simp [readings, DiagonalResidueRAM.word_val w _ hb]
      · simp [readings,h]
    rw [update,ih]

end RoutingISA.CellPacketEncode

end BorderVNP
end Computability
end OAI
