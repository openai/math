import OAI.Computability.VPVNP.PrimedInputRAM

/-!
# Prescribed headers for the auxiliary RAM

The pair's cut lengths occupy words 0, 1 and 2. After them come the two
fixed-width group index fields, the advice field, and two equal-capacity
exterior fields. Each bit occupies one word. The nominated histogram
follows these fields, and all unused header positions are zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM

open BurstRAM

variable {w : ℕ}

/-- Represent a Boolean header or shared bit by a zero or one RAM word. -/
def encodeBit (w : ℕ) (b : Bool) : Word w := if b then 1 else 0

@[simp] theorem encodeBit_eq_one (hw : 0 < w) (b : Bool) :
    encodeBit w b = 1 ↔ b = true := by
  cases b
  · have h : 1 < 2^w := Nat.one_lt_two_pow hw.ne'
    simp [encodeBit, Fin.ext_iff, Nat.mod_eq_of_lt h]
  · simp [encodeBit]

/-- The left, middle or right cut length stored in the corresponding one of the first three
header words. -/
def cutLength (L : Lengths) (i : Fin 3) : ℕ :=
  if i = 0 then L.leftCut else if i = 1 then L.middleCut else L.rightCut

/-- Lay out the three cut lengths, group indices, advice, exterior bits and nominated histogram
in external memory, padding the unused cells with zero. -/
def headerMemory (L : Lengths) (hdr : Header L → Bool) (hist : List (Word w)) (a : ℕ) : Word w :=
  if h : a < 3 then Fin.ofNat _ (cutLength L ⟨a,h⟩) else
  if h : a < 3 + L.index then encodeBit w (hdr (.group 0 ⟨a-3, by omega⟩)) else
  if h : a < 3 + 2*L.index then encodeBit w (hdr (.group 1 ⟨a-3-L.index, by omega⟩)) else
  if h : a < 3 + 2*L.index + L.advice then
    encodeBit w (hdr (.advice ⟨a-(3+2*L.index), by omega⟩)) else
  let base := 3 + 2*L.index + L.advice
  if h : a < base + L.leftCut then encodeBit w (hdr (.leftCut ⟨a-base, by omega⟩)) else
  if hcut : a < base + L.cutCapacity then 0 else
  if h : a < base + L.cutCapacity + L.rightCut then
    encodeBit w (hdr (.rightCut ⟨a-(base+L.cutCapacity), by omega⟩)) else
  if a < Header.count L then 0 else hist[a-Header.count L]?.getD 0

@[simp] theorem headerMemory_length (L : Lengths) (hdr : Header L → Bool) (hist : List (Word w))
    (j : Fin 3) :
    headerMemory L hdr hist j.val = Fin.ofNat _ (cutLength L j) := by
  simp [headerMemory, j.isLt]

@[simp] theorem headerMemory_bits (L : Lengths) (hdr : Header L → Bool) (hist : List (Word w))
    (j : Header L) : headerMemory L hdr hist j.address.val = encodeBit w (hdr j) := by
  cases j with
  | group g i =>
    have hg : g.val = 0 ∨ g.val = 1 := by have := g.isLt; omega
    rcases hg with hg | hg
    · obtain rfl : g = 0 := Fin.ext hg
      simp [Header.address, headerMemory, i.isLt]
    · obtain rfl : g = 1 := Fin.ext hg
      have hi := i.isLt
      simp only [Header.address, Fin.val_one, headerMemory]
      simp only [Nat.one_mul]
      split_ifs <;> first | rfl | omega | (congr 4; omega)
  | advice i =>
    have hi := i.isLt
    simp only [Header.address, headerMemory]
    simp only [Nat.add_sub_cancel_left]
    split_ifs <;> first | rfl | omega
  | leftCut i =>
    have hi := i.isLt
    simp only [Header.address, headerMemory]
    simp only [Nat.add_sub_cancel_left]
    split_ifs <;> first | rfl | omega
  | rightCut i =>
    have hi := i.isLt
    have hc := L.leftFit
    simp only [Header.address, headerMemory]
    simp only [Nat.add_sub_cancel_left]
    split_ifs <;> first | rfl | omega

/-- Read the supplied word for one histogram entry, or zero if it lies beyond the end. -/
theorem headerMemory_hist (L : Lengths) (hdr : Header L → Bool) (hist : List (Word w)) (j : ℕ) :
    headerMemory L hdr hist (Header.count L+j) = hist[j]?.getD 0 := by
  have := L.leftFit
  have := L.rightFit
  unfold headerMemory Header.count
  dsimp only
  split_ifs <;> first | omega | simp

variable {L : Lengths} {n r H : ℕ}

namespace Layout

/-- The stream obtained from the inverse path-counting equivalence consists
of exactly the bits consumed by the first pass, in physical order. -/
theorem streamEquiv_symm (Q : Layout L n r H w) (bitWord : Bool → Word w) (initial : Memory w)
    (bits : Internal L r H w → Bool) :
    ((Q.streamEquiv bitWord initial).symm bits).val = branches (Q.assignment bits) := rfl

/-- A parser can read each output bit directly from RAM following any admissible
first-pass branch sequence. The three cut lengths and the actual bit-valued
words in the initialization are fixed by the header format above. -/
theorem assemble_stream (Q : Layout L n r H w) (hdr : Header L → Bool) (hist : List (Word w))
    (bs : {bs : List Bool //
      (firstPass Q.owns Q.bitAddress (encodeBit w) bs (headerMemory L hdr hist)).isSome = true}) :
    let init := headerMemory L hdr hist
    let bits := Q.streamEquiv (encodeBit w) init bs
    ∃ final, Q.assemble (encodeBit w) bs.val init = some final ∧
      ∀ u : Site r, ∀ j : Fin n,
        final (Q.outputAddress (finProdFinEquiv (finProdFinEquiv u,j))).val =
          encodeBit w (input Q.program Q.fits hdr bits u j) := by
  let init := headerMemory L hdr hist
  let bits := Q.streamEquiv (encodeBit w) init bs
  have hb : branches (Q.assignment bits) = bs.val :=
    congrArg Subtype.val ((Q.streamEquiv (encodeBit w) init).symm_apply_apply bs)
  refine ⟨Q.assembled (encodeBit w) bits init, ?_, ?_⟩
  · rw [← hb]
    exact Q.assemble_branches ..
  · exact Q.assembled_input _ _ _ _ (fun j ↦ headerMemory_bits L hdr hist j)

end Layout
end PrimedInputRAM

end VPVNP
end Computability
end OAI
