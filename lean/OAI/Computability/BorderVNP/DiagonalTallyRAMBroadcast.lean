import OAI.Computability.BorderVNP.DiagonalTallyRAMLayout

/-! # Uniqueness of the actual common bit prefix

Each team constrains a different row in a row-major encoding. A fixed field width gives
each bounded subtotal a unique little-endian representation, so the physical broadcast
has multiplicity one for a fully assigned substituted contraction.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyRAM

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM VPVNP.TapeWord

variable {w b R d : ℕ}

/-- Flatten a table of subtotal words to their literal little-endian fields. -/
def broadcast (b : ℕ) (a : Fin R → Fin d → ℕ) : List (List Bool) :=
  List.ofFn fun k : Fin (R*d) => wordBits (word b (a k.divNat k.modNat))

/-- Native input word at a row and coordinate. -/
def fieldWord (w : ℕ) (xs : List (List Bool)) (i : Fin R) (j : Fin d) : Word w :=
  word w (value (xs[(finProdFinEquiv (i,j)).val]?.getD []))

/-- The native reader and the rectangular array use the same flattening order. -/
theorem claimWord_fieldWord (f : Frame) (hd : f.dim = d) (xs : List (List Bool))
    (i : Fin R) (j : Fin d) : claimWord (w := w) f xs i.val j.val = fieldWord w xs i j := by
  simp only [claimWord,fieldWord,hd,finProdFinEquiv_apply_val]

private theorem encoded_field (a : Fin R → Fin d → ℕ) (b : ℕ) (i : Fin R) (j : Fin d) :
    (broadcast b a)[(finProdFinEquiv (i,j)).val]?.getD [] = wordBits (word b (a i j)) := by
  let k := finProdFinEquiv (i,j)
  have hh : k.val < (broadcast b a).length := by simp [broadcast]
  change (broadcast b a)[k.val]?.getD [] = _
  rw [List.getElem?_eq_getElem hh]
  simp only [Option.getD_some,broadcast,List.getElem_ofFn]
  have he : (k.divNat,k.modNat) = (i,j) := finProdFinEquiv.symm_apply_apply _
  exact congrArg (fun p => wordBits (word b (a p.1 p.2))) he

/-- The actual width-limited decode of a generated word gives the specified subtotal. -/
theorem fieldWord_broadcast (a : Fin R → Fin d → ℕ) (hfit : ∀ i j, a i j < 2^b)
    (i : Fin R) (j : Fin d) : fieldWord w (broadcast b a) i j = word w (a i j) := by
  rw [fieldWord,encoded_field,value_wordBits,word_val _ _ (hfit i j)]

private theorem force_field (a : Fin R → Fin d → ℕ) (hb : b ≤ w)
    (hfit : ∀ i j, a i j < 2^b) (xs : List (List Bool)) (hlen : xs.length = R*d)
    (hw : ∀ z ∈ xs, z.length = b)
    (hclaim : ∀ i j, fieldWord w xs i j = word w (a i j)) :
    xs = broadcast b a := by
  apply List.ext_getElem (by simpa [broadcast] using hlen)
  intro k h1 h2
  let l : Fin (R*d) := ⟨k,hlen ▸ h1⟩
  let i := l.divNat
  let j := l.modNat
  have hp : (finProdFinEquiv (i,j)).val = k :=
    congrArg Fin.val (finProdFinEquiv.apply_symm_apply l)
  have hb' : xs[k].length = b := hw _ (List.getElem_mem h1)
  have hcap : 2^b ≤ 2^w := Nat.pow_le_pow_right (by decide) hb
  have hv := value_lt xs[k]
  rw [hb'] at hv
  have hword := hclaim i j
  rw [fieldWord,hp,List.getElem?_eq_getElem h1,Option.getD_some] at hword
  have hval := congrArg Fin.val hword
  rw [word_val _ _ (hv.trans_le hcap),word_val _ _ ((hfit i j).trans_le hcap)] at hval
  have hdest := encoded_field a b i j
  rw [hp,List.getElem?_eq_getElem h2,Option.getD_some] at hdest
  rw [hdest]
  apply eq_of_length_value
  · simpa using hb'
  · rwa [value_wordBits,word_val _ _ (hfit i j)]

/-- Exactly one fixed-width common bit buffer passes all numeric row constraints. -/
theorem unique_broadcast (a : Fin R → Fin d → ℕ) (hb : b ≤ w) (hfit : ∀ i j, a i j < 2^b) :
    ∃! xs : List (List Bool), xs.length = R*d ∧ (∀ z ∈ xs, z.length = b) ∧
      ∀ i j, fieldWord w xs i j = word w (a i j) := by
  refine ⟨broadcast b a, ⟨by simp [broadcast], ?_, fieldWord_broadcast a hfit⟩, ?_⟩
  · intro z hz
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hz
    exact length_wordBits _
  · rintro xs ⟨hl,hw,hc⟩
    exact force_field a hb hfit xs hl hw hc

/-- A common broadcast accepted by every native team table equals the literal encoding
of its actual local count words, regardless of the traces and ending states. -/
theorem broadcast_of_complete_runs (a : Fin R → Fin d → ℕ) (hb : b ≤ w)
    (hfit : ∀ i j, a i j < 2^b) (xs : List (List Bool)) (hlen : xs.length = R*d)
    (hw : ∀ z ∈ xs, z.length = b) (f : Fin R → Frame)
    (pub : Fin R → Arg → Word w) (mac : Fin R → TeamOpcode.Macros w 8)
    (s : Fin R → Bank w) (m : Fin R → Memory w) (rs : Fin R → List (ℕ × ℕ))
    (hf : ∀ i, (f i).dim = d ∧ (f i).team = i.val)
    (input : ∀ i, Input (f i) (pub i) (m i) (rs i) xs)
    (localCounts : ∀ i (j : Fin d),
      DiagonalTallyScatter.after (f i).localBase (rs i) (m i) ((f i).localBase+j.val) = word w (a i j))
    (accepted : ∀ i, ∃ es t mt, Runs (pub i) (mac i) complete (s i) (m i) es t mt) :
    xs = broadcast b a := by
  apply force_field a hb hfit xs hlen hw
  intro i j
  obtain ⟨es,t,mt,r⟩ := accepted i
  have hm := complete_sound (pub i) (mac i) (s i) (m i) (f i) (rs i) xs (input i) r
    j.val ((hf i).1 ▸ j.isLt)
  rw [(hf i).2,claimWord_fieldWord (f i) (hf i).1 xs i j,localCounts] at hm
  exact hm.symm

end DiagonalTallyRAM

end BorderVNP
end Computability
end OAI
