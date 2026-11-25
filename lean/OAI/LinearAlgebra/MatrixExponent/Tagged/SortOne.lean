import OAI.LinearAlgebra.MatrixExponent.Tagged.Array
import OAI.LinearAlgebra.MatrixExponent.Diagram.Permute

section
/-! # Checking wider payloads against the same tags -/

namespace OAI.LinearAlgebra.MatrixExponent.Tagged

variable {F : Type} [Field F] {a b : Wire} {w t m : ℕ}

private theorem project_net {f : Val a → Val b} (h : DNet F a b f m) (w : ℕ) :
    DNet F (inputs w a) (inputs w b) (project w f) (2 ^ w * (w + 2 * m)) := by
  have htag := (DNet.id F (word w)).par h
  refine ((mapRows_net h w).par (mapRows_net htag w)).mono ?_
  rw [wd_word]
  exact le_of_eq (by ring)

private theorem pad_net (F : Type) [Field F] (ha : wd b ≤ wd a) :
    ∃ f, DNet F b a f (wd a) ∧ Function.Injective f := by
  let p := word (wd a - wd b)
  have hw : wd (.pair b p) = wd a := by simp [p, wd, ha]
  obtain ⟨f, hf, hi⟩ := Rewire.exists_of_width hw
  let z := (bits p).symm (fun _ => false)
  have h := ((DNet.id F b).par (literal_net F p z)).pre (.unit' _)
  refine ⟨fun x => f (x, z), (h.post hf).mono hw.le, ?_⟩
  exact fun _ _ he => congrArg Prod.fst (hi he)

theorem tag_shrink (h : Batch (tag F w a) t m) (ha : wd b ≤ wd a) :
    Batch (tag F w b) t (m + t * 2 ^ w * (w + 2 * wd a)) := by
  obtain ⟨f, hf, hi⟩ := pad_net F ha
  have k := h.pullback (project_net hf w)
  simp only [tag_project F w f hi] at k
  exact k.mono (le_of_eq (by ring))

private theorem tag_double (h : Batch (tag F w a) t m) :
    Batch (tag F w (.pair a a)) t (2 * m + t * 2 ^ w * (3 * w + 12 * wd a)) := by
  have k := (h.par_pred h).pullback
    ((project_net (DNet.fst F a a) w).pair (project_net (DNet.snd F a a) w))
  simp only [← tag_pair] at k
  refine k.mono ?_
  simp only [wd, wd_tree, row, wd_word]
  exact le_of_eq (by ring)

/-- The overhead for `2^k` slices is linear in the total number of rows,
including all copies. The same tag appears on each slice. -/
theorem tag_slices (h : Batch (tag F w a) t m) (k : ℕ) (ha : wd b ≤ 2 ^ k * wd a) :
    Batch (tag F w b) t (2 ^ k * m + (6 * k + 2) * 2 ^ k * t * 2 ^ w * (w + wd a)) := by
  have aux (j : ℕ) : Batch (tag F w (tree j a)) t (2 ^ j * m + 6 * j * 2 ^ j * t * 2 ^ w * (w + wd a)) := by
    induction j with
    | zero => simpa using h
    | succ j ih =>
      apply (tag_double ih).mono
      rw [wd_tree, pow_succ]
      have hw := Nat.mul_le_mul_right (t * 2 ^ w * w) (Nat.one_le_pow j 2 (by decide))
      ring_nf at hw ⊢
      omega
  refine (tag_shrink (aux k) (by simpa [wd_tree] using ha)).mono ?_
  rw [wd_tree]
  have hw := Nat.mul_le_mul_right (t * 2 ^ w * w) (Nat.one_le_pow k 2 (by decide))
  ring_nf at hw ⊢
  omega

end OAI.LinearAlgebra.MatrixExponent.Tagged
end

section
/-! # Sorting ordinary records with a tagged permutation verifier -/

namespace OAI.LinearAlgebra.MatrixExponent.Tagged

variable {F : Type} [Field F] {a : Wire} {w m k : ℕ}

/-- A verifier for logarithmic-width payloads can sort records up to four
times as wide. The comparison cost is charged separately. -/
theorem sort_one [LinearOrder (Val a)]
    (h : Net F (inputs w (word w)) .unit (tag F w (word w)) m) (hw : wd a ≤ 4 * w)
    (comp : DNet F (.pair a a) .bit (fun x => decide (x.1 < x.2)) k) :
    DNet F (tree w a) (tree w a) (sortTree w) (4 * m + 10000 * 2 ^ w * (w + k + 1)) := by
  have ha := tag_slices (b := a) (Batch.of_net h 1) 2 (by simpa using hw)
  have hs := sort_of_tag ha comp
  apply ((hs.pre (.unit' _)).post (.unit _)).mono
  rw [wd_word]
  have he := Nat.mul_le_mul_left (2 ^ w) hw
  ring_nf at he ⊢
  omega

end OAI.LinearAlgebra.MatrixExponent.Tagged
end
