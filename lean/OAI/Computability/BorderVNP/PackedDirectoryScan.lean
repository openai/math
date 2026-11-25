import OAI.Computability.BorderVNP.PackedDirectoryLoop
import OAI.Computability.BorderVNP.PackedDirectoryFit

/-! # Sparse native traversal of all Section 7.3 delivery records -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory.ISA

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

variable {w : ℕ}

/-- Consecutive emitted words for a range of candidate indices. -/
def stream (row : ℕ → Row) (w i n : ℕ) : List (Word w) :=
  (List.range' i n).flatMap fun j => output w (row j)

private theorem placement_putWords {w : ℕ} (m : Memory w) (a base : ℕ) (xs : List (Word w))
    (h : a+xs.length ≤ base) :
    placement (readings (putWords m a xs)) base = placement (readings m) base := by
  funext j
  simp only [placement,readings]
  rw [putWords_outside _ _ _ _ (Or.inr (by omega : a+xs.length ≤ base+j*2)),
    putWords_outside _ _ _ _ (Or.inr (by omega : a+xs.length ≤ base+j*2+1))]

/-- Scanning a suffix from a populated prefix emits its live rows exactly in order. Its
cost is linear in the number of public candidates even when the rows carry many bits. -/
theorem scan_runs (d : Layout) (pb lb : ℕ) (pp lp : ℕ → ℕ × ℕ) (pub : Arg → Word w)
    (macros : TeamOpcode.Macros w 8) (i n : ℕ) (hindex : i+n = d.candidates)
    (positive : 0 < d.processors ∧ 0 < d.fields)
    (fits : ∀ j < d.candidates, if j < 2*d.entries then LayoutFitsPrivate d w pb pp j
      else LayoutFitsLive d w lb lp j)
    (s : Bank w) (m : Memory w) (a : ℕ) (h : Prepared d pb lb (readings s))
    (hi : (s 19).val = i) (ha : (s 20).val = a)
    (hp : placement (readings m) pb = pp) (hl : placement (readings m) lb = lp)
    (bounds : a+7*n < 2^w ∧ a+7*n ≤ pb ∧ a+7*n ≤ lb) :
    let words := stream (d.row pp lp) w i n
    ∃ es t, Runs pub macros (.whileLt 19 18 rowStep) s m es t (putWords m a words) ∧
      traceCost es ≤ (candidate.slots+19)*n+1 ∧ (t 20).val = a+words.length ∧ t 21 = s 21 := by
  induction n generalizing i a s m with
  | zero =>
    have endLoop : ¬ s 19 < s 18 := by
      change ¬ (s 19).val < (s 18).val
      have last : (s 18).val = d.candidates := h.derived.2.2.2.2.2
      omega
    exact ⟨_,s,.whileDone endLoop,le_rfl,by simpa [stream] using ha,rfl⟩
  | succ n ih =>
    let row := d.row pp lp i
    let first := output w row
    have size : first.length ≤ 7 := by rw [show first = output w row by rfl,output_length]; split <;> decide
    have lt : i < d.candidates := by omega
    have hn : d.candidates < 2^w := (h.derived.2.2.2.2.2 ▸ (s 18).isLt)
    have go : s 19 < s 18 := by
      change (s 19).val < (s 18).val
      rw [hi,show (s 18).val = d.candidates from h.derived.2.2.2.2.2]
      exact lt
    have valid := candidate_safe (readings pub) (readings m) (readings s) h positive.1 positive.2
      (by simpa only [readings,hi,hp,hl] using fits i lt)
    obtain ⟨es,t,run,ct,stable,next,ptr,h21⟩ :=
      rowStep_runs pub macros s m a h ha (by omega) (by omega) valid
    simp only [hp,hl,hi] at run next ptr
    let m' := putWords m a first
    have hp' : placement (readings m') pb = pp := (placement_putWords m a pb first (by omega)).trans hp
    have hl' : placement (readings m') lb = lp := (placement_putWords m a lb first (by omega)).trans hl
    obtain ⟨fs,z,loop,ft,addr,end21⟩ := ih (i+1) (by omega) t m' (a+first.length) stable
      next ptr hp' hl' (by omega)
    let words := stream (d.row pp lp) w (i+1) n
    have join : stream (d.row pp lp) w i (n+1) = first ++ words := by
      simp only [stream,List.range'_succ,List.flatMap_cons,first,row,words]
    refine ⟨tick w :: (es++fs),z,?_,?_,?_,end21.trans h21⟩
    · rw [join,putWords_append]
      exact .whileStep go run loop
    · change 1+traceCost (es++fs) ≤ (candidate.slots+19)*(n+1)+1
      rw [show traceCost (es++fs) = traceCost es+traceCost fs from VPVNP.RAMBuckets.cost_append ..,
        Nat.mul_succ]
      omega
    · rw [join,List.length_append]
      simpa [words,Nat.add_assoc] using addr

/-- Expanding the completed compact directory gives exactly the native word stream. -/
theorem stream_directory (d : Layout) (pp lp : ℕ → ℕ × ℕ) (w : ℕ) :
    stream (d.row pp lp) w 0 d.candidates =
      (d.directory pp lp).flatMap fun r => r.words.map (DiagonalResidueRAM.word w) := by
  simp only [stream,← List.range_eq_range',Layout.directory]
  generalize List.range d.candidates = xs
  induction xs with
  | nil => rfl
  | cons j xs ih =>
    by_cases h : (d.row pp lp j).width = 0 <;>
      simpa [List.flatMap_cons,List.map_cons,output,h,Nat.pos_iff_ne_zero] using ih

end Packing.Directory.ISA

end BorderVNP
end Computability
end OAI
