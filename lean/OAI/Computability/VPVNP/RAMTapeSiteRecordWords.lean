import OAI.Computability.VPVNP.RAMTapeSiteEndpoints
import OAI.Computability.VPVNP.RAMSiteInput

/-!
# Preparing the address and header words for the initial memory record

Allocate `w` zero bits, trim as many cells as the source width, and prepend the low-order
source bits. For the site address the trim count comes from its public tally. For the
header a scan counts its four actual cells. Every source and scratch stack is restored.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteRecordWords

open BurstRAM TapeWord Function

/-- Ports for parsed address and header bits, their padded word outputs, public widths, and
conversion scratch. -/
inductive Port where | address | header | siteLog | width | addressWord | headerWord | count | tmp
  deriving DecidableEq

instance : Fintype Port := derive_fintype% _

/-- The same unsigned site address, represented with `w` bits. -/
def addressWord {d w : ℕ} (hd : d ≤ w) (v : Word d) : Word w :=
  ⟨v.val, v.isLt.trans_le (Nat.pow_le_pow_right (by decide) hd)⟩

theorem address_bits {d w : ℕ} (hd : d ≤ w) (v : Word d) :
    wordBits v ++ List.replicate (w-d) false = wordBits (addressWord hd v) := by
  apply eq_of_length_value
  · simp; omega
  · simp [addressWord, value_append, value_wordBits]

theorem header_bits {w : ℕ} (hw : 4 ≤ w) (hdr : ProcessorInput.Header) :
    List.ofFn hdr ++ List.replicate (w-4) false = wordBits (ProcessorInput.headerWord hw hdr) := by
  apply List.ext_getElem
  · simp; omega
  · intro i _ hi
    have hiw : i < w := by simpa using hi
    by_cases h : i < 4
    · rw [List.getElem_append_left (by simpa using h)]
      simp only [BurstRAM.wordBits, List.getElem_ofFn, ProcessorInput.headerWord, Equiv.apply_symm_apply, h, dite_true]
    · rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt h), List.getElem_replicate]
      simpa only [BurstRAM.wordBits, List.getElem_ofFn] using
        (ProcessorInput.headerWord_padding hw hdr ⟨i,hiw⟩ (Nat.le_of_not_gt h)).symm

private inductive Field where | address | header
private def src : Field → Port | .address => .address | .header => .header
private def sizeSource : Field → Port | .address => .siteLog | .header => .header
private def dst : Field → Port | .address => .addressWord | .header => .headerWord

private def extend (f : Field) : FiniteRoutine Port :=
  (((WordCopy.mapWord .tmp (dst f) (fun _ => false) .width).followedBy
    (WordCopy.mapWord .tmp .count (fun _ => true) (sizeSource f))).followedBy
    (SiteEndpointTrim.routine .count (dst f))).followedBy
    (SuccessorFields.prependCopy (src f) (dst f) .tmp)

private theorem extend_runs (f : Field) (s : Stacks Port) (n w : ℕ) (hn : n ≤ w)
    (hwidth : s .width = List.replicate w true) (hsize : (s (sizeSource f)).length = n)
    (hbits : (s (src f)).length = n) (hdst : s (dst f) = []) (hc : s .count = []) (ht : s .tmp = []) :
    (extend f).Runs (5*w + 13*n + 7) s
      (update s (dst f) (s (src f) ++ List.replicate (w-n) false)) := by
  have h₁ : Port.width ≠ dst f := by cases f <;> decide
  have h₂ : Port.tmp ≠ dst f := by cases f <;> decide
  have h₃ : sizeSource f ≠ Port.tmp := by cases f <;> decide
  have h₄ : sizeSource f ≠ Port.count := by cases f <;> decide
  have h₅ : sizeSource f ≠ dst f := by cases f <;> decide
  have h₆ : Port.count ≠ dst f := by cases f <;> decide
  have h₇ : src f ≠ dst f := by cases f <;> decide
  have h₈ : src f ≠ Port.tmp := by cases f <;> decide
  let padded := update s (dst f) (List.replicate w false)
  let counted := update padded .count (List.replicate n true)
  let tail := List.replicate (w - n) false
  let trimmed := update s (dst f) tail
  have hz := WordCopy.mapWord_run Port.tmp (dst f) (fun _ => false) (by decide : Port.width ≠ .tmp)
    h₁ h₂ s ht
  simp only [hwidth, hdst, List.map_const', List.length_replicate, List.reverse_replicate,
    List.append_nil] at hz
  have hm := WordCopy.mapWord_run Port.tmp Port.count (fun _ => true) h₃ h₄ (by decide) padded
    (by simpa [padded, h₂] using ht)
  simp only [padded, update_of_ne h₅, update_of_ne h₆, hc, List.map_const',
    List.reverse_replicate, List.append_nil, hsize] at hm
  have hlen : List.replicate w false = List.replicate n false ++ tail := by
    rw [show tail = List.replicate (w - n) false from rfl, ← List.replicate_add, Nat.add_sub_of_le hn]
  have htrim := SiteEndpointTrim.run h₆ counted n tail (update_self ..)
    (by simpa [counted, padded, Ne.symm h₆] using hlen)
  have hframe : update (update counted .count []) (dst f) tail = trimmed := by
    funext i
    by_cases hd : i = dst f <;> by_cases hcount : i = Port.count <;>
      simp [counted, padded, trimmed, hd, hcount, hc, h₆]
  rw [hframe] at htrim
  have hcopy := SuccessorFields.prependCopy_runs (src f) (dst f) Port.tmp h₇ h₈ (Ne.symm h₂)
    trimmed (by simpa [trimmed, h₂] using ht)
  simp only [trimmed, update_of_ne h₇, update_self, update_idem, hbits] at hcopy
  have h := ((hz.followedBy hm).followedBy htrim).followedBy hcopy
  convert! h using 1
  omega

/-- The same finite table prepares both words for all public widths. -/
def prepare {K : Type} (ports : Port → K) : FiniteRoutine K :=
  ((extend .address).followedBy (extend .header)).onPorts ports

/-- Exact step count for forming the padded address and header words used in the initial
record. -/
def steps (d w : ℕ) : ℕ := 10*w + 13*d + 66

theorem steps_le {d w : ℕ} (hd : d ≤ w) : steps d w ≤ 23*w + 66 := by unfold steps; omega

theorem prepare_runs {K : Type} [DecidableEq K] {d w : ℕ} (ports : Port → K) (hp : Injective ports)
    (s : Stacks K) (v : Word d) (hdr : ProcessorInput.Header) (hd : d ≤ w) (hw : 4 ≤ w)
    (hv : s (ports .address) = wordBits v) (hh : s (ports .header) = List.ofFn hdr)
    (hdmarks : s (ports .siteLog) = List.replicate d true)
    (hwmarks : s (ports .width) = List.replicate w true)
    (ha : s (ports .addressWord) = []) (hb : s (ports .headerWord) = [])
    (hc : s (ports .count) = []) (ht : s (ports .tmp) = []) :
    (prepare ports).Runs (steps d w) s (update (update s (ports .addressWord)
      (wordBits (addressWord hd v))) (ports .headerWord) (wordBits (ProcessorInput.headerWord hw hdr))) := by
  let base := s ∘ ports
  let mid := update base .addressWord (wordBits (addressWord hd v))
  have h₁ := extend_runs .address base d w hd hwmarks
    (by simp [base, sizeSource, hdmarks]) (by simp [base, src, hv]) ha hc ht
  have he₁ : base (src .address) ++ List.replicate (w-d) false = wordBits (addressWord hd v) := by
    simpa [base, src, hv] using address_bits hd v
  rw [he₁] at h₁
  have h₂ := extend_runs .header mid 4 w hw hwmarks (by simp [mid, base, sizeSource, hh])
    (by simp [mid, base, src, hh]) hb hc ht
  have he₂ : mid (src .header) ++ List.replicate (w-4) false = wordBits (ProcessorInput.headerWord hw hdr) := by
    simpa [mid, base, src, hh] using header_bits hw hdr
  rw [he₂] at h₂
  have hcost : (5*w+13*d+7) + (5*w+13*4+7) = steps d w := by unfold steps; omega
  have hrun := h₁.followedBy h₂
  rw [hcost] at hrun
  apply FiniteRoutine.runs_onPorts_framed _ hp hrun
  · intro i; rfl
  · intro i; cases i <;> simp [mid, base, dst, hp.eq_iff]
  · intro i hi
    rw [update_of_ne (Ne.symm (hi .headerWord)), update_of_ne (Ne.symm (hi .addressWord))]

/-- Extend the actual contents of the header source to the indicated word
width. The source may have any length that fits. -/
def extendHeader := extend .header

theorem extendHeader_runs (s : Stacks Port) (w : ℕ) (hs : (s .header).length ≤ w)
    (hwidth : s .width = List.replicate w true) (hd : s .headerWord = [])
    (hc : s .count = []) (ht : s .tmp = []) :
    extendHeader.Runs (5*w + 13*(s .header).length + 7) s
      (update s .headerWord (s .header ++ List.replicate (w - (s .header).length) false)) :=
  extend_runs .header s _ w hs hwidth rfl rfl hd hc ht

end RAMTape.SiteRecordWords

end VPVNP
end Computability
end OAI
