import OAI.Computability.VPVNP.PrimedInputRAMHeaders
import OAI.Computability.VPVNP.PrimedBudget
import OAI.Computability.VPVNP.PairedChain

/-!
# Allocating the pair counter's headers and two rectangles

The bit-valued index, advice and cut arrays and the nominated histogram
occupy a polynomial number of header addresses independent of `B`. Choosing
`B` last puts all these addresses below the actual virtual site count `R′`.
The two rectangles then start at `R′` and their addresses fit the paper's
prescribed word width.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM

open BurstRAM CursorBounds Compression Filter

private theorem degreeFits (B n : ℕ) : n^B ≤ processorCount B n := by
  calc
    n^B ≤ (2^(Nat.clog 2 n))^B := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) _
    _ = processorCount B n := by
      rw [← pow_mul, Nat.mul_comm]
      rfl

/-- Both row-major rectangles fit above the full virtual header interval. -/
theorem rectangleAddressSpace (B n : ℕ) (hB : 1 ≤ B) :
    2^(virtualBits B n) + positions n (addressWidth B n) + positions n (addressWidth B n) ≤
      2^(CursorBounds.wordBits B n) := by
  let r := addressWidth B n
  let c := Nat.clog 2 n
  have hc : c ≤ r := Nat.le_mul_of_pos_left _ hB
  have hv := virtualBits_le B n
  have hD : virtualBits B n ≤ 3*r := by
    change virtualBits B n ≤ (B+2)*c at hv
    rw [Nat.add_mul] at hv
    change c ≤ B*c at hc
    change virtualBits B n ≤ 3*(B*c)
    omega
  have hn : n ≤ 2^r := (Nat.le_pow_clog (by decide) n).trans (Nat.pow_le_pow_right (by decide) hc)
  have hr : 2^r * n ≤ 2^(3*r) := by
    calc
      _ ≤ 2^r * 2^r := Nat.mul_le_mul_left _ hn
      _ = 2^(r+r) := (Nat.pow_add ..).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have hvirt := Nat.pow_le_pow_right (by decide : 0 < 2) hD
  have hs : positions n r ≤ 2 * 2^(3*r) := by
    unfold positions
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ hr
  have hw : 3*r+3 ≤ (r+10)^4 := by
    calc
      _ ≤ (r+10)^2 := by nlinarith [Nat.zero_le (r*r)]
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 4)
  have hlarge := Nat.pow_le_pow_right (by decide : 0 < 2) hw
  rw [Nat.pow_add] at hlarge
  change 2^(virtualBits B n) + positions n r + positions n r ≤ 2^((r+10)^4)
  norm_num1 at hlarge
  omega

/-- A fixed degree bound for the header data is absorbed by the choice of
address multiplier `B`; the same capacity covers the middle cut. -/
theorem headerCapacity {B C n : ℕ} (hn : 3 ≤ n) (hB : C+2 ≤ B) (L : Lengths) (hist : ℕ)
    (hi : L.index ≤ n^C) (ha : L.advice ≤ n^C) (hc : L.cutCapacity ≤ n^C)
    (hm : L.middleCut ≤ n^C) (ht : hist ≤ n^C) :
    Header.count L + hist ≤ 2^(virtualBits B n) ∧ L.middleCut ≤ 2^(addressWidth B n) := by
  have hp : 1 ≤ n^C := Nat.pow_pos (by omega)
  have hscale : 9 ≤ n^2 := by nlinarith
  have hdata : Header.count L + hist ≤ n^(C+2) := by
    rw [Nat.pow_add]
    apply le_trans _ (Nat.mul_le_mul_left (n^C) hscale)
    unfold Header.count
    omega
  have hbig : n^(C+2) ≤ processorCount B n :=
    (Nat.pow_le_pow_right (by omega) hB).trans (degreeFits ..)
  have hmid := (Nat.pow_le_pow_right (by omega : 0<n) (show C ≤ C+2 by omega)).trans hbig
  exact ⟨(hdata.trans hbig).trans (Nat.pow_le_pow_right (by decide) (addressBits_le_virtualBits B n hn)),
    hm.trans hmid⟩

/-- The literal prefix and the paper's processor parameters give an actual
two-pass layout, including the room for every histogram header and exactly
the virtual site's header interval as the scratch base. -/
theorem eventually_layout (p : UniversalMachine.Program) {B C : ℕ} (hB : C+2 ≤ B)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1) (lengths : ℕ → Lengths) (hist : ℕ → ℕ)
    (hs : ∀ᶠ n : ℕ in atTop, (lengths n).index ≤ n^C ∧ (lengths n).advice ≤ n^C ∧
      (lengths n).cutCapacity ≤ n^C ∧ (lengths n).middleCut ≤ n^C ∧ hist n ≤ n^C) :
    ∀ᶠ n : ℕ in atTop, ∃ Q : Layout (lengths n) n (addressWidth B n) (liveBucket δ n)
      (CursorBounds.wordBits B n), Q.program = p ∧ Q.scratchBase = 2^(virtualBits B n) ∧
        Header.count (lengths n) + hist n ≤ Q.scratchBase := by
  filter_upwards [hs, eventually_liveInputFits p B hδ hδ', eventually_ge_atTop 3] with n h hf hn
  obtain ⟨hi,ha,hc,hm,ht⟩ := h
  obtain ⟨hcap,hmid⟩ := headerCapacity hn hB (lengths n) (hist n) hi ha hc hm ht
  exact ⟨⟨p, hf, hmid, 2^(virtualBits B n), by omega, rectangleAddressSpace B n (by omega)⟩,
    rfl, rfl, hcap⟩

/-- The choice of `B` and the threshold length work simultaneously for
every primed pair, including the endpoint pairs whose exterior cuts are
empty. The cut capacity uses the paper's `n^a * n^d₂` upper bound. -/
theorem eventually_pairedLayouts (p : UniversalMachine.Program) (a d₁ d₂ C B : ℕ)
    (hB : max (max (a+1) (a+d₂)) (max d₁ C) + 2 ≤ B) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ i : Fin (2^(n^a-1)), ∀ t ≤ n^C,
      let L := PairedChain.lengths (n^a-1) (n^d₂) (n^d₁) i
      ∃ Q : Layout L n (addressWidth B n) (liveBucket δ n) (CursorBounds.wordBits B n),
        Q.program = p ∧ Q.scratchBase = 2^(virtualBits B n) ∧ Header.count L+t ≤ Q.scratchBase := by
  let deg := max (max (a+1) (a+d₂)) (max d₁ C)
  filter_upwards [eventually_liveInputFits p B hδ hδ', eventually_ge_atTop 3] with n hf hn
  intro i t ht
  let L := PairedChain.lengths (n^a-1) (n^d₂) (n^d₁) i
  have hpow : 1 ≤ n^a := Nat.pow_pos (by omega)
  have hc : L.cutCapacity = n^(a+d₂) := by
    change (n^a-1+1)*n^d₂ = _
    rw [Nat.sub_add_cancel hpow, Nat.pow_add]
  have hi : L.index ≤ n^(a+1) := by
    change n^a-1+2 ≤ n^(a+1)
    rw [Nat.pow_succ]
    have := Nat.mul_le_mul_left (n^a) (show 2 ≤ n by omega)
    omega
  have hm : L.middleCut ≤ L.cutCapacity := by
    change CutSchedule.width _ _ _ ≤ _
    unfold CutSchedule.width
    split
    · exact Nat.mul_le_mul_right _ (Nat.sub_le ..)
    · exact Nat.zero_le _
  have mono {x : ℕ} (hx : x ≤ deg) : n^x ≤ n^deg := Nat.pow_le_pow_right (by omega) hx
  have hcap : L.cutCapacity ≤ n^deg := hc.le.trans (mono (by dsimp [deg]; omega))
  obtain ⟨hfits,hmid⟩ := headerCapacity hn hB L t (hi.trans (mono (by dsimp [deg]; omega)))
    (mono (x := d₁) (by dsimp [deg]; omega)) hcap (hm.trans hcap) (ht.trans (mono (by dsimp [deg]; omega)))
  exact ⟨⟨p,hf,hmid,2^(virtualBits B n),(Nat.le_add_right (Header.count L) t).trans hfits,rectangleAddressSpace B n (by omega)⟩,
    rfl,rfl,hfits⟩

/-- The header provider agrees with the zero-elsewhere initial memory of
Lemma 10.1 when all nominated histogram words fit in the header interval. -/
theorem initialMemory_headerMemory {w : ℕ} (L : Lengths) (hdr : Header L → Bool)
    (hist : List (Word w)) {S : ℕ} (hS : Header.count L + hist.length ≤ S) :
    RAMMemory.initialMemory S (headerMemory L hdr hist) = headerMemory L hdr hist := by
  funext a
  by_cases ha : a < S
  · simp [RAMMemory.initialMemory, ha]
  · simp only [RAMMemory.initialMemory, ha, ite_false]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show Header.count L ≤ a by omega)
    rw [headerMemory_hist]
    have hj : hist.length ≤ j := by omega
    simp [List.getElem?_eq_none hj]

end PrimedInputRAM

end VPVNP
end Computability
end OAI
