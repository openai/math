import OAI.Computability.BorderVNP.PackedDirectoryNative
import OAI.Computability.BorderVNP.TransmissionDataKeys

/-! # Native directory safety on its real private and live entries

A terminal candidate may fetch two words beyond a team's site interval. Its start is then
at the candidate block boundary, its destination displacement is zero, and its width is
zero. The machine consequently handles arbitrary words at unused addresses. Only the
actual private and live placement offsets require a polynomial size bound.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory.ISA

open RoutingISA VPVNP.BurstRAM
open scoped Classical

/-- A common bound formed from public scalar dimensions, the true placement bases, and the
maximum occupied receiving offset. -/
def placementBound (d : Layout) (pb lb extent : ℕ) :=
  d.candidates+d.literal+d.description+d.block+d.sites+d.stride+
    (d.literal+(d.teams-1)*d.link)+pb+lb+extent

private def limited (p : ℕ → ℕ × ℕ) (count i : ℕ) := if i < count then p i else (0,0)

private theorem limitedSizes (d : Layout) (pb lb extent : ℕ) (pp lp : ℕ → ℕ × ℕ)
    (privateRoom : ∀ j < d.entries, (pp j).2 ≤ extent)
    (liveRoom : ∀ a < d.teams*d.sites, (lp a).2 ≤ extent) :
    Sizes d pb lb (limited pp d.entries) (limited lp (d.teams*d.sites)) (placementBound d pb lb extent) := by
  unfold placementBound
  constructor
  case offsets =>
    constructor
    · intro j _
      by_cases h : j<d.entries
      · simp only [limited,h,ite_true]
        have := privateRoom j h
        omega
      · simp [limited,h]
    · intro a _
      by_cases h : a<d.teams*d.sites
      · simp only [limited,h,ite_true]
        have := liveRoom a h
        omega
      · simp [limited,h]
  all_goals omega

private theorem fieldStart_le (d : Layout) (bounds : d.DestinationBounds) (p f : ℕ)
    (hp : p < d.processors) (hf : f < d.fields) :
    p*d.stride + f*(d.literal+(d.teams-1)*d.link) ≤ d.sites*d.block := by
  have last : f*(d.literal+(d.teams-1)*d.link) ≤ d.stride := by
    have cases : f=0 ∨ (f=1 ∧ d.fields=2) := by have := bounds.fields; omega
    rcases cases with h|⟨h,hf⟩
    · simp [h]
    · simp [h,hf,Layout.stride,Nat.two_mul]
  have limit := Nat.mul_le_mul_right d.stride hp
  rw [Nat.succ_mul] at limit
  exact ((Nat.add_le_add_left last _).trans limit).trans bounds.room

private theorem fieldTeam_lt (d : Layout) {i : ℕ} (hi : i < d.candidates) (live : 2*d.entries ≤ i)
    (hp : 0 < d.processors) (hf : 0 < d.fields) :
    ((i-2*d.entries)/(d.literal/d.block+2)/d.fields)/d.processors < d.teams := by
  have step : 0 < d.literal/d.block+2 := Nat.zero_lt_succ _
  apply (Nat.div_lt_iff_lt_mul hp).mpr
  apply (Nat.div_lt_iff_lt_mul hf).mpr
  apply (Nat.div_lt_iff_lt_mul step).mpr
  change i < 2*d.entries + d.teams*d.processors*d.fields*(d.literal/d.block+2) at hi
  omega

/-- The complete candidate loop is safe in actual word memory. The hypotheses on fetched
offsets apply to just the occupied placement table entries, even for the final empty slices. -/
theorem occupied_candidates_fit {d : Layout} {w pb lb extent : ℕ} (pp lp : ℕ → ℕ × ℕ)
    (bounds : d.DestinationBounds) (fields : 0 < d.fields)
    (privateRoom : ∀ j < d.entries, (pp j).2 ≤ extent)
    (liveRoom : ∀ a < d.teams*d.sites, (lp a).2 ≤ extent)
    (word : ∀ a, (lp a).2 < 2^w) (room : wordBound (placementBound d pb lb extent) < 2^w)
    (i : ℕ) (hi : i < d.candidates) :
    if i < 2*d.entries then LayoutFitsPrivate d w pb pp i else LayoutFitsLive d w lb lp i := by
  have clipped := candidates_fit (limitedSizes d pb lb extent pp lp privateRoom liveRoom)
    bounds.tail bounds.block room i hi
  by_cases priv : i < 2*d.entries
  · have hj : i/2 < d.entries := (Nat.div_lt_iff_lt_mul (by decide : 0<2)).mpr (by omega)
    simpa only [priv,ite_true,LayoutFitsPrivate,limited,hj] using clipped
  · simp only [priv,ite_false,LayoutFitsLive] at clipped ⊢
    let j := i-2*d.entries
    let pieces := d.literal/d.block+2
    let u := j/pieces
    let a := u/d.fields
    let team := a/d.processors
    let start := (a%d.processors)*d.stride+(u%d.fields)*(d.literal+(d.teams-1)*d.link)
    let site := start/d.block+j%pieces
    let entry := team*d.sites+site
    change EndpointsFit w start d.literal d.block (j%pieces) ∧ lb+entry*2+1 < 2^w ∧
      (limited lp (d.teams*d.sites) entry).2+(max start (site*d.block)-site*d.block) < 2^w at clipped
    refine ⟨clipped.1,clipped.2.1,?_⟩
    change (lp entry).2+(max start (site*d.block)-site*d.block) < 2^w
    by_cases inside : entry < d.teams*d.sites
    · simpa only [limited,inside,ite_true] using clipped.2.2
    · have ht : team < d.teams := fieldTeam_lt d hi (by omega) bounds.processors fields
      have hs : d.sites ≤ site := by
        have h := Nat.mul_le_mul_right d.sites ht
        rw [Nat.succ_mul] at h
        dsimp only [entry] at inside
        omega
      have startRoom : start ≤ site*d.block :=
        (fieldStart_le d bounds _ _ (Nat.mod_lt _ bounds.processors) (Nat.mod_lt _ fields)).trans
          (Nat.mul_le_mul_right _ hs)
      simpa only [max_eq_right startRoom,Nat.sub_self,Nat.add_zero] using word entry

/-- Four operand-width multiples and ten extra bits suffice for the quartic intermediate
bound, including the entire private and live address space. -/
theorem placement_word_room {B b W : ℕ} (bound : B < 2^b) (wide : 4*b+6 ≤ W) :
    wordBound B < 2^W := by
  have h := Nat.pow_le_pow_left (show B+1 ≤ 2^b by omega) 4
  have eq : (2^b)^4 = 2^(4*b) := by rw [←pow_mul,Nat.mul_comm]
  have half : 32*(2^(4*b)) < 2^(4*b+6) := by rw [pow_add]; have := Nat.two_pow_pos (4*b); norm_num; omega
  exact ((Nat.mul_le_mul_left 32 (h.trans_eq eq)).trans_lt half).trans_le (Nat.pow_le_pow_right (by decide) wide)

end Packing.Directory.ISA

end BorderVNP
end Computability
end OAI
