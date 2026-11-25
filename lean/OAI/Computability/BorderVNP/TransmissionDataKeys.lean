import OAI.Computability.BorderVNP.PackedDirectoryBudget

/-! # Recovering populated data candidates from destination keys and lanes -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory

open private inside quotient from OAI.Computability.BorderVNP.PackedDirectoryInverse
open private liveReencode from OAI.Computability.BorderVNP.PackedDirectoryBudget

/-- A destination word names a private description, or a site in a team's live copy. -/
abbrev Layout.DestinationKey (d : Layout) := Fin d.entries ⊕ (Fin d.teams × Fin d.sites)

/-- Number of genuine lanes in the destination word. -/
def Layout.keyWidth (d : Layout) : d.DestinationKey → ℕ
  | .inl _ => d.description
  | .inr _ => d.block

/-- The two physical placement directories interpreted at the typed destination word. -/
def Layout.keyPlacement (d : Layout) (pp lp : ℕ → ℕ × ℕ) : d.DestinationKey → ℕ × ℕ
  | .inl j => pp j.val
  | .inr (t,s) => lp (t.val*d.sites+s.val)

/-- A placement-independent word together with a lane strictly within that word. -/
abbrev Layout.DestinationSlot (d : Layout) := (key : d.DestinationKey) × Fin (d.keyWidth key)

/-- A bit in the raw public candidate enumeration. Empty slices contribute no bits. -/
abbrev Layout.CandidateBit (d : Layout) (pp lp : ℕ → ℕ × ℕ) :=
  (i : Fin d.candidates) × Fin (d.row pp lp i).width

/-- Bounds for recovering a source processor and field from its destination site and lane. -/
structure Layout.DestinationBounds (d : Layout) : Prop where
  /-- Nonempty processor tails for private data. -/
  tail : 0 < d.literal/2
  /-- Nonempty site blocks. -/
  block : 0 < d.block
  /-- At least one processor per team. -/
  processors : 0 < d.processors
  /-- An ordinary literal and at most one extra pin field per processor. -/
  fields : d.fields ≤ 2
  /-- A team's processor slots fit its sequence of site blocks. -/
  room : d.processors*d.stride ≤ d.sites*d.block

/-- Recover the raw candidate and within-row offset from the logical destination word
and its lane. No final cell number or slot base is consulted. -/
def Layout.recoverDestination (d : Layout) : d.DestinationSlot → ℕ × ℕ
  | ⟨.inl j, lane⟩ =>
    let start := j.val*d.description
    let pos := start+lane.val
    let k := pos/(d.literal/2)-start/(d.literal/2)
    (privateIndex j k,pos-(slice start d.description (d.literal/2) k).1)
  | ⟨.inr (t,site), lane⟩ =>
    let pos := site.val*d.block+lane.val
    let p := pos/d.stride
    let spacing := d.literal+(d.teams-1)*d.link
    let f := (pos%d.stride)/spacing
    let start := p*d.stride+f*spacing
    let k := site.val-start/d.block
    (d.liveIndex t p f k,pos-(slice start d.literal d.block k).1)

private theorem private_slot (d : Layout) (bounds : d.DestinationBounds) (j : Fin d.entries)
    (k : Fin 2) (e : ℕ) (he : e < (slice (j.val*d.description) d.description (d.literal/2) k).2) :
    ∃ x : d.DestinationSlot, d.recoverDestination x = (privateIndex j k,e) ∧ ∀ pp lp,
      (d.privateRow pp j k).cell = (d.keyPlacement pp lp x.1).1 ∧
      (d.privateRow pp j k).slot+e = (d.keyPlacement pp lp x.1).2+x.2.val := by
  let start := j.val*d.description
  let sl := slice start d.description (d.literal/2) k
  let pos := sl.1+e
  obtain ⟨lo,hi,blo,bhi⟩ := inside he
  have le : start ≤ sl.1 := le_max_left ..
  have lane : pos-start < d.description := by change pos < start+d.description at hi; omega
  let x : d.DestinationSlot := ⟨.inl j,⟨pos-start,lane⟩⟩
  have back : start+(pos-start) = pos := by change start ≤ pos at lo; omega
  have block : pos/(d.literal/2) = start/(d.literal/2)+k.val := quotient bounds.tail blo bhi
  refine ⟨x,?_,fun pp lp => ⟨rfl,?_⟩⟩
  · let raw := start+(pos-start)
    let step := raw/(d.literal/2)-start/(d.literal/2)
    have hs : step = k.val := by simp only [step,raw,back,block,Nat.add_sub_cancel_left]
    change (privateIndex j step,raw-(slice start d.description (d.literal/2) step).1) = _
    rw [hs,show raw = pos from back]
    change (_,pos-sl.1) = _
    simp only [pos,Nat.add_sub_cancel_left]
  · change (pp j).2+(sl.1-start)+e = (pp j).2+(pos-start)
    dsimp only [pos]; omega

private theorem live_slot (d : Layout) (bounds : d.DestinationBounds) (t : Fin d.teams)
    (p : Fin d.processors) (f : Fin d.fields) (k : Fin (d.literal/d.block+2)) (e : ℕ)
    (he : e < (slice (p.val*d.stride+f.val*(d.literal+(d.teams-1)*d.link)) d.literal d.block k).2) :
    ∃ x : d.DestinationSlot, d.recoverDestination x = (d.liveIndex t p f k,e) ∧ ∀ pp lp,
      (d.liveRow lp t p f k).cell = (d.keyPlacement pp lp x.1).1 ∧
      (d.liveRow lp t p f k).slot+e = (d.keyPlacement pp lp x.1).2+x.2.val := by
  let spacing := d.literal+(d.teams-1)*d.link
  let start := p.val*d.stride+f.val*spacing
  let sl := slice start d.literal d.block k
  let pos := sl.1+e
  let site := start/d.block+k.val
  have ⟨lo,hi,blo,bhi⟩ : start ≤ pos ∧ pos < start+d.literal ∧
      site*d.block ≤ pos ∧ pos < site*d.block+d.block := inside he
  have span : f.val*spacing+d.literal ≤ d.stride := by
    have hf := f.isLt
    have lim := bounds.fields
    have cases : f.val = 0 ∧ (d.fields = 1 ∨ d.fields = 2) ∨ f.val = 1 ∧ d.fields = 2 := by omega
    rcases cases with ⟨h,h'|h'⟩ | ⟨h,h'⟩ <;> simp only [h,h',Layout.stride,spacing,zero_mul,zero_add,
      one_mul,Nat.two_mul] <;> omega
  change p.val*d.stride+f.val*spacing ≤ pos at lo
  change pos < p.val*d.stride+f.val*spacing+d.literal at hi
  change site*d.block ≤ pos at blo
  change pos < site*d.block+d.block at bhi
  have pHi : pos < p.val*d.stride+d.stride := by omega
  have pLo : p.val*d.stride ≤ pos := (Nat.le_add_right ..).trans lo
  have pIdx : pos/d.stride = p.val := quotient (by omega) pLo pHi
  have offset : pos % d.stride = pos-p.val*d.stride := by
    have h := Nat.div_add_mod' pos d.stride
    rw [pIdx] at h
    omega
  have fIdx : pos % d.stride / spacing = f.val := by
    rw [offset]
    apply quotient (by dsimp only [spacing]; have := bounds.tail; omega)
    · omega
    · have : d.literal ≤ spacing := Nat.le_add_right ..
      omega
  have extent : pos < d.sites*d.block :=
    (pHi.trans_le (by simpa [Nat.succ_mul] using Nat.mul_le_mul_right d.stride p.isLt)).trans_le bounds.room
  have siteFit : site < d.sites := (Nat.mul_lt_mul_right bounds.block).mp (blo.trans_lt extent)
  have lane : pos-site*d.block < d.block := by omega
  let x : d.DestinationSlot := ⟨.inr (t,⟨site,siteFit⟩),⟨pos-site*d.block,lane⟩⟩
  have back : site*d.block+(pos-site*d.block) = pos := by omega
  refine ⟨x,?_,fun pp lp => ⟨rfl,?_⟩⟩
  · let raw := site*d.block+(pos-site*d.block)
    let proc := raw/d.stride
    let field := (raw%d.stride)/spacing
    let start' := proc*d.stride+field*spacing
    let step := site-start'/d.block
    have hp : proc = p.val := by simp only [proc,raw,back,pIdx]
    have hf : field = f.val := by simp only [field,raw,back,fIdx]
    have hstart : start' = start := by simp only [start',hp,hf,start]
    have hs : step = k.val := by simp only [step,hstart,site,Nat.add_sub_cancel_left]
    change (d.liveIndex t proc field step,raw-(slice start' d.literal d.block step).1) = _
    rw [hp,hf,hstart,hs,show raw = pos from back]
    change (_,pos-sl.1) = _
    simp only [pos,Nat.add_sub_cancel_left]
  · change (lp (t.val*d.sites+site)).2+(sl.1-site*d.block)+e = (lp (t.val*d.sites+site)).2+(pos-site*d.block)
    have lb : site*d.block ≤ sl.1 := le_max_right ..
    dsimp only [pos]; omega

private theorem width_eq (d : Layout) (pp lp : ℕ → ℕ × ℕ) (i : ℕ) :
    (d.row pp lp i).width = (d.row (fun _ => (0,0)) (fun _ => (0,0)) i).width := by
  unfold Layout.row
  split <;> rfl

private theorem slot_exists (d : Layout) (bounds : d.DestinationBounds) (i : Fin d.candidates) (e : ℕ)
    (he : e < (d.row (fun _ => (0,0)) (fun _ => (0,0)) i).width) :
    ∃ x : d.DestinationSlot, d.recoverDestination x = (i.val,e) ∧ ∀ pp lp,
      (d.row pp lp i).cell = (d.keyPlacement pp lp x.1).1 ∧
      (d.row pp lp i).slot+e = (d.keyPlacement pp lp x.1).2+x.2.val := by
  by_cases privateRow : i.val < 2*d.entries
  · let j : Fin d.entries := ⟨i.val/2, (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr (by omega)⟩
    let k : Fin 2 := ⟨i.val%2, Nat.mod_lt _ (by decide)⟩
    have eq : privateIndex j k = i.val := Nat.div_add_mod i.val 2
    rw [← eq,(d.row_privateIndex _ _ j k).2] at he
    obtain ⟨x,hx,hh⟩ := private_slot d bounds j k e he
    refine ⟨x,hx.trans (congrArg (·,e) eq),fun pp lp => ?_⟩
    rw [← eq,(d.row_privateIndex pp lp j k).2]
    exact hh pp lp
  · let n := i.val-2*d.entries
    let pieces := d.literal/d.block+2
    let u := n/pieces
    let a := u/d.fields
    have hn : n < d.teams*d.processors*d.fields*pieces := by
      have hi := i.isLt
      change i.val < 2*d.entries + d.teams*d.processors*d.fields*pieces at hi
      dsimp only [n]; omega
    have hp : 0 < pieces := Nat.zero_lt_succ _
    have hf : 0 < d.fields := by
      by_contra! hz
      rw [show d.fields = 0 from by omega, Nat.mul_zero, Nat.zero_mul] at hn
      omega
    have hu : u < d.teams*d.processors*d.fields := (Nat.div_lt_iff_lt_mul hp).mpr hn
    have ha : a < d.teams*d.processors := (Nat.div_lt_iff_lt_mul hf).mpr hu
    let t : Fin d.teams := ⟨a/d.processors,(Nat.div_lt_iff_lt_mul bounds.processors).mpr ha⟩
    let p : Fin d.processors := ⟨a%d.processors,Nat.mod_lt _ bounds.processors⟩
    let f : Fin d.fields := ⟨u%d.fields,Nat.mod_lt _ hf⟩
    let k : Fin pieces := ⟨n%pieces,Nat.mod_lt _ hp⟩
    have eq : d.liveIndex t p f k = i.val := liveReencode d i (by omega)
    rw [← eq,(d.row_liveIndex _ _ t p f k).2] at he
    obtain ⟨x,hx,hh⟩ := live_slot d bounds t p f k e he
    refine ⟨x,hx.trans (congrArg (·,e) eq),fun pp lp => ?_⟩
    rw [← eq,(d.row_liveIndex pp lp t p f k).2]
    exact hh pp lp

/-- Classify a genuine candidate bit by its logical word and lane. The defining choice
uses the raw candidate index and bit, and the witness works for every placement. -/
noncomputable def Layout.destinationKey (d : Layout) (pp lp : ℕ → ℕ × ℕ) (bounds : d.DestinationBounds)
    (b : d.CandidateBit pp lp) : d.DestinationSlot :=
  Classical.choose (slot_exists d bounds b.1 b.2.val ((width_eq d pp lp b.1) ▸ b.2.isLt))

/-- The key and lane recover the original candidate number and the bit within it. -/
theorem Layout.recover_destinationKey (d : Layout) (pp lp : ℕ → ℕ × ℕ) (bounds : d.DestinationBounds)
    (b : d.CandidateBit pp lp) :
    d.recoverDestination (d.destinationKey pp lp bounds b) = (b.1.val,b.2.val) :=
  (Classical.choose_spec (slot_exists d bounds b.1 b.2.val ((width_eq d pp lp b.1) ▸ b.2.isLt))).1

/-- Distinct populated candidate bits occupy distinct logical word/lane pairs. -/
theorem Layout.destinationKey_injective (d : Layout) (pp lp : ℕ → ℕ × ℕ) (bounds : d.DestinationBounds) :
    Function.Injective (d.destinationKey pp lp bounds) := by
  rintro ⟨i,e⟩ ⟨j,f⟩ eq
  have back := (d.recover_destinationKey pp lp bounds ⟨i,e⟩).symm.trans
    ((congrArg d.recoverDestination eq).trans (d.recover_destinationKey pp lp bounds ⟨j,f⟩))
  have ij : i = j := Fin.ext (congrArg Prod.fst back)
  subst j
  exact congrArg (Sigma.mk i) (Fin.ext (congrArg Prod.snd back))

/-- The row actually names the cell in the placement directory, and its receiving slot
plus the bit offset is the placed word base plus the logical lane. -/
theorem Layout.destinationKey_placement (d : Layout) (pp lp : ℕ → ℕ × ℕ) (bounds : d.DestinationBounds)
    (b : d.CandidateBit pp lp) :
    let x := d.destinationKey pp lp bounds b
    (d.row pp lp b.1).cell = (d.keyPlacement pp lp x.1).1 ∧
      (d.row pp lp b.1).slot+b.2.val = (d.keyPlacement pp lp x.1).2+x.2.val :=
  (Classical.choose_spec (slot_exists d bounds b.1 b.2.val ((width_eq d pp lp b.1) ▸ b.2.isLt))).2 pp lp

end Packing.Directory

end BorderVNP
end Computability
end OAI
