import OAI.Computability.BorderVNP.TransmissionSources

/-!
# The private site-description suffix in the live literal

An original description bit is assigned a consecutive tail index. The packing
program's public range identifies the same team, processor and literal offset.
This establishes the actual RAM source for every bit of every site description.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory

open VPVNP.BurstRAM BorderVNP.RoutingISA

/-- All programmed bits preceding the reserved suffix can be selected independently.
Inside the suffix, concatenate the actual descriptions and zero the unused capacity. -/
def Layout.literalBit (d : Layout) (literalHead : ℕ → ℕ → ℕ → Bool)
    (strings : Fin d.entries → Fin d.description → Bool) (team processor offset : ℕ) : Bool :=
  let head := d.literal-d.literal/2
  let linear := (team*d.processors+processor)*(d.literal/2) + (offset-head)
  if offset < head then literalHead team processor offset
  else if h : linear / d.description < d.entries ∧ linear % d.description < d.description then
    strings ⟨linear/d.description,h.1⟩ ⟨linear%d.description,h.2⟩
  else false

/-- The first portion of the physical literal retains the supplied program and its public
parameters verbatim. -/
theorem Layout.literalBit_head (d : Layout) (literalHead : ℕ → ℕ → ℕ → Bool)
    (strings : Fin d.entries → Fin d.description → Bool) (team processor offset : ℕ)
    (h : offset < d.literal - d.literal/2) :
    d.literalBit literalHead strings team processor offset = literalHead team processor offset := by
  simp [literalBit,h]

private theorem tail_field_bounds (d : Layout) (pp : ℕ → ℕ × ℕ) (j k e : ℕ)
    (he : e < (d.privateRow pp j k).width) :
    d.literal - d.literal/2 ≤ (d.privateRow pp j k).offset+e ∧
      (d.privateRow pp j k).offset+e < d.literal := by
  let t := d.literal/2
  let pos := j*d.description
  let p := slice pos d.description t k
  let u := pos/t+k
  change e < p.2 at he
  have h := (mem_slice_iff pos d.description t k (p.1+e)).mp (show p.1 ≤ p.1+e ∧ p.1+e < p.1+p.2 from ⟨by omega,by omega⟩)
  change pos ≤ p.1+e ∧ _ ∧ u*t ≤ p.1+e ∧ p.1+e < u*t+t at h
  have hl : u*t ≤ p.1 := by simp [p,u,slice]
  change d.literal-t ≤ (d.literal-t+(p.1-u*t))+e ∧ _ < _
  change d.literal-t ≤ (d.literal-t+(p.1-u*t))+e ∧ (d.literal-t+(p.1-u*t))+e < d.literal
  have ht : t ≤ d.literal := Nat.div_le_self _ _
  omega

/-- Every original private bit has an actual delivery row with a valid processor source
field; the encoded live literal at that position is precisely the original string bit. -/
theorem Layout.private_literal_row (d : Layout) (pp lp : ℕ → ℕ × ℕ) (literalHead : ℕ → ℕ → ℕ → Bool)
    (strings : Fin d.entries → Fin d.description → Bool) (j : Fin d.entries) (b : Fin d.description)
    (hp : 0 < d.processors) (ht : 0 < d.literal/2) (short : d.description ≤ d.literal/2)
    (fits : d.entries*d.description ≤ d.teams*d.processors*(d.literal/2)) :
    ∃ r ∈ d.directory pp lp, ∃ e < r.width, r.field = 0 ∧ r.team < d.teams ∧
      r.processor < d.processors ∧ r.offset+e < d.literal ∧
      r.cell = (pp j).1 ∧ r.slot+e = (pp j).2+b ∧
      d.literalBit literalHead strings r.team r.processor (r.offset+e) = strings j b := by
  obtain ⟨k,⟨e,he,hc,hslot,hsrc⟩,_⟩ := d.private_bit pp j ht short b
  let r := d.privateRow pp j k
  have hm : r ∈ d.directory pp lp := by
    obtain ⟨hindex,hrow⟩ := d.row_privateIndex pp lp j k
    exact (d.mem_directory_iff ..).mpr ⟨_,hindex,hrow,Nat.zero_lt_of_lt he⟩
  obtain ⟨hlo,hhi⟩ := tail_field_bounds d pp j k e he
  change d.literal-d.literal/2 ≤ r.offset+e at hlo
  change (r.team*d.processors+r.processor)*(d.literal/2)+(r.offset+e-(d.literal-d.literal/2)) = j.val*d.description+b.val at hsrc
  have hproc : r.processor < d.processors := Nat.mod_lt _ hp
  have hcap : j.val*d.description+b.val < d.teams*d.processors*(d.literal/2) :=
    ((Nat.add_lt_add_left b.isLt _).trans_le ((Nat.succ_mul _ _).symm ▸
      Nat.mul_le_mul_right d.description j.isLt)).trans_le fits
  have hteam : r.team < d.teams := by
    by_contra! no
    have h := (Nat.mul_le_mul_right d.processors no).trans (Nat.le_add_right _ r.processor)
    have hr := Nat.mul_le_mul_right (d.literal/2) h
    change (r.team*d.processors+r.processor)*(d.literal/2)+_ = j.val*d.description+b at hsrc
    omega
  refine ⟨r,hm,e,he,rfl,hteam,hproc,hhi,hc,hslot,?_⟩
  have hdiv : (j.val*d.description+b.val)/d.description = j.val := by
    rw [Nat.mul_comm j.val d.description, Nat.mul_add_div (Nat.zero_lt_of_lt b.isLt),Nat.div_eq_of_lt b.isLt,Nat.add_zero]
  have hmod : (j.val*d.description+b.val)%d.description = b.val := by
    rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt b.isLt]
  change d.literalBit literalHead strings r.team r.processor (r.offset+e) = _
  simp only [literalBit,ite_eq_right (Nat.not_lt_of_ge hlo),hsrc,hdiv,hmod,
    dite_eq_left (And.intro j.isLt b.isLt)]

/-- The real source word at each site-description delivery is the bit of the original
private network. The processor inputs may contain arbitrary code and public parameters
before the reserved tail. -/
theorem Layout.private_source_word {w : ℕ} (d : Layout) (pp lp : ℕ → ℕ × ℕ)
    (literalHead : ℕ → ℕ → ℕ → Bool) (strings : Fin d.entries → Fin d.description → Bool)
    (j : Fin d.entries) (b : Fin d.description) (hp : 0 < d.processors)
    (ht : 0 < d.literal/2) (short : d.description ≤ d.literal/2)
    (fits : d.entries*d.description ≤ d.teams*d.processors*(d.literal/2))
    (L : ℕ → Pins.Layout) (P : ∀ t, Pins.ProcessorFields (L t))
    (hlit : ∀ t, d.literal = (L t).literal) (hproc : ∀ t, d.processors = (L t).processors)
    (guess : ℕ → ℕ → Bool) (mem : ℕ → Memory w) (loaded : ∀ t, (P t).ContainsInput (mem t))
    (scratchI : ∀ t, (L t).processors*(L t).stride ≤ (L t).ibase)
    (scratchH : ∀ t, (L t).processors*(L t).stride ≤ (L t).hbase)
    (literals : ∀ t p, (P t).literal p =
      List.ofFn (fun i : Fin d.literal => d.literalBit literalHead strings t p.val i.val)) :
    ∃ r ∈ d.directory pp lp, ∃ e < r.width, r.team < d.teams ∧ r.cell = (pp j).1 ∧
      r.slot+e = (pp j).2+b ∧
      Pins.preparedMemory (L r.team) (guess r.team) (mem r.team) (L r.team).count
        (r.sourceBase (L r.team)+e) = Fin.ofNat _ (strings j b).toNat := by
  obtain ⟨r,hm,e,he,hf,hteam,hp',ho,hc,hslot,hs⟩ :=
    d.private_literal_row pp lp literalHead strings j b hp ht short fits
  refine ⟨r,hm,e,he,hteam,hc,hslot,?_⟩
  have read := r.literal_source (L r.team) (P r.team) (guess r.team) (mem r.team)
    (loaded r.team) e hf (hproc r.team ▸ hp') (hlit r.team ▸ ho) (scratchI _) (scratchH _)
  rw [read,literals]
  simp [TeamTapeInputEmit.headerWord,ho,hs]

end Packing.Directory

end BorderVNP
end Computability
end OAI
