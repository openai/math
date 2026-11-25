import OAI.Computability.BorderVNP.PackedDirectoryEval

/-! # Public word-fit tests for the compact delivery directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory.ISA

open RoutingISA

/-- For one candidate it suffices to fit its half-open field and block endpoints.
The explicit index bound also covers a zero-width block during setup. -/
structure EndpointsFit (w start len block step : ℕ) : Prop where
  /-- Positive width is the Euclidean divisor. -/
  positive : 0 < block
  /-- Absolute block number. -/
  index : start/block+step < 2^w
  /-- End of the source field. -/
  fieldEnd : start+len < 2^w
  /-- End of the addressed uniform block. -/
  blockEnd : (start/block+step)*block+block < 2^w

private theorem intersection_safe_iff {w : ℕ} (pub : Arg → ℕ) (mem : ℕ → ℕ) (s : Reg → ℕ) :
    intersection.safeReadOnly w pub mem s ↔ EndpointsFit w (s 22) (s 23) (s 24) (s 25) := by
  have iff : ∀ a b c e, EndpointsFit w a b c e ↔ 0 < c ∧ a/c+e < 2^w ∧
      a+b < 2^w ∧ (a/c+e)*c+c < 2^w := fun a b c e =>
    ⟨fun h => ⟨h.positive,h.index,h.fieldEnd,h.blockEnd⟩,fun ⟨h1,h2,h3,h4⟩ => ⟨h1,h2,h3,h4⟩⟩
  by_cases left : s 22 < (s 22/s 24+s 25)*s 24 <;>
    by_cases right : (s 22/s 24+s 25)*s 24+s 24 < s 22+s 23 <;>
    simp (config := { decide := true }) [intersection, Code.block, Code.evalNat, Code.safeReadOnly,
      addressOpFits,addressOp,left,right,iff] <;> omega

/-- The private case uses the end of the actual two-word descriptor and both output
offsets. These numerical inequalities only refer to the original public layout. -/
def LayoutFitsPrivate (d : Layout) (w base : ℕ) (dest : ℕ → ℕ × ℕ) (i : ℕ) : Prop :=
  let j := i/2
  let start := j*d.description
  let block := d.literal/2
  let step := i%2
  let beginAt := max start ((start/block+step)*block)
  EndpointsFit w start d.description block step ∧
    base+j*2+1 < 2^w ∧ d.literal + beginAt < 2^w ∧ (dest j).2+beginAt < 2^w

/-- The live case uses its team/site entry in the two-word public placement array.
The stored offset and both intersection endpoints are checked before writing a row. -/
def LayoutFitsLive (d : Layout) (w base : ℕ) (dest : ℕ → ℕ × ℕ) (i : ℕ) : Prop :=
  let j := i - 2*d.entries
  let k := d.literal/d.block+2
  let u := j/k
  let a := u/d.fields
  let team := a/d.processors
  let start := a%d.processors*d.stride + u%d.fields*(d.literal+(d.teams-1)*d.link)
  let site := start/d.block+j%k
  let entry := team*d.sites+site
  let beginAt := max start (site*d.block)
  EndpointsFit w start d.literal d.block (j%k) ∧
    base+entry*2+1 < 2^w ∧ (dest entry).2+(beginAt-site*d.block) < 2^w

private theorem componentFits {x y base cap : ℕ} (h : base+(x+y)*2+1 < cap) : x < cap := by omega

/-- A finite list of ordinary coordinate inequalities certifies each candidate's
actual fixed-word computation, including all subtractions and Euclidean divisors. -/
theorem candidate_safe {w : ℕ} {d : Layout} {p l : ℕ} (pub : Arg → ℕ) (mem : ℕ → ℕ)
    (s : Reg → ℕ) (h : Prepared d p l s) (hp : 0 < d.processors) (hf : 0 < d.fields)
    (hrow : if s 19 < 2*d.entries then LayoutFitsPrivate d w p (placement mem p) (s 19)
      else LayoutFitsLive d w l (placement mem l) (s 19)) :
    candidate.safeReadOnly w pub mem s := by
  rcases h with ⟨⟨h0,h1,h2⟩,⟨h3,h4,h5,h6,h7,h8,h9,h10⟩,⟨h11,h12⟩,⟨h13,h14,h15,h16,h17,h18⟩⟩
  by_cases priv : s 19 < 2*d.entries
  · simp only [priv,ite_true,LayoutFitsPrivate,placement] at hrow
    obtain ⟨he,ha,ho,hd⟩ := hrow
    have room := he
    rcases he with ⟨hb,hi,hs,hl⟩
    simp (config := { decide := true }) [candidate,privateCandidate,Code.safeReadOnly,Code.evalNat,Code.block,
      addressOpFits,addressOp,priv,h13,h15,h4,h5,h9,h1,h2,h11,hp,intersect_eval,getPlacement,
      intersection_safe_iff,room]
    omega
  · simp only [priv,ite_false,LayoutFitsLive,placement] at hrow
    obtain ⟨he,ha,hd⟩ := hrow
    have hx := componentFits ha
    have room := he
    rcases he with ⟨hb,hi,hs,hl⟩
    simp (config := { decide := true }) [candidate,liveCandidate,Code.safeReadOnly,Code.evalNat,Code.block,
      addressOpFits,addressOp,priv,h13,h14,h8,h10,h4,h16,h17,h5,h7,h1,h2,h12,hp,hf,intersect_eval,
      getPlacement,intersection_safe_iff,room]
    repeat' apply And.intro
    all_goals omega

end Packing.Directory.ISA

end BorderVNP
end Computability
end OAI
