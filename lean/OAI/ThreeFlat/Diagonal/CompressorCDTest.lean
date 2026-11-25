import OAI.ThreeFlat.Diagonal.CompressorDemandInput
import OAI.ThreeFlat.Diagonal.CompressorDenseRead

namespace OAI
/-! # A bounded ordered search recovers the unique accepted low color word -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkWidth
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr RAM.DescriptorExpr Placement
open scoped Classical Fin.NatCast
variable {n w c d t l : ℕ} {B H : Type*} [AddCommGroup H]
variable {P : PackingData B H (BitWord t) (BitWord l) d c} {E : Codec B w c t l}
variable {data : Param → Word w} {m : Memory w} {vs : Fin n → Word w}
local notation "V" => Formula.value data m vs
variable {g : ArcColumns (F n)} (R : ArcReads P E (g.map (Formula.value data m vs)) m)
variable {table tags lanes : F n}
local notation "L" => Demand.layout table tags lanes d c

theorem first_word {k : ℕ} (test : Fin k → F n) (i : Fin k) (xs : List (Fin k))
    (has : i∈xs) (only : ∀j, V (test j)=1 ↔ j=i) :
    V (firstWord test xs)=(i.val:Word w) := by
  induction xs with
  | nil => simp at has
  | cons j ys ih =>
    by_cases h : j=i
    · subst j
      simp [firstWord,Formula.value,Comparison.test,(only i).2 rfl,Fin.ofNat_eq_cast]
    · have miss := (only j).not.mpr h
      have mem : i∈ys := (List.mem_cons.mp has).resolve_left (Ne.symm h)
      simpa [firstWord,Formula.value,Comparison.test,miss] using ih mem

theorem rank_unique (a : P.Motif) (hc : 2≤c) (j : Fin (2^c)) (hj : j∈oldBlock P a.val.1 a.val.2.2) :
    blockIndex P a.val.1 a.val.2.2 j =
      blockIndex P a.val.1 a.val.2.2 (tagOrdinal c a.val.2.1) ↔ j=tagOrdinal c a.val.2.1 := by
  let s := oldBlock P a.val.1 a.val.2.2
  let u : s := ⟨j,hj⟩
  let v : s := (blockCoordinates P a).2
  let e := s.orderIsoOfFin (oldBlock_card P a.val.1 a.val.2.2 hc)
  constructor
  · intro same
    have hu := blockIndex_listed P _ _ u hc
    have hv := blockIndex_listed P _ _ v hc
    have h : e.symm u=e.symm v := Fin.ext (hu.symm.trans (same.trans hv))
    exact congrArg Subtype.val (e.symm.injective h)
  · rintro rfl
    rfl

private theorem candidate_position (a : P.Motif) (x : Placement.Position (F n)) (i : Fin (2^c))
    (hsite : x.site.map V = siteCode E a.val.1.1) (hlabel : V x.slot = slotCode P a.val.2.2) :
    ({x with bits := Formula.lit i.val} : Placement.Position (F n)).map V =
      posCode P E (sourcePosition (a.val.1,(tagOrdinal c).symm i,a.val.2.2)) := by
  change Placement.Position.mk (x.site.map V) (i.val : Word w) (V x.slot) =
    Placement.Position.mk (siteCode E a.val.1.1) (tagWord E.colors ((tagOrdinal c).symm i)) (slotCode P a.val.2.2)
  rw [hsite,hlabel,←Demand.tag_cast,Equiv.apply_symm_apply]

include R
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem test_code (hc : 2≤c) (wide : 2^c<2^w) (a : P.Motif)
    (x : Placement.Position (F n)) (slot rank : F n)
    (hsite : x.site.map V=siteCode E a.val.1.1) (hlabel : V x.slot=slotCode P a.val.2.2)
    (hslot : V slot=(a.val.1.2.val:Word w))
    (hrank : V rank=(blockIndex P a.val.1 a.val.2.2 (tagOrdinal c a.val.2.1):Word w))
    (i : Fin (2^c)) : V (cdTest g L x slot rank i)=1 ↔ i=tagOrdinal c a.val.2.1 := by
  let y : Placement.Position (F n) := {x with bits := Formula.lit i.val}
  let b : Arc B H (BitWord t) (BitWord l) d c := (a.val.1,(tagOrdinal c).symm i,a.val.2.2)
  have hy : y.map V = posCode P E (sourcePosition b) := candidate_position a x i hsite hlabel
  let e : Ends (F n) := ends (Demand.formulaOps n) g d false y slot
  have he : e.map V = encodeEnds P E b := Demand.ends_code g R false y slot (sourcePosition b) a.val.1.2 hy hslot
  have h₁ := Demand.bit_code g R y (sourcePosition b) hy
  have h₂ := Demand.bit_code g R e.target (sourcePosition (P.actual b)) (congrArg Ends.target he)
  have lo := lowerCD_code (table:=table) (tags:=tags) (lanes:=lanes) R y slot b hy hslot
  have upper (j : Fin (2^c)) : blockIndex P a.val.1 a.val.2.2 j<2^w := by
    apply Nat.lt_of_le_of_lt _ wide
    exact (Finset.card_filter_le _ _).trans (by simpa using Finset.card_le_univ (oldBlock P a.val.1 a.val.2.2))
  have nd : (0:Word w)≠1 := by
    apply ne_of_lt
    change 0 < 1 % (2^w)
    have h : 1<2^w := lt_of_le_of_lt (Nat.two_pow_pos c) wide
    simpa only [Nat.mod_eq_of_lt h] using Nat.zero_lt_one
  have choice : V (lowerCD g L y slot)=V rank ↔
      blockIndex P a.val.1 a.val.2.2 i=blockIndex P a.val.1 a.val.2.2 (tagOrdinal c a.val.2.1) := by
    rw [lo,hrank]
    change ((blockIndex P _ _ (tagOrdinal c ((tagOrdinal c).symm i)):Word w) = _) ↔ _
    rw [Equiv.apply_symm_apply]
    constructor
    · intro equal
      have vals := congrArg Fin.val equal
      change ((blockIndex P a.val.1 a.val.2.2 i : Word w).val) =
        ((blockIndex P a.val.1 a.val.2.2 (tagOrdinal c a.val.2.1) : Word w).val) at vals
      rw [Fin.val_cast_of_lt (upper i),Fin.val_cast_of_lt (upper (tagOrdinal c a.val.2.1))] at vals
      exact vals
    · intro equal
      exact congrArg (fun z : ℕ => (z : Word w)) equal
  have member : i∈oldBlock P a.val.1 a.val.2.2 ↔
      ¬(P.thick (sourcePosition b) ∧ P.thick (sourcePosition (P.actual b))) := by simp [oldBlock,b]
  have trueMem : tagOrdinal c a.val.2.1∈oldBlock P a.val.1 a.val.2.2 := (blockCoordinates P a).2.property
  change V (.select .eq ((Demand.formulaOps n).choose (thickBit (Demand.formulaOps n) g.toColumns y) (.lit 1)
    ((Demand.formulaOps n).choose (thickBit (Demand.formulaOps n) g.toColumns e.target) (.lit 1) (.lit 0) (.lit 1))
    (.lit 1)) (.lit 1) (.select .eq (lowerCD g L y slot) rank (.lit 1) (.lit 0)) (.lit 0))=1 ↔ _
  by_cases hsrc : P.thick (sourcePosition b) <;> by_cases hdst : P.thick (sourcePosition (P.actual b))
  · have miss := member.not.mpr (by simp [hsrc,hdst])
    have ne : i≠tagOrdinal c a.val.2.1 := fun h => miss (h ▸ trueMem)
    simp [Demand.eval_choose,Formula.value,Comparison.test,h₁,h₂,hsrc,hdst,ne,nd]
  all_goals
    have mem := member.mpr (by simp [*])
    have rnk := rank_unique a hc i mem
    simp [Demand.eval_choose,Formula.value,Comparison.test,h₁,h₂,hsrc,hdst,choice,rnk,nd]

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkWidth

end OAI
