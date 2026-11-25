import OAI.ThreeFlat.Diagonal.CompressorDemandROM
import OAI.ThreeFlat.Diagonal.CompressorDemandFinite
import Mathlib.Data.ZMod.Defs

namespace OAI
/-! # Correctness of the two local old-width loops at one physical bundle -/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.Demand
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement Computability.VPVNP.Compression
open scoped Fin.CommRing BigOperators Classical
variable {n w d c t l : ℕ} {B H : Type*} [AddCommGroup H] [Fintype H] [Fintype B]
variable {P : PackingData B H (BitWord t) (BitWord l) d c} {E : Codec B w c t l} {base : B ↪ ℕ}
variable {data : Param → Word w} {m : Memory w} {vs : Fin n → Word w}
local notation "V" => Formula.value data m vs
variable {table tagCount laneCount : Formula n} {widths : Arc B H (BitWord t) (BitWord l) d c → ℕ}
variable {g : ArcColumns (Formula n)} (R : ArcReads P E (g.map (Formula.value data m vs)) m)
variable (W : WidthReads P E base data m vs table tagCount laneCount widths)
include R W
local notation "L" => layout table tagCount laneCount d c

omit [Fintype H] [Fintype B] in
theorem element_code (p : Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l) × Fin d)
    (s : Placement.Site (Formula n)) (port : Formula n) (h : Fin d) (u : Fin (2^c))
    (hs : s.map V = siteCode E p.1) (hp : V port = (p.2.val : Word w)) :
    V (element g L s port h u) = (gatherElements P widths p h u : Word w) := by
  let x : Placement.Position (Formula n) := ⟨s,.lit u.val,.lit h.val⟩
  let z := ((tagOrdinal c).symm u,P.slotLabel.symm h)
  let a : Arc B H (BitWord t) (BitWord l) d c := (p,z)
  have hx : x.map V = posCode P E (sourcePosition a) := by
    simp only [x,z,a,sourcePosition,posCode,Placement.Position.map,hs,Formula.value,
      Fin.ofNat_eq_cast,Equiv.apply_symm_apply,←tag_cast]
  let ae := ends (formulaOps n) g d false x port
  have he : ae.map V = encodeEnds P E a := ends_code g R false x port (sourcePosition a) p.2 hx hp
  have ht : ae.target.map V = posCode P E (sourcePosition (P.actual a)) := congrArg Ends.target he
  have f1 := bit_code g R x (sourcePosition a) hx
  have f2 := bit_code g R ae.target (sourcePosition (P.actual a)) ht
  have read := read_code W a x port hx hp
  change V ((formulaOps n).choose (thickBit (formulaOps n) g.toColumns x) (.lit 1)
    ((formulaOps n).choose (thickBit (formulaOps n) g.toColumns ae.target) (.lit 1) (width L x port) (.lit 0))
    (.lit 0)) = _
  simp only [eval_choose,show V (.lit 1)=1 from rfl,show V (.lit 0)=0 from rfl,f1,f2,read]
  by_cases h1 : P.thick (sourcePosition a) <;> by_cases h2 : P.thick (sourcePosition (P.actual a)) <;>
    simp only [a,z] at h1 h2 ⊢ <;>
    simp only [gatherElements,ttAt,h1,h2,and_self,and_false,and_true,ite_true,ite_false,Nat.cast_zero]

theorem total_code (p : Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l) × Fin d)
    (s : Placement.Site (Formula n)) (port : Formula n)
    (hs : s.map V = siteCode E p.1) (hp : V port = (p.2.val : Word w)) :
    V (thickWidth g L s port) = (CompressorPacking.thickWidth P widths p : Word w) := by
  rw [thickWidth,slots_word,←gather_elements,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.cast_sum]
  exact Finset.sum_congr rfl fun u _ => element_code R W p s port i u hs hp

omit [Fintype H] [Fintype B] in
theorem earlier_code (motif : P.Motif) (dir : Bool) (s : Placement.Site (Formula n))
    (port cutoff : Formula n) (i : Fin d) (u : Fin (2^c))
    (hs : s.map V = siteCode E (P.bundle motif).1) (hp : V port = ((P.bundle motif).2.val : Word w))
    (cut : V cutoff = (key P base motif.val : Word w)) :
    V (earlier g L s port cutoff dir i u) = (gatherRanks P (key P base) motif dir i u : Word w) := by
  let p := P.bundle motif
  let k := (tagOrdinal c).symm u
  let x : Placement.Position (Formula n) := ⟨toggle (formulaOps n) g.toColumns s,.lit u.val,port⟩
  let z := center P p i k
  let a := atCenter P p dir i k
  let e := ends (formulaOps n) g d dir x (.lit i.val)
  have hx : x.map V = posCode P E (sourcePosition z) := by
    have ns : (toggle (formulaOps n) g.toColumns s).map V = siteCode E (P.offsetSite.symm p.1) := by
      rw [eval_toggle,hs,toggle_inverse R.toGraphReads]
    simp only [x,z,k,center,Placement.Position.map,posCode,sourcePosition,ns,hp,Formula.value,
      Fin.ofNat_eq_cast,←tag_cast,Equiv.apply_symm_apply,p]
  have he : e.map V = encodeEnds P E a :=
    ends_code g R dir x (.lit i.val) (sourcePosition z) i hx rfl
  have hxbit := bit_code g R x (sourcePosition z) hx
  have hab := bit_code g R e.source (sourcePosition a) (congrArg Ends.source he)
  have ka := address_code W a e.source e.originalSlot (congrArg Ends.source he)
    (congrArg Ends.originalSlot he)
  have lt : V (physical L e.source e.originalSlot) < V cutoff ↔ key P base a < key P base motif.val := by
    rw [ka,cut,Fin.lt_def,Fin.val_cast_of_lt (W.ordinalFits _),Fin.val_cast_of_lt (W.ordinalFits _)]
  let test := Formula.select .lt (physical L e.source e.originalSlot) cutoff (.lit 1) (.lit 0)
  have value_test : V test = if key P base a < key P base motif.val then 1 else 0 := by
    rw [show V test = _ from eval_lt data m vs _ _ _ _]
    by_cases lower : key P base a < key P base motif.val
    · rw [ite_eq_left (lt.mpr lower),ite_eq_left lower];rfl
    · rw [ite_eq_right (fun h => lower (lt.mp h)),ite_eq_right lower];rfl
  have accepted : gatherRanks P (key P base) motif dir i u =
      if (¬P.thick (sourcePosition z) ∧ (dir=true → P.thick (sourcePosition a))) ∧
        key P base a < key P base motif.val then 1 else 0 := by
    cases dir <;> simp [gatherRanks,acceptedCenter,atCenter,a,z,p,k]
  change V ((formulaOps n).choose (thickBit (formulaOps n) g.toColumns x) (.lit 1) (.lit 0)
    (if dir then (formulaOps n).choose (thickBit (formulaOps n) g.toColumns e.source) (.lit 1) test (.lit 0)
     else test)) = _
  rw [accepted]
  cases dir <;> by_cases h1 : P.thick (sourcePosition z) <;>
    by_cases h2 : P.thick (sourcePosition a) <;> by_cases h3 : key P base a < key P base motif.val <;>
    simp [eval_choose,show V (.lit 1)=1 from rfl,show V (.lit 0)=0 from rfl,hxbit,hab,value_test,h1,h2,h3]

theorem rank_code (hc : 2 ≤ c) (motif : P.Motif) (s : Placement.Site (Formula n))
    (port cutoff : Formula n) (hs : s.map V = siteCode E (P.bundle motif).1)
    (hp : V port = ((P.bundle motif).2.val : Word w)) (cut : V cutoff = (key P base motif.val : Word w)) :
    V (bundleNumber g L s port cutoff) = ((motifNumbers P (key P base) hc motif).2.val : Word w) := by
  change V (allSlots (L).degree (L).colors (earlier g L s port cutoff false)) +
    V (allSlots (L).degree (L).colors (earlier g L s port cutoff true)) = _
  rw [slots_word,slots_word,←gather_ranks,Nat.cast_add]
  congr 1 <;> rw [Nat.cast_sum] <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    rw [Nat.cast_sum] <;> apply Finset.sum_congr rfl <;> intro u _ <;>
    exact earlier_code R W motif _ s port cutoff i u hs hp cut

end ThreeFlat.Diagonal.CompressorPacking.Native.Demand

end OAI
