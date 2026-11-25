import OAI.Hierarchy.DescentDatedOrdinaryPrimitiveRate
import OAI.Hierarchy.DescentDatedPrimitiveFunding

namespace OAI
/-! The compilation height of the primitive date uses exactly the queried word widths already paid. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentOrdinaryPrimitiveCheckpoint DescentDatedAddressBook Filter
noncomputable section
variable {F P : Type} [Field F]
theorem primitivePeak_of_funding (v : PhysicalOrdinary F P) {h unit : ℕ}
    (paid : v.paletteShape.Funding h unit) (chip : (2*v.bornBook.chipBits)*v.bornBook.lanes≤h/2) :
    primitivePeak v≤h/2:=by
  have raw : DescentOperandFamilyBook.unit 1 v.bornBook.chipBits*v.bornBook.lanes≤h/2:=by
    simpa only [DescentOperandFamilyBook.unit,Nat.mul_one,two_mul] using chip
  simp only [primitivePeak,List.foldr,max_le_iff]
  exact ⟨raw,paid.oldKey,paid.newbornKey,paid.originKey,paid.durableKey,paid.projection,paid.gates,
    paid.spread,paid.selection,Nat.zero_le _⟩

theorem primitivePeak_bounded {ι : ℕ→Type*} {Pins : ∀h,ι h→Type} (v : ∀h (i:ι h),PhysicalOrdinary F (Pins h i)) (unit : ∀h,ι h→ℕ)
    (funded : ∀ᶠ h : ℕ in atTop,∀i,(v h i).paletteShape.Funding h (unit h i))
    (chips : ∀ᶠ h : ℕ in atTop,∀i,(2*(v h i).bornBook.chipBits)*(v h i).bornBook.lanes≤h/2) :
    ∃C : ℕ,∀ᶠ h : ℕ in atTop,∀i,primitivePeak (v h i)≤C*h:=by
  refine ⟨1,?_⟩
  filter_upwards [funded,chips] with h selected book
  intro i
  simpa only [Nat.one_mul] using (primitivePeak_of_funding _ (selected i) (book i)).trans (Nat.div_le_self ..)

/-- The five batch counts require no new address estimate: each is at most the purchased word width. -/
theorem primitive_scalar_room {ι : ℕ→Type*} {Pins : ∀h,ι h→Type} (v : ∀h (i:ι h),PhysicalOrdinary F (Pins h i)) (unit : ∀h,ι h→ℕ)
    (funded : ∀ᶠ h : ℕ in atTop,∀i,(v h i).paletteShape.Funding h (unit h i))
    (chips : ∀ᶠ h : ℕ in atTop,∀i,(2*(v h i).bornBook.chipBits)*(v h i).bornBook.lanes≤h/2)
    (hh : Bounded (fun h i=>(v h i).paletteShape.hosts)) (gg : Bounded (fun h i=>(v h i).paletteShape.groups))
    (lo : Bounded (fun h i=>(v h i).paletteShape.lows)) (bb : Bounded (fun h i=>(v h i).paletteShape.blocks))
    (pp : Bounded (fun h i=>(v h i).paletteShape.ports)) (cc : Bounded (fun h i=>(v h i).paletteShape.capacity))
    (oo : Bounded (fun h i=>(v h i).paletteShape.oldNodes))
    (parent : ∀h i,(v h i).bornBook.hosts=(v h i).paletteShape.hosts ∧
      (v h i).bornBook.groups=(v h i).paletteShape.oldGroups ∧
      (v h i).bornBook.blocks=(v h i).paletteShape.blocks ∧ (v h i).bornBook.cap=(v h i).paletteShape.capacity) :
    PrimitiveScalarRoom v:=by
  have cap (slots : ∀h,ι h→ℕ)
      (under : ∀h i,(v h i).paletteShape.Funding h (unit h i)→slots h i≤h) : Bounded slots:=by
    refine ⟨1,?_⟩
    filter_upwards [funded] with h bound
    exact fun i=>by simpa only [Nat.one_mul] using (under h i (bound i)).trans Nat.lt_two_pow_self.le
  exact ⟨hh,gg,lo,bb,pp,cc,oo,cap _ (fun _ _ z=>z.old.ceiling),cap _ (fun _ _ z=>z.newborn.ceiling),
    cap _ (fun _ _ z=>z.ranks.ceiling),cap _ (fun _ _ z=>z.working.ceiling),cap _ (fun _ _ z=>z.held.ceiling),
    hh.of_le (fun h i=>(parent h i).1.le),(gg.mul bb).of_le (fun h i=>(parent h i).2.1.le),
    bb.of_le (fun h i=>(parent h i).2.2.1.le),cc.of_le (fun h i=>(parent h i).2.2.2.le),
    primitivePeak_bounded v unit funded chips⟩

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
