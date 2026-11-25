import OAI.Hierarchy.DescentPackedEpochShelves
import OAI.Hierarchy.DescentExteriorShelf
import OAI.Hierarchy.DescentDatedAddressRate
import OAI.Hierarchy.DescentTerminalRoleTables

namespace OAI
/-! # The genuine compact original input and its first mutable calendar address -/
namespace Hierarchy.DescentDatedAddressBook
open DescentPackedEpochShelves DescentTerminalEpochChart DescentPackedProfileTape DescentDatedAddressBook Filter
noncomputable section
structure InitialArea (A : Type) where
  seedStop : ℕ
  profileCapacity : ℕ
  grain : ℕ
  epochs : List (Source A)
  headBits : ℕ
  restBits : ℕ
  exteriorLanes : ℕ
  exteriorRows : ℕ
  roleBits : Fin 6→ℕ

namespace InitialArea
variable {A : Type} (v : InitialArea A)
/-- Original bit header and epoch data followed by the actual packed public decoding ROM. -/
def compact := DescentPackedProfileInstall.end_ (v.seedStop+extent v.grain v.epochs) v.profileCapacity v.grain
def exterior :=DescentExteriorShelf.span v.headBits v.restBits v.exteriorLanes v.exteriorRows
def physicalStop :=v.compact+17*v.exterior
/-- The 17 true columns fit in one dyadic input bank of size 32 times the row span. -/
def roleBase :=v.compact+32*v.exterior
def floor := v.roleBase+DescentTerminalRoleTables.count v.roleBits

theorem role_words {field : Fin 6→ℕ} : DescentTerminalRoleTables.count field≤2^((∑f,field f)+3) := by
  let mux:=∏f,2^(field f)
  have each (f:Fin 6) : 2^(field f)≤ mux := by
    dsimp only [mux]
    rw [Finset.prod_pow_eq_pow_sum]
    exact Nat.pow_le_pow_right (by decide) (Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ f))
  have marks : (∑f,2^(field f))≤6*mux :=by simpa using Finset.sum_le_sum (s:=Finset.univ) (fun f _=>each f)
  change (∑f,2^(field f))+mux+mux≤_
  calc
    _≤8*mux:=by omega
    _=2^((∑f,field f)+3):=by dsimp only [mux];rw [Finset.prod_pow_eq_pow_sum,pow_add];ring

theorem before (v : InitialArea A) : v.physicalStop≤v.floor := by
  unfold physicalStop floor roleBase
  omega

variable {ι : ℕ→Type*} (I : ∀h,ι h→InitialArea A)
theorem original_rate
    (seed : Bounded (fun h i=>(I h i).seedStop))
    (slots_ : Bounded (fun h i=>((I h i).epochs.map (fun s=>slots s.seats (I h i).grain)).sum))
    (epochs : Bounded (fun h i=>(I h i).epochs.length)) (grain : Bounded (fun h i=>(I h i).grain))
    (rows : Bounded (fun h i=>DescentExteriorShelf.rows (I h i).headBits (I h i).restBits (I h i).exteriorRows))
    (roles : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,(∑f:Fin 6,(I h i).roleBits f)+3≤K*h)
    (field : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,let v:=I h i;
      (DescentTerminalEpochBits.width v.profileCapacity+1)*v.grain≤K*h ∧
      DescentExteriorShelf.tableBits v.headBits v.restBits v.exteriorLanes≤K*h) :
    Bounded (fun h i=>(I h i).floor) := by
  obtain ⟨K,hw⟩:=field
  have dictionary:=Bounded.pow_of_linear (K:=K) (hw.mono fun h hh i=>(hh i).1)
  have exterior:=Bounded.pow_of_linear (K:=K) (hw.mono fun h hh i=>(hh i).2)
  have plan : Bounded (fun h i=>extent (I h i).grain (I h i).epochs) :=
    (((Bounded.const 4).mul slots_).add ((Bounded.const 2).mul epochs)).of_le fun h i=>
      extent_le _ _
  have header:=(((seed.add plan).add (((Bounded.const 2).mul (grain.add (Bounded.const 1))).add (Bounded.const 1))).add
    (((Bounded.const 2).mul dictionary).add (Bounded.const 1)))
  have compact_ : Bounded (fun h i=>(I h i).compact) := header.of_le fun h i=>
    DescentPackedProfileInstall.extent _ _ _
  have region : Bounded (fun h i=>(I h i).exterior) := by
    apply (rows.padded.max' exterior).of_le
    intro h i
    let v:=I h i
    change 2^(max (Nat.clog 2 (DescentExteriorShelf.rows v.headBits v.restBits v.exteriorRows))
      (DescentExteriorShelf.tableBits v.headBits v.restBits v.exteriorLanes))≤_
    rcases le_total (Nat.clog 2 (DescentExteriorShelf.rows v.headBits v.restBits v.exteriorRows))
      (DescentExteriorShelf.tableBits v.headBits v.restBits v.exteriorLanes) with less|less
    · rw [max_eq_right less];exact Nat.le_max_right ..
    · rw [max_eq_left less];exact Nat.le_max_left ..
  obtain ⟨K',hi⟩:=roles
  have rates:=Bounded.pow_of_linear (K:=K') hi
  have static : Bounded (fun h i=>DescentTerminalRoleTables.count (I h i).roleBits) :=rates.of_le fun h i=>role_words
  exact (compact_.add ((Bounded.const 32).mul region)).add static

end InitialArea
end
end Hierarchy.DescentDatedAddressBook

end OAI
