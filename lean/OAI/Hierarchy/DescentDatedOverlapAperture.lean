import OAI.Hierarchy.DescentOverlapTables
import OAI.Hierarchy.DescentDatedAddressRate

namespace OAI
/-! # Native nondivisible changes of packed group width between consecutive dates -/
namespace Hierarchy.DescentSIMDLookup.Overlap
open DescentDatedAddressBook Filter
noncomputable section

theorem address_affine (base H G A B a : ℕ) :
    endAddress base H G A B a=base+endAddress 0 H G A B a := by
  simp [endAddress,dest,dictBase,Nat.add_assoc]

theorem address_rate {ι : ℕ→Type*} {H G A B a : ∀h,ι h→ℕ}
    (hosts : Bounded H) (groups : Bounded G) (old : Bounded A) (new : Bounded B)
    (packed : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,a h i*A h i≤K*h) :
    Bounded (fun h i=>endAddress 0 (H h i) (G h i) (A h i) (B h i) (a h i)) := by
  obtain ⟨K,hk⟩:=packed
  have batch : Bounded (fun h i=>chunks (G h i) (B h i)) :=
    (groups.add new).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have count : Bounded (fun h i=>pieces (G h i) (A h i) (B h i)) :=
    (groups.add old).of_le fun _ _=>(min_le_left ..).trans ((Nat.div_le_self ..).trans (Nat.sub_le ..))
  have pad:=((hosts.mul batch).add (Bounded.const 1)).padded
  have key:=((old.add (Bounded.const 1)).padded).mul (Bounded.pow_of_linear (K:=K) hk)
  apply ((((count.add (Bounded.const 1)).mul pad).add (count.mul key)).add pad).of_le
  intro h i
  simp only [endAddress,dest,dictBase,keyBits,Nat.pow_add,rows,mapBits,Nat.zero_add,Nat.le_refl]

/-- Repeated physical converters receive disjoint fresh address sections. They may have
different field widths. All earlier data read by every step remains in its prior section. -/
def pageFloor (base H G A B : ℕ) (bits : ℕ→ℕ) :=
  DescentDatedAddressBook.floor base (fun j=>endAddress 0 H G A B (bits j))

theorem next_page (base H G A B : ℕ) (bits : ℕ→ℕ) (j : ℕ) :
    endAddress (pageFloor base H G A B bits j) H G A B (bits j)=
      pageFloor base H G A B bits (j+1) := by
  rw [address_affine]
  rfl

theorem pages_rate {ι : ℕ→Type*} {count H G A B lo : ∀h,ι h→ℕ} (bits : ∀h,ι h→ℕ→ℕ)
    (hosts : Bounded H) (groups : Bounded G) (old : Bounded A) (new : Bounded B)
    (n : Bounded count) (origin : Bounded lo)
    (packed : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i j,j<count h i→bits h i j*A h i≤K*h) :
    Bounded (fun h i=>pageFloor (lo h i) (H h i) (G h i) (A h i) (B h i) (bits h i) (count h i)) := by
  let idx:=fun h=>Σi:ι h,Fin (count h i)
  have lift {v : ∀h,ι h→ℕ} (h : Bounded v) : Bounded (ι:=idx) (fun k p=>v k p.1) := by
    obtain ⟨K,b⟩:=h
    exact ⟨K,b.mono fun k hk p=>hk p.1⟩
  obtain ⟨K,hk⟩:=packed
  have all:=address_rate (ι:=idx) (a:=fun h p=>bits h p.1 p.2.val)
    (lift hosts) (lift groups) (lift old) (lift new) ⟨K,hk.mono fun h hh p=>hh p.1 p.2 p.2.isLt⟩
  obtain ⟨U,hu⟩:=all
  have one : Bounded (ι:=ι) (fun h _=>2^(U*h)) :=⟨U,Filter.Eventually.of_forall (fun _ _=>le_rfl)⟩
  obtain ⟨L,hl⟩:=origin.add (n.mul one)
  refine ⟨L,?_⟩
  filter_upwards [hu,hl] with h item cost
  intro i
  apply (DescentDatedAddressBook.floor_le (origin:=lo h i) _ _).trans (cost i)
  intro j hj
  exact item ⟨i,j,hj⟩

end
end Hierarchy.DescentSIMDLookup.Overlap

end OAI
