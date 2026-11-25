import OAI.Hierarchy.ProtocolStackContraction
import OAI.Hierarchy.TaggedShorterGroups

namespace OAI
/-! # Contracting a finite menu of physical stacks at distinct word lengths -/

noncomputable section
namespace Hierarchy.Tagged.WideStack

open ThreeFlat Routing Spill CallPool
open TaggedShorterCompaction TaggedShorterNetwork TaggedShorterGroups ProtocolStackContraction
open scoped Classical BigOperators

/-- The number of physically wired candidates is the maximum appearing
in the next-fit volume bound, including any extra idle module rows. -/
theorem capacity_eq (G : Type) [Fintype G] (D B M : ℕ) :
    capacity G D B M = max M (Fintype.card G*TaggedShorterPacking.batches D B) := by
  apply congrArg (max M)
  let Bn := TaggedShorterPacking.batches D B
  calc
    Fintype.card (TaggedShorterGroups.Candidate G D B) = Fintype.card (G × Fin Bn) :=
      Fintype.card_congr (Equiv.sigmaEquivProd G (Fin Bn))
    _ = _ := by rw [Fintype.card_prod,Fintype.card_fin]

/-- A fixed selected term's occupied stacks, their physical board and the
size requirements for its actual compactors. -/
structure Board (F : Type*) [CommSemiring F] where
  Group : Type
  [finiteGroup : Fintype Group]
  D : ℕ
  halfBatch : ℕ
  address : ℕ
  width : ℕ
  modules : ℕ
  fraction : ℝ
  parentRows : ℝ
  counts : Group → ℕ
  positive : 0 < halfBatch
  batch : 2^address = 2*halfBatch
  bound : ∀ g, counts g ≤ D
  active : ((∑ g,counts g:ℕ):ℝ) ≤ fraction*parentRows
  padding : (Fintype.card Group:ℝ)*(2*halfBatch:ℕ) ≤ fraction*parentRows
  purchased : modules = ⌈6*fraction*parentRows/(2*halfBatch:ℕ)⌉₊
  near : Compactor F D (2^address) (address+width)
  far : Compactor F (capacity Group D halfBatch modules) modules (Width (2^address) (address+width))
  fits : 1+address+address ≤ width
  place : ∀ g, Bool → Fin (counts g) ↪ Fin D

attribute [instance] Board.finiteGroup

variable {F : Type*} [CommSemiring F]

abbrev Board.Slots (b : Board F) := Slot b.Group b.D → Bits b.width
abbrev Board.Labels (b : Board F) := Edge b.counts → Bits b.width

structure Settings (b : Board F) where
  mask : Fin (capacity b.Group b.D b.halfBatch b.modules) × Bool → Fin b.D → Bool
  occupied : Fin (capacity b.Group b.D b.halfBatch b.modules) → Bool
  id : Fin (capacity b.Group b.D b.halfBatch b.modules) × Bool → Fin b.D → Bits b.address

def Settings.close {b : Board F} (c : Settings b) (x : b.Slots) :=
  TaggedShorterBank.close (TaggedShorterBank.cut b.near b.far (lane F b.address b.address b.width))
    (oracle F b.address b.width)
    (input (read b.Group b.D b.halfBatch b.modules) x c.occupied c.mask c.id)

/-- Canonical occupied flags, endpoint masks and IDs of the ordered list
of links in the selected term. Every idle endpoint has zero metadata. -/
def Board.settings (b : Board F) : Settings b where
  mask := groupMask b.counts b.bound b.halfBatch b.modules b.place
  occupied := groupOccupied b.counts b.bound b.halfBatch b.modules
  id := groupID b.counts b.bound b.modules b.positive (by have := b.batch; omega) b.place

theorem Board.checks (b : Board F) :
    (∀ i a x, b.settings.mask (i,a) x = false → b.settings.id (i,a) x = fun _ => false) ∧
      ∀ x : b.Slots, b.settings.close x = if Linked b.place x then 1 else 0 :=
  by
    obtain ⟨ids,payload⟩ := checks_fixed b.counts b.positive b.batch b.bound b.active
      b.padding b.purchased b.near b.far b.fits b.place
    refine ⟨ids,fun x=> (payload x).trans ?_⟩
    by_cases ok : Linked b.place x
    · simp only [ite_eq_left ok,ite_eq_left (show ∀ g u, x (some g,true,b.place g true u)=
          x (some g,false,b.place g false u) from ok)]
    · simp only [ite_eq_right ok,ite_eq_right (show ¬∀ g u, x (some g,true,b.place g true u)=
          x (some g,false,b.place g false u) from ok)]

/-- The shared site weight may read any combination of types, including
records of different bit widths. Product of all actual closed boards and
canonical inactive padding picks exactly one copy of each tuple of active
wire assignments. The guesses for masks and IDs are fixed before that sum. -/
theorem contract {ι : Type} [Fintype ι] (b : ι → Board F) :
    let c := fun i => (b i).settings
    ∀ φ : (∀ i,(b i).Slots) → F,
      (∑ z : ∀ i,(b i).Slots,
        (∏ i, (c i).close (z i)) *
          (if ∀ i, Padding (b i).place (fun _=>false) (z i) then φ z else 0)) =
        ∑ a : ∀ i,(b i).Labels,
          φ (fun i => encode (b i).place (fun _=>false) (a i)) := by
  classical
  intro c φ
  have check (i : ι) := (b i).checks.2
  let emb : (∀ i,(b i).Labels) ↪ (∀ i,(b i).Slots) :=
    ⟨fun w i => encode (b i).place (fun _=>false) (w i),fun a d eq => funext fun i =>
      encode_injective (b i).place (fun _=>false) (congrFun eq i)⟩
  let value (z : ∀ i,(b i).Slots) :=
    (∏ i,(c i).close (z i)) * (if ∀ i, Padding (b i).place (fun _=>false) (z i) then φ z else 0)
  have recover (z : ∀ i,(b i).Slots) (valid : ∀ i, Padding (b i).place (fun _=>false) (z i))
      (linked : ∀ i, Linked (b i).place (z i)) : z ∈ Finset.univ.map emb := by
    choose a rep using fun i => exists_encode_of_valid (b i).place (fun _=>false) (z i)
      (valid i) (linked i)
    exact Finset.mem_map.mpr ⟨a,Finset.mem_univ _,funext rep⟩
  change ∑ z,value z = _
  calc
    _ = ∑ z ∈ Finset.univ.map emb,value z := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro z _ missing
      by_cases pad : ∀ i,Padding (b i).place (fun _=>false) (z i)
      · have dead : ¬∀ i, Linked (b i).place (z i) := fun ok => missing (recover z pad ok)
        obtain ⟨i,miss⟩ := Classical.not_forall.mp dead
        have zero : (c i).close (z i)=0 := (check i _).trans (ite_eq_right miss)
        have product : (∏ i,(c i).close (z i))=0 := Finset.prod_eq_zero (Finset.mem_univ i) zero
        simp only [value,product,zero_mul]
      · simp [value,pad]
    _ = _ := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro a _
      have hex (i : ι) := encoded_valid (b i).place (fun _=>false) (a i)
      have pad (i : ι) : Padding (b i).place (fun _=>false) (emb a i) := (hex i).1
      have linked (i : ι) : Linked (b i).place (emb a i) := (hex i).2
      have hits (i : ι) : (c i).close (emb a i) = 1 := (check i _).trans (ite_eq_left (linked i))
      simp only [value,hits,Finset.prod_const_one,ite_eq_left pad,one_mul]
      rfl

end Hierarchy.Tagged.WideStack

end
end OAI
