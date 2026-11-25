import OAI.Hierarchy.TaggedShorterNetwork
import OAI.Hierarchy.TaggedShorterPacking
import OAI.ThreeFlat.Routing.CallAddressData

namespace OAI
/-! # Reserving a fixed candidate board for each supergroup

Candidate batches are bought before the number and endpoints of the links are
specified. A legal term selects a prefix of the candidates in each supergroup.
Its occurrence numbers determine the common identifiers at both endpoints.
-/

noncomputable section
namespace Hierarchy.TaggedShorterGroups
open ThreeFlat Routing Spill CallPool
open TaggedShorterCompaction TaggedShorterPacking TaggedShorterNetwork
open scoped Classical BigOperators

variable {G : Type} [Fintype G] {D B n M w : ℕ}

abbrev Candidate (G : Type) (D B : ℕ) := Batch (fun _ : G => D) B

def capacity (G : Type) [Fintype G] (D B M : ℕ) := max M (Fintype.card (Candidate G D B))

def board (G : Type) [Fintype G] (D B M : ℕ) : Candidate G D B ↪ Fin (capacity G D B M) :=
  (Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb (le_max_right _ _))

def read (G : Type) [Fintype G] (D B M : ℕ)
    (s : Fin (capacity G D B M) × Bool) (i : Fin D) : (Option G) × Bool × Fin D :=
  (Function.extend (board G D B M) (fun j => some j.1) (fun _ => none) s.1,s.2,i)

private theorem read_batch (c : G → ℕ) (hc : ∀ g, c g ≤ D) (j : Batch c B) (b : Bool) (i : Fin D) :
    read G D B M ((board G D B M) (batchAddress B hc j),b) i = (some j.1,b,i) := by
  simp only [read,(board G D B M).injective.extend_apply]
  rfl

def localID {c : G → ℕ} (hb : 0<B) (width : B≤2^n) (b : Batch c B) :
    Unit c B b ↪ Tagged.Bits n :=
  ((offset hb b).trans (Fin.castLEEmb width)).trans (Computability.VPVNP.RAMSerialization.wordBits n).toEmbedding

def groupBoard (size : G → ℕ) (bound : ∀g,size g≤D) (B M : ℕ) :
    Batch size B ↪ Fin (capacity G D B M) := (batchAddress B bound).trans (board G D B M)

def groupOccupied (size : G → ℕ) (bound : ∀g,size g≤D) (B M : ℕ)
    (i : Fin (capacity G D B M)) : Bool :=
  decide (Nonempty (AtCandidate (groupBoard size bound B M) (Unit size B) i))

def groupAddress (size : G → ℕ) (bound : ∀g,size g≤D) (B M : ℕ)
    (place : ∀g,Bool → Fin (size g) ↪ Fin D) (i : Fin (capacity G D B M)) (side : Bool) :
    AtCandidate (groupBoard size bound B M) (Unit size B) i ↪ Fin D :=
  locatedAddress (groupBoard size bound B M)
    (fun b => (Function.Embedding.subtype _).trans (place b.1 side)) i

def groupMask (size : G → ℕ) (bound : ∀g,size g≤D) (B M : ℕ)
    (place : ∀g,Bool → Fin (size g) ↪ Fin D) (sb : Fin (capacity G D B M) × Bool) (x : Fin D) : Bool :=
  decide (x ∈ Set.range (groupAddress size bound B M place sb.1 sb.2))

def groupID (size : G → ℕ) (bound : ∀g,size g≤D) (M : ℕ)
    (hb : 0<B) (width : B≤2^n) (place : ∀g,Bool → Fin (size g) ↪ Fin D)
    (sb : Fin (capacity G D B M) × Bool) : Fin D → Tagged.Bits n :=
  Function.extend (groupAddress size bound B M place sb.1 sb.2)
    (locatedAddress (groupBoard size bound B M) (localID hb width) sb.1) (fun _ _ => false)

theorem active_groupID (size : G → ℕ) (bound : ∀g,size g≤D) (M : ℕ)
    (hb : 0<B) (width : B≤2^n) (place : ∀g,Bool → Fin (size g) ↪ Fin D)
    (i : Fin (capacity G D B M)) (side : Bool)
    (u : AtCandidate (groupBoard size bound B M) (Unit size B) i) :
    groupID size bound M hb width place (i,side) (groupAddress size bound B M place i side u)=
      localID hb width u.val.1 u.val.2 := by
  unfold groupID
  rw [(groupAddress size bound B M place i side).injective.extend_apply]
  rfl

/-- All legal ordered occurrence lists of a given type share this same
two-level circuit and the same numbered leaf data reads. -/
theorem checks_fixed {F : Type*} [CommSemiring F] {cstar N : ℝ} (groupsize : G → ℕ)
    (hb : 0<B) (rows : 2^n=2*B) (bound : ∀ g, groupsize g ≤ D)
    (active : ((∑ g,groupsize g : ℕ):ℝ) ≤ cstar*N)
    (padding : (Fintype.card G : ℝ)*(2*B:ℕ) ≤ cstar*N)
    (modules : M = ⌈6*cstar*N/(2*B:ℕ)⌉₊)
    (near : Compactor F D (2^n) (n+w))
    (far : Compactor F (capacity G D B M) M (Width (2^n) (n+w)))
    (fits : 1+n+n ≤ w)
    (address : ∀ g, Bool → Fin (groupsize g) ↪ Fin D) :
    let mask := groupMask groupsize bound B M address
    let occupied := groupOccupied groupsize bound B M
    let id := groupID groupsize bound M hb (by omega : B≤2^n) address
    (∀ i b x, mask (i,b) x = false → id (i,b) x = fun _ => false) ∧
      ∀ payload : Option G × Bool × Fin D → Tagged.Bits w,
      TaggedShorterBank.close (TaggedShorterBank.cut near far (lane F n n w))
        (oracle F n w) (input (read G D B M) payload occupied mask id) =
        if ∀ g u, payload (some g,true,address g true u) = payload (some g,false,address g false u)
        then 1 else 0 := by
  let atBatch := (batchAddress B bound).trans (board G D B M)
  let U := Unit groupsize B
  let locals := AtCandidate atBatch U
  let xAddr (k : Fin (capacity G D B M)) (side : Bool) : locals k ↪ Fin D :=
    locatedAddress (U:=U) atBatch (fun b => (Function.Embedding.subtype _).trans (address b.1 side)) k
  have width : B≤2^n := by omega
  let ids (k : Fin (capacity G D B M)) := locatedAddress atBatch (localID hb width) k
  let id (sb : Fin (capacity G D B M) × Bool) :=
    Function.extend (xAddr sb.1 sb.2) (ids sb.1) (fun _ _ => false)
  have named k b a : id (k,b) (xAddr k b a) = ids k a := (xAddr k b).injective.extend_apply _ _ _
  have localFit k : 2*Fintype.card (locals k) ≤ 2^n := by
    let inBatch := locatedAddress atBatch (offset hb) k
    have size : Fintype.card (locals k) ≤ B := by simpa using Fintype.card_le_of_embedding inBatch
    omega
  have activeMask : (Finset.univ.filter (fun k => Nonempty (locals k))) ⊆ Finset.univ.map atBatch := by
    intro k hk
    obtain ⟨⟨⟨b,u⟩,he⟩⟩ := (Finset.mem_filter.mp hk).2
    exact Finset.mem_map.mpr ⟨b,Finset.mem_univ _,he⟩
  have poolFit : 2*(Finset.univ.filter (fun k => Nonempty (locals k))).card ≤ M := by
    have pay := half_modules Finset.univ groupsize hb (by simpa using active) (by simpa using padding)
    calc
      _ ≤ 2*(Finset.univ.map atBatch).card := Nat.mul_le_mul_left _ (Finset.card_le_card activeMask)
      _ = 2*∑ g, batches (groupsize g) B := by
        rw [Finset.card_map,Finset.card_univ]
        congr 1
        change Fintype.card (Σ g:G,Fin (batches (groupsize g) B)) = _
        exact (Fintype.card_sigma (α:=fun g:G=>Fin (batches (groupsize g) B))).trans
          (Finset.sum_congr rfl (fun g _=>Fintype.card_fin _))
      _ ≤ M := modules ▸ pay
  let mask := fun (sb : Fin (capacity G D B M) × Bool) i => decide (i ∈ Set.range (xAddr sb.1 sb.2))
  change (∀ i b x, mask (i,b) x = false → id (i,b) x = fun _ => false) ∧
     ∀ payload : Option G × Bool × Fin D → Tagged.Bits w,
       TaggedShorterBank.close (TaggedShorterBank.cut near far (lane F n n w))
         (oracle F n w) (input (read G D B M) payload (fun k => decide (Nonempty (locals k))) mask id) =
         if ∀ g u, payload (some g,true,address g true u) = payload (some g,false,address g false u)
         then 1 else 0
  refine ⟨?_,?_⟩
  · intro i b x off
    have idle : ¬(x∈Set.range (xAddr i b)) := of_decide_eq_false off
    exact Function.extend_apply' (ids i) (fun _ _ => false) x idle
  intro payload
  have eqn := TaggedShorterNetwork.checks near far fits (read G D B M) payload xAddr ids id named localFit poolFit
  refine eqn.trans ?_
  congr 1
  apply propext
  have actualRead (b : Batch groupsize B) (u : U b) (side : Bool) :
      read G D B M (atBatch b,side) (xAddr (atBatch b) side ⟨⟨b,u⟩,rfl⟩)=
        (some b.1,side,address b.1 side u.val) :=
    read_batch groupsize bound b side (address b.1 side u.val)
  constructor
  · intro done g u
    let b := batchIndex hb g u
    let unit : U b := ⟨u,rfl⟩
    have eq:=done (atBatch b) (⟨⟨b,unit⟩,rfl⟩ : locals (atBatch b))
    rw [actualRead b unit true,actualRead b unit false] at eq
    exact eq
  · rintro done k ⟨⟨b,u⟩,he⟩
    subst k
    rw [actualRead b u true,actualRead b u false]
    exact done b.1 u.val

theorem checks_uniform {F : Type*} [CommSemiring F] {cstar N : ℝ} (groupsize : G → ℕ)
    (hb : 0<B) (rows : 2^n=2*B) (bound : ∀ g, groupsize g ≤ D)
    (active : ((∑ g,groupsize g : ℕ):ℝ) ≤ cstar*N)
    (padding : (Fintype.card G : ℝ)*(2*B:ℕ) ≤ cstar*N)
    (modules : M = ⌈6*cstar*N/(2*B:ℕ)⌉₊)
    (near : Compactor F D (2^n) (n+w))
    (far : Compactor F (capacity G D B M) M (Width (2^n) (n+w)))
    (fits : 1+n+n ≤ w)
    (address : ∀ g, Bool → Fin (groupsize g) ↪ Fin D) :
    ∃ (mask : Fin (capacity G D B M) × Bool → Fin D → Bool)
      (occupied : Fin (capacity G D B M) → Bool)
      (id : Fin (capacity G D B M) × Bool → Fin D → Tagged.Bits n),
      (∀ i b x, mask (i,b) x = false → id (i,b) x = fun _ => false) ∧
      ∀ payload : Option G × Bool × Fin D → Tagged.Bits w,
      TaggedShorterBank.close (TaggedShorterBank.cut near far (lane F n n w))
        (oracle F n w) (input (read G D B M) payload occupied mask id) =
        if ∀ g u, payload (some g,true,address g true u) = payload (some g,false,address g false u)
        then 1 else 0 := by
  exact ⟨groupMask groupsize bound B M address,groupOccupied groupsize bound B M,
    groupID groupsize bound M hb (by omega) address,
    checks_fixed groupsize hb rows bound active padding modules near far fits address⟩

theorem checks {F : Type*} [CommSemiring F] {cstar N : ℝ} (groupsize : G → ℕ)
    (hb : 0<B) (rows : 2^n=2*B) (bound : ∀ g, groupsize g ≤ D)
    (active : ((∑ g,groupsize g : ℕ):ℝ) ≤ cstar*N)
    (padding : (Fintype.card G : ℝ)*(2*B:ℕ) ≤ cstar*N)
    (modules : M = ⌈6*cstar*N/(2*B:ℕ)⌉₊)
    (near : Compactor F D (2^n) (n+w))
    (far : Compactor F (capacity G D B M) M (Width (2^n) (n+w)))
    (fits : 1+n+n ≤ w)
    (address : ∀ g, Bool → Fin (groupsize g) ↪ Fin D)
    (payload : Option G × Bool × Fin D → Tagged.Bits w) :
    ∃ (mask : Fin (capacity G D B M) × Bool → Fin D → Bool)
      (occupied : Fin (capacity G D B M) → Bool)
      (id : Fin (capacity G D B M) × Bool → Fin D → Tagged.Bits n),
      (∀ i b x, mask (i,b) x = false → id (i,b) x = fun _ => false) ∧
      TaggedShorterBank.close (TaggedShorterBank.cut near far (lane F n n w))
        (oracle F n w) (input (read G D B M) payload occupied mask id) =
        if ∀ g u, payload (some g,true,address g true u) = payload (some g,false,address g false u)
        then 1 else 0 := by
  obtain ⟨mask,occupied,id,pad,all⟩ :=
    checks_uniform groupsize hb rows bound active padding modules near far fits address
  exact ⟨mask,occupied,id,pad,all payload⟩

end Hierarchy.TaggedShorterGroups

end
end OAI
