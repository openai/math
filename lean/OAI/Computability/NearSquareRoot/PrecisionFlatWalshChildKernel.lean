import OAI.Computability.NearSquareRoot.PrecisionFlatWalshKernel

/-! # Packed selected addresses of a recursive Walsh child

A child transforms the two bits of its chosen lane in each column. All
other lanes are spectator coordinates shared by the input and output.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FlatWalshKernel

open Finset Matrix KernelPass KernelScaleLayout

private def laneSlots (a h : ℕ) (j : Fin (a+1)) : Fin h × Fin 2 ↪ Fin ((a+1)*(2*h)) where
  toFun v := slots a h (j,v)
  inj' _ _ e := congrArg Prod.snd ((slots a h).injective e)

/-- The `2*h` bit positions of one child lane in its packed bank. -/
def laneBits (a h : ℕ) (j : Fin (a+1)) : Finset (Fin ((a+1)*(2*h))) :=
  univ.map (laneSlots a h j)

theorem laneBits_card (a h : ℕ) (j : Fin (a+1)) : (laneBits a h j).card = 2*h := by
  simp [laneBits, Nat.mul_comm]

private theorem slot_mem {a h : ℕ} (j l : Fin (a+1)) (v : Fin h × Fin 2) :
    slots a h (l,v) ∈ laneBits a h j ↔ l = j := by
  rw [laneBits, mem_map]
  constructor
  · rintro ⟨r,_,e⟩
    exact (congrArg Prod.fst ((slots a h).injective e)).symm
  · rintro rfl
    exact ⟨v, mem_univ _, rfl⟩

private theorem digit_eq (x y : ZMod 2) :
    decide (y = 1) = decide (x = 1) ↔ x = y := by
  have h : ∀ i j : Fin 2, decide (j = 1) = decide (i = 1) ↔ i = j := by decide
  exact h x y

private theorem off_lane {a h : ℕ} (j : Fin (a+1)) (y x : Addr (a+1) h) :
    BoxFin.offBits (laneBits a h j) (rank y) (rank x) ↔
      ∀ t l, l ≠ j → x t l = y t l := by
  constructor
  · intro hf t l hne
    funext b
    have hd := hf (slots a h (l,t,b)) (fun hm => hne ((slot_mem ..).mp hm))
    rw [testBit_rank, testBit_rank] at hd
    exact (digit_eq ..).mp hd
  · intro hf p hn
    obtain ⟨⟨l,t,b⟩,rfl⟩ := (slots a h).surjective p
    have hne := mt (slot_mem j l (t,b)).mpr hn
    rw [testBit_rank, testBit_rank, hf t l hne]

private theorem flat_on_fiber {n : ℕ} {s : Finset (Fin n)} (y x : Fin (2^n))
    (hs : BoxFin.offBits s y x) :
    BoxFin.flatWalsh s y x = ∏ b ∈ s, bitFactor (y.val.testBit b.val) (x.val.testBit b.val) := by
  classical
  simp only [BoxFin.flatWalsh, Matrix.of_apply, ite_eq_left hs, bitFactor, prod_mul_distrib,
    prod_const, Bool.and_eq_true]
  congr 1
  rw [← prod_filter]
  simp [BoxFin.physicalOverlap]

/-- Every dyadic entry of the child matrix is its selected Walsh entry at
the physically stored packed ordinals. -/
theorem packed_child_entry {a h : ℕ} (j : Fin (a+1)) (y x : Addr (a+1) h) :
    (∏ t, (childEntry j (y t) (x t) : ℂ)) =
      BoxFin.flatWalsh (laneBits a h j) (rank y) (rank x) := by
  classical
  by_cases hf : ∀ t l, l ≠ j → x t l = y t l
  · have off := (off_lane j y x).mpr hf
    rw [flat_on_fiber _ _ off, laneBits, prod_map, Fintype.prod_prod_type]
    apply prod_congr rfl
    intro t _
    rw [childEntry, ite_eq_left (hf t), bitPair]
    apply prod_congr rfl
    intro b _
    change _ = bitFactor ((KernelScaleLayout.rank y).val.testBit (slots a h (j,t,b)).val)
      ((KernelScaleLayout.rank x).val.testBit (slots a h (j,t,b)).val)
    rw [testBit_rank, testBit_rank]
  · have off := mt (off_lane j y x).mp hf
    simp only [BoxFin.flatWalsh, Matrix.of_apply, ite_eq_right off]
    push Not at hf
    obtain ⟨t,l,hl,hne⟩ := hf
    apply prod_eq_zero (mem_univ t)
    simp [childEntry, show ¬ ∀ b ≠ j, x t b = y t b from fun g => hne (g l hl)]

/-- The bit order inside an MSF lane is reversed in the packed ordinal's
ordinary low-to-high bit numbering. -/
theorem slots_val (a h : ℕ) (j : Fin (a+1)) (t : Fin h) (b : Fin 2) :
    (slots a h (j,t,b)).val = (a+1)*(2*h)-1-(j.val*(2*h)+(2*t.val+b.val)) := by
  simp [slots, Fin.rev, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm]
  omega

/-- Any embedding of the contiguous bit window with the lane's offset has
exactly the child mask as its image. -/
theorem laneBits_eq_window (a h : ℕ) (j : Fin (a+1))
    (e : Fin (2*h) ↪ Fin ((a+1)*(2*h)))
    (he : ∀ p, (e p).val = (a-j.val)*(2*h) + p.val) : laneBits a h j = univ.map e := by
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    obtain ⟨⟨t,b⟩,_,rfl⟩ := mem_map.mp hp
    change slots a h (j,t,b) ∈ univ.map e
    have hi : 2*t.val+b.val < 2*h := by omega
    let q : Fin (2*h) := ⟨2*h-1-(2*t.val+b.val), by omega⟩
    refine mem_map.mpr ⟨q, mem_univ _, Fin.ext ?_⟩
    rw [he, slots_val, Nat.succ_mul a (2*h)]
    have hs : (a-j.val)*(2*h) + j.val*(2*h) = a*(2*h) := by
      rw [← Nat.add_mul, show a-j.val+j.val = a by omega]
    dsimp only [q]
    omega
  · simp [laneBits_card]

/-- Spectator tests can recognize the child by one range comparison, for
both the empty lane and nonempty lanes. -/
theorem mem_laneBits_iff {a h : ℕ} (j : Fin (a+1)) (p : Fin ((a+1)*(2*h))) :
    p ∈ laneBits a h j ↔ (a-j.val)*(2*h) ≤ p.val ∧ p.val < (a-j.val)*(2*h) + 2*h := by
  let d := (a-j.val)*(2*h)
  have bound : d+2*h ≤ (a+1)*(2*h) := by
    rw [Nat.succ_mul a (2*h)]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.sub_le ..)) _
  let e : Fin (2*h) ↪ Fin ((a+1)*(2*h)) :=
    ⟨fun q => ⟨d+q.val, by omega⟩, fun q r he => Fin.ext (by simpa using congrArg Fin.val he)⟩
  rw [laneBits_eq_window a h j e (fun _ => rfl), mem_map]
  change _ ↔ d ≤ p.val ∧ p.val < d+2*h
  constructor
  · rintro ⟨q,_,rfl⟩
    change d ≤ d+q.val ∧ d+q.val < d+2*h
    omega
  · rintro ⟨lo,hi⟩
    refine ⟨⟨p.val-d, by omega⟩, mem_univ _, Fin.ext ?_⟩
    change d+(p.val-d) = p.val
    omega

end FlatWalshKernel

end NearSquareRoot
end Computability
end OAI
