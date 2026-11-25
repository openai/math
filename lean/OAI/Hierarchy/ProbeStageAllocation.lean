import OAI.Hierarchy.ProbeStagePorts
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI
/-! # Greedy color and stable position allocation in permutation blocks -/

namespace Hierarchy.ProbeStage

open Finset
open scoped BigOperators

namespace Greedy

variable {n B : ℕ} {L H : Type*} [DecidableEq L] [DecidableEq H]

def before (n k : ℕ) : Finset (Fin n) := univ.filter fun i => i.val < k

def load {E : Type*} [DecidableEq E] (key : Fin n → E) (seen : Finset (Fin n))
    (color : Fin n → Fin B) (x : E) (c : Fin B) : ℕ :=
  (seen.filter fun i => key i = x ∧ color i = c).card

theorem sum_load {E : Type*} [DecidableEq E] (key : Fin n → E) (seen : Finset (Fin n))
    (color : Fin n → Fin B) (x : E) : ∑ c, load key seen color x c = (seen.filter fun i => key i = x).card := by
  have h := Finset.card_eq_sum_card_fiberwise (f := color) (s := seen.filter fun i => key i = x)
    (t := univ) (fun _ _ => Finset.mem_univ _)
  simpa only [load, Finset.filter_filter] using h.symm

def available (left : Fin n → L) (right : Fin n → H) (seen : Finset (Fin n))
    (color : Fin n → Fin B) (i : Fin n) : Finset (Fin B) := univ.filter fun c =>
  load left seen color (left i) c < quota B ∧ load right seen color (right i) c < quota B

/-- When each block contains at most `B⁹` records, two endpoints cannot together exhaust all
`B` colors at quota `4 B⁸`. -/
theorem available_nonempty (pos : 0 < B) (left : Fin n → L) (right : Fin n → H)
    (hl : ∀ x, (univ.filter fun i => left i = x).card ≤ blockSize B)
    (hr : ∀ x, (univ.filter fun i => right i = x).card ≤ blockSize B)
    (seen : Finset (Fin n)) (color : Fin n → Fin B) (i : Fin n) :
    (available left right seen color i).Nonempty := by
  by_contra he
  have h (c : Fin B) : quota B ≤ load left seen color (left i) c + load right seen color (right i) c := by
    have h' : c ∉ available left right seen color i := fun hc => he ⟨c,hc⟩
    simp [available] at h'
    omega
  have hs := Finset.sum_le_sum (s := (univ : Finset (Fin B))) (fun c _ => h c)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Finset.sum_add_distrib,sum_load] at hs
  have hL : (seen.filter fun j => left j=left i).card ≤ blockSize B :=
    (card_le_card (filter_subset_filter _ (subset_univ seen))).trans (hl (left i))
  have hR : (seen.filter fun j => right j=right i).card ≤ blockSize B :=
    (card_le_card (filter_subset_filter _ (subset_univ seen))).trans (hr (right i))
  have heq : B * quota B = 4 * blockSize B := by unfold quota blockSize; ring
  have hs' : B * quota B ≤ (seen.filter fun j => left j=left i).card + (seen.filter fun j => right j=right i).card := by simpa using hs
  rw [heq] at hs'
  have hp : 0 < blockSize B := pow_pos pos _
  omega

def first (pos : 0 < B) (S : Finset (Fin B)) : Fin B :=
  if h : S.Nonempty then S.min' h else ⟨0,pos⟩

theorem first_mem (pos : 0 < B) {S : Finset (Fin B)} (h : S.Nonempty) : first pos S ∈ S := by
  rw [first,dite_eq_left h]; exact Finset.min'_mem _ _

/-- Scan the records in numerical order using the specified deterministic color search. -/
def colors (pos : 0<B) (pick : Fin n → Finset (Fin B) → Fin B) (left : Fin n → L) (right : Fin n → H) : ℕ → Fin n → Fin B
  | 0 => fun _ => ⟨0,pos⟩
  | k+1 =>
    let prev := colors pos pick left right k
    if hk : k<n then
      let i : Fin n := ⟨k,hk⟩
      Function.update prev i (pick i (available left right (before n k) prev i))
    else prev

private theorem before_succ {k : ℕ} (hk : k<n) : before n (k+1) = insert (⟨k,hk⟩ : Fin n) (before n k) := by
  ext j
  simp only [before,mem_filter,mem_univ,true_and,mem_insert,Fin.ext_iff]
  omega

private theorem load_update {E : Type*} [DecidableEq E] (key : Fin n → E) {seen : Finset (Fin n)}
    (color : Fin n → Fin B) (i : Fin n) (hi : i ∉ seen) (chosen : Fin B) (x : E) (c : Fin B) :
    load key (insert i seen) (Function.update color i chosen) x c = load key seen color x c +
      (if key i=x ∧ chosen=c then 1 else 0) := by
  have older : seen.filter (fun j => key j=x ∧ Function.update color i chosen j=c) =
      seen.filter (fun j => key j=x ∧ color j=c) := by
    ext j
    by_cases hj : j ∈ seen
    · have hji : j ≠ i := fun eq => hi (eq ▸ hj)
      simp [hj,Function.update_of_ne hji]
    · simp [hj]
  unfold load
  rw [filter_insert]
  simp only [Function.update_self,older]
  split <;> simp [*]

private theorem load_preserved {E : Type*} [DecidableEq E] (key : Fin n → E) {seen : Finset (Fin n)}
    (color : Fin n → Fin B) (i : Fin n) (hi : i ∉ seen) (chosen : Fin B)
    (cap : ∀ x c, load key seen color x c ≤ quota B) (good : load key seen color (key i) chosen < quota B) :
    ∀ x c, load key (insert i seen) (Function.update color i chosen) x c ≤ quota B := by
  intro x c
  rw [load_update key color i hi chosen]
  split_ifs with h
  · obtain ⟨rfl,rfl⟩ := h; omega
  · simpa using cap x c

theorem colors_cap (pos : 0<B) (pick : Fin n → Finset (Fin B) → Fin B)
    (hpick : ∀ i S, S.Nonempty → pick i S ∈ S) (left : Fin n → L) (right : Fin n → H)
    (hl : ∀ x, (univ.filter fun i => left i=x).card ≤ blockSize B)
    (hr : ∀ x, (univ.filter fun i => right i=x).card ≤ blockSize B)
    (k : ℕ) (hk : k ≤ n) :
    (∀ x c, load left (before n k) (colors pos pick left right k) x c ≤ quota B) ∧
    (∀ x c, load right (before n k) (colors pos pick left right k) x c ≤ quota B) := by
  induction k with
  | zero => simp [load,before]
  | succ k ih =>
    have hk' : k<n := by omega
    let i : Fin n := ⟨k,hk'⟩
    let prev := colors pos pick left right k
    let chosen := pick i (available left right (before n k) prev i)
    have hi : i ∉ before n k := by simp [i,before]
    have hgood : chosen ∈ available left right (before n k) prev i :=
      hpick i _ (available_nonempty pos left right hl hr _ _ _)
    obtain ⟨hcL,hcR⟩ := (Finset.mem_filter.mp hgood).2
    obtain ⟨hprevL,hprevR⟩ := ih hk'.le
    simp only [colors,dite_eq_left hk',before_succ hk']
    exact ⟨load_preserved left prev i hi chosen hprevL hcL,load_preserved right prev i hi chosen hprevR hcR⟩

/-- The stable rank among records in one fiber. -/
def rank {E : Type*} [DecidableEq E] (key : Fin n → E) (i : Fin n) : ℕ :=
  ((before n i.val).filter fun j => key j = key i).card

private theorem rank_lt {E : Type*} [DecidableEq E] (key : Fin n → E) (i : Fin n) :
    rank key i < (univ.filter fun j => key j=key i).card := by
  apply card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨filter_subset_filter _ (subset_univ _),?_⟩
  intro he
  have hh : i ∈ (before n i.val).filter (fun j => key j=key i) := he.symm ▸ (by simp)
  simp [before] at hh

private theorem rank_strict {E : Type*} [DecidableEq E] (key : Fin n → E) (i j : Fin n)
    (hk : key i = key j) (hlt : i<j) : rank key i < rank key j := by
  unfold rank
  rw [hk]
  apply card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · apply filter_subset_filter
    intro x hx
    simp only [before,mem_filter,mem_univ,true_and] at hx ⊢
    exact lt_trans hx hlt
  · intro eq
    have hi : i ∈ (before n j.val).filter (fun t => key t=key j) := by simp [before,hk,hlt]
    rw [← eq] at hi
    simp [before] at hi

private theorem ranks_injective {E : Type*} [DecidableEq E] (key : Fin n → E) :
    Function.Injective fun i => (key i, rank key i) := by
  intro i j hij
  obtain ⟨hk,hr⟩ := Prod.mk.inj hij
  rcases lt_trichotomy i j with h|h|h
  · exact False.elim ((rank_strict key i j hk h).ne hr)
  · exact h
  · exact False.elim ((rank_strict key j i hk.symm h).ne hr.symm)

private theorem keycap (c : Fin n → Fin B) {E : Type*} [DecidableEq E] (key : Fin n → E)
    (het : ∀ x b, load key univ c x b ≤ quota B) (i : Fin n) :
    rank (fun j => (key j,c j)) i < quota B := by
  apply (rank_lt _ i).trans_le
  simpa only [Prod.mk.injEq, load] using het (key i) (c i)

/-- A bounded assignment with stable entry and exit ranks, based on the fixed greedy scan. -/
def allocationWith (pos : 0<B) (pick : Fin n → Finset (Fin B) → Fin B)
    (hpick : ∀ i S, S.Nonempty → pick i S ∈ S) (left : Fin n → L) (right : Fin n → H)
    (hl : ∀ x, (univ.filter fun i => left i=x).card ≤ blockSize B)
    (hr : ∀ x, (univ.filter fun i => right i=x).card ≤ blockSize B) : Allocation B left right := by
  let c := colors pos pick left right n
  have done : before n n = univ := by ext j; simp [before]
  have hc := colors_cap pos pick hpick left right hl hr n le_rfl
  rw [done] at hc
  let lr := fun i => (⟨_,keycap c left hc.1 i⟩ : Fin (quota B))
  let rr := fun i => (⟨_,keycap c right hc.2 i⟩ : Fin (quota B))
  refine ⟨c,lr,rr,?_,?_⟩
  · intro i j eq
    obtain ⟨h,cb⟩ := Prod.mk.inj eq
    obtain ⟨hh,hb⟩ := Prod.mk.inj cb
    exact ranks_injective (fun t => (left t,c t)) (Prod.ext (Prod.ext h hh) (congrArg Fin.val hb))
  · intro i j eq
    obtain ⟨h,cb⟩ := Prod.mk.inj eq
    obtain ⟨hh,hb⟩ := Prod.mk.inj cb
    exact ranks_injective (fun t => (right t,c t)) (Prod.ext (Prod.ext h hh) (congrArg Fin.val hb))

end Greedy

/-- Run a validated deterministic color search in each pair of endpoint masks. -/
noncomputable def allocateWith {n m B : ℕ} {G : Type*} (p : Tiles (Fin n) G m) (pos : 0<B)
    (pick : Fin n → Finset (Fin B) → Fin B) (hpick : ∀ i S, S.Nonempty → pick i S ∈ S) :
    Allocation B (leftBlock p pos) (rightBlock p pos) := by
  classical
  apply Greedy.allocationWith pos pick hpick
  · intro x
    have h := Fintype.card_le_of_injective _ (leftBlockFiber p pos x).injective
    simpa only [Fintype.card_subtype, Fintype.card_fin] using h
  · intro x
    have h := Fintype.card_le_of_injective _ (rightBlockFiber p pos x).injective
    simpa only [Fintype.card_subtype, Fintype.card_fin] using h

/-- Ordinary greedy coloring, using the first free global color. -/
noncomputable def allocate {n m B : ℕ} {G : Type*} (p : Tiles (Fin n) G m) (pos : 0<B) :
    Allocation B (leftBlock p pos) (rightBlock p pos) :=
  allocateWith p pos (fun _ => Greedy.first pos) (fun _ _ => Greedy.first_mem pos)

end Hierarchy.ProbeStage

end OAI
