import OAI.LinearAlgebra.MatrixExponent.Diagram.Permute
import OAI.LinearAlgebra.MatrixExponent.CompareExchange
import OAI.LinearAlgebra.MatrixExponent.Network.Dense
import Mathlib.Logic.Equiv.Fin.Basic

section
/-!
# Deterministic networks on finite sets of named bits

The names prescribe a layout only. Changing that layout is a free
permutation of the exterior wires.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Install

def Depends {I J : Type} (f : (I → Bool) → (J → Bool)) (R : ℕ) : Prop :=
  ∀ i : J, ∃ S : Finset I, S.card ≤ R ∧ ∀ x y, (∀ j ∈ S, x j = y j) → f x i = f y i

def BNet (F : Type) [Field F] {I J : Type} (f : (I → Bool) → (J → Bool)) (m : ℕ) : Prop :=
  ∀ (a b : Wire) (i : I ≃ slots a) (j : J ≃ slots b),
    DNet F a b (fun x => (bits b).symm (f (bits a x ∘ i) ∘ j.symm)) m

namespace BNet

variable {F I J K : Type} [Field F] {f : (I → Bool) → (J → Bool)} {m n : ℕ}

theorem mono (h : BNet F f m) (le : m ≤ n) : BNet F f n :=
  fun a b i j => (h a b i j).mono le

private noncomputable def names (I : Type) [Fintype I] : I ≃ slots (word (Fintype.card I)) :=
  Fintype.equivOfCardEq (by simp)

theorem comp [Fintype J] {g : (J → Bool) → (K → Bool)} (h : BNet F f m) (k : BNet F g n) :
    BNet F (g ∘ f) (m + n) := by
  intro a c i l
  let b := word (Fintype.card J)
  let j : J ≃ slots b := names J
  simpa only [Function.comp_def, Equiv.apply_symm_apply, Equiv.symm_apply_apply] using
    (h a b i j).comp (k b c j l)

theorem of_layout {a b : Wire} (i : I ≃ slots a) (j : J ≃ slots b)
    (h : DNet F a b (fun x => (bits b).symm (f (bits a x ∘ i) ∘ j.symm)) m) :
    BNet F f m := by
  intro c d k l
  have hp := (h.pre (rewire_reindex (i.symm.trans k))).post (rewire_reindex (l.symm.trans j))
  simpa [reindex, Function.comp_def] using hp

theorem parallel [Fintype I] [Fintype J] [Fintype K] {L : Type} [Fintype L]
    {g : (K → Bool) → (L → Bool)} (h : BNet F f m) (k : BNet F g n) :
    BNet F (fun x => Sum.elim (f (x ∘ Sum.inl)) (g (x ∘ Sum.inr))) (m + n) := by
  let a := word (Fintype.card I)
  let b := word (Fintype.card J)
  let c := word (Fintype.card K)
  let d := word (Fintype.card L)
  apply of_layout (a := .pair a c) (b := .pair b d)
    ((names I).sumCongr (names K)) ((names J).sumCongr (names L))
  exact (h a b (names I) (names J)).par (k c d (names K) (names L))

theorem id (F I : Type) [Field F] [Fintype I] :
    BNet F (_root_.id : (I → Bool) → _) (Fintype.card I) := by
  intro a b i j
  rw [Fintype.card_congr i, card_slots]
  exact (DNet.id F a).post (rewire_reindex (j.symm.trans i))

end BNet
end OAI.LinearAlgebra.MatrixExponent.Install
end

section
/-!
# Bounded dependence gives a linear circuit

First copy and permute the needed wires. Each output bit can then be
computed independently on its own bounded input bundle.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Install

variable {F : Type} [Field F] {a b c : Wire}

def project (f : slots b → slots a) (x : Val a) : Val b :=
  (bits b).symm (bits a x ∘ f)

@[simp] theorem bits_project (f : slots b → slots a) (x : Val a) (i : slots b) :
    bits b (project f x) i = bits a x (f i) :=
  congrFun ((bits b).apply_symm_apply _) i

private theorem split {U V : Type} (b : Wire) (f : slots b → U ⊕ V) :
    ∃ (l r : Wire) (e : slots b ≃ slots l ⊕ slots r)
      (u : slots l → U) (v : slots r → V), ∀ j, f j = Sum.map u v (e j) := by
  induction b with
  | unit => exact ⟨.unit, .unit, (Equiv.sumEmpty Empty Empty).symm,
      Empty.elim, Empty.elim, fun j => j.elim⟩
  | bit =>
    rcases h : f () with x | y
    · exact ⟨.bit, .unit, (Equiv.sumEmpty Unit Empty).symm,
        fun _ => x, Empty.elim, fun _ => h⟩
    · exact ⟨.unit, .bit, (Equiv.emptySum Empty Unit).symm,
        Empty.elim, fun _ => y, fun _ => h⟩
  | pair a b ha hb =>
    obtain ⟨l, r, e, u, v, h⟩ := ha (f ∘ Sum.inl)
    obtain ⟨l', r', e', u', v', h'⟩ := hb (f ∘ Sum.inr)
    refine ⟨.pair l l', .pair r r', (e.sumCongr e').trans (Equiv.sumSumSumComm _ _ _ _),
      Sum.elim u u', Sum.elim v v', ?_⟩
    rintro (j | j)
    · specialize h j
      cases he : e j <;> simp_all
    · specialize h' j
      cases he : e' j <;> simp_all

private theorem broadcast (F : Type) [Field F] (n : ℕ) :
    DNet F .bit (word n) (fun x => (bits (word n)).symm (fun _ => x)) (1 + 2 * n) := by
  induction n with
  | zero => exact DNet.discard F .bit
  | succ n ih =>
    exact ((DNet.id F .bit).pair ih).mono (by simp [wd]; omega)

theorem project_net (F : Type) [Field F] (f : slots b → slots a) :
    DNet F a b (project f) (wd a + 2 * wd b) := by
  induction a generalizing b with
  | unit =>
    let e : slots b ≃ slots .unit :=
      ⟨f, Empty.elim, fun i => (f i).elim, fun i => i.elim⟩
    exact ((DNet.id F .unit).post (rewire_reindex e)).mono (Nat.zero_le _)
  | bit =>
    let e : slots b ≃ slots (word (wd b)) := Fintype.equivOfCardEq (by simp)
    have h := (broadcast F (wd b)).post (rewire_reindex e)
    convert h using 1 <;> try rfl
    funext x
    apply (bits b).injective
    funext j
    simp [bits_project, bits_reindex]
    rfl
  | pair a c ha hc =>
    obtain ⟨l, r, e, u, v, h⟩ := split b f
    have hp := ((ha u).par (hc v)).post (rewire_reindex (a := .pair l r) e)
    have hw : wd b = wd l + wd r := by simpa using Fintype.card_congr e
    convert hp.mono (n := wd (.pair a c) + 2 * wd b) (by simp [wd, hw]; omega) using 1
    funext x
    apply (bits b).injective
    funext j
    simp only [bits_project, bits_reindex, h j]
    cases e j with
    | inl i => exact (bits_project u x.1 i).symm
    | inr i => exact (bits_project v x.2 i).symm

private theorem assemble {I : Type} (F : Type) [Field F] (R : ℕ)
    (b : Wire) (f : (I → Bool) → slots b → Bool) (h : Depends f R) :
    ∃ (u : Wire) (p : slots u → I) (g : Val u → Val b),
      wd u ≤ R * wd b ∧ DNet F u b g (8 * 2 ^ (R + 1) * wd b) ∧
      ∀ x, bits b (g ((bits u).symm (x ∘ p))) = f x := by
  classical
  induction b with
  | unit =>
    refine ⟨.unit, Empty.elim, id, ?_, ?_, fun x => funext fun j => j.elim⟩
    · exact Nat.zero_le _
    · exact (DNet.id F .unit).mono (Nat.zero_le _)
  | bit =>
    obtain ⟨S, hs, he⟩ := h ()
    let u := word S.card
    let e : slots u ≃ S := @Fintype.equivOfCardEq (slots u) S (slotsFintype u) _
      ((card_slots u).trans ((wd_word _).trans (Fintype.card_coe S).symm))
    let g (v : Val u) := f (fun i => if hi : i ∈ S then bits u v (e.symm ⟨i, hi⟩) else false) ()
    refine ⟨u, fun j => ↑(e j), g, by simpa [wd, u], ?_, ?_⟩
    · obtain ⟨v, hv, hm⟩ := Net.dense u .bit (fun x y => if g x = y then (1 : F) else 0)
      refine ⟨v, hm.trans ?_, hv⟩
      simp only [u, wd_word, wd, mul_one]
      gcongr
    · intro x
      funext j
      apply he
      intro i hi
      simp [hi]
  | pair b c hb hc =>
    obtain ⟨u, p, g, hu, hg, he⟩ := hb (fun x i => f x (.inl i)) (fun i => h (.inl i))
    obtain ⟨v, r, l, hv, hl, hd⟩ := hc (fun x i => f x (.inr i)) (fun i => h (.inr i))
    refine ⟨.pair u v, Sum.elim p r, _, ?_, (hg.par hl).mono ?_, ?_⟩
    · simpa only [wd, mul_add] using Nat.add_le_add hu hv
    · simp [wd, mul_add]
    · intro x
      funext j
      rcases j with j | j
      · exact congrFun (he x) j
      · exact congrFun (hd x) j

def localCost (R : ℕ) := 2 * R + 8 * 2 ^ (R + 1)

theorem Depends.bnet {I J : Type} [Fintype I] [Fintype J] {R : ℕ}
    {f : (I → Bool) → J → Bool} (h : Depends f R) (F : Type) [Field F] :
    BNet F f (Fintype.card I + localCost R * Fintype.card J) := by
  intro a b i j
  obtain ⟨u, p, g, hu, hg, he⟩ := assemble F R b (fun x => f x ∘ j.symm) (fun z => h (j.symm z))
  have hn := (project_net F (i ∘ p)).comp hg
  have hcost : wd a + 2 * wd u + 8 * 2 ^ (R + 1) * wd b ≤
      Fintype.card I + localCost R * Fintype.card J := by
    rw [Fintype.card_congr i, Fintype.card_congr j, card_slots, card_slots,
      localCost, add_mul, mul_assoc 2 R]
    omega
  convert hn.mono hcost using 1
  funext x
  apply (bits b).injective
  rw [Equiv.apply_symm_apply]
  exact (he (bits a x ∘ i)).symm

end OAI.LinearAlgebra.MatrixExponent.Install
end

section
/-! # Parallel computation on named bundles -/

namespace OAI.LinearAlgebra.MatrixExponent.Install.BNet

variable {F I J K L : Type} [Field F] {f : (I → Bool) → (J → Bool)} {m n : ℕ}

theorem rename (h : BNet F f m) (e : I ≃ K) (d : J ≃ L) :
    BNet F (fun x => f (x ∘ e) ∘ d.symm) m := fun a b i j => h a b (e.trans i) (d.trans j)

theorem pull [Fintype I] [Fintype K] (h : BNet F f m) (e : I → K) :
    BNet F (fun x => f (x ∘ e)) (Fintype.card K + 2 * Fintype.card I + m) := by
  have hp : BNet F (fun x => x ∘ e) (Fintype.card K + 2 * Fintype.card I) := by
    intro a b i j
    rw [Fintype.card_congr i, Fintype.card_congr j, card_slots, card_slots]
    exact project_net F (i ∘ e ∘ j.symm)
  exact hp.comp h

theorem pair [Fintype I] [Fintype J] [Fintype K] {g : (I → Bool) → (K → Bool)}
    (h : BNet F f m) (k : BNet F g n) :
    BNet F (fun x => Sum.elim (f x) (g x)) (5 * Fintype.card I + m + n) := by
  have t := (h.parallel k).pull (Sum.elim _root_.id _root_.id)
  exact t.mono (by rw [Fintype.card_sum]; omega)

theorem family [Fintype I] [Fintype J] (t : ℕ)
    (f : Fin (2 ^ t) → (I → Bool) → (J → Bool)) (h : ∀ i, BNet F (f i) m) :
    BNet F (fun (x : Fin (2 ^ t) × I → Bool) (p : Fin (2 ^ t) × J) =>
      f p.1 (fun j => x (p.1, j)) p.2) (2 ^ t * m) := by
  induction t with
  | zero =>
    have k := (h 0).rename (Equiv.uniqueProd I (Fin 1)).symm (Equiv.uniqueProd J (Fin 1)).symm
    convert k using 1 <;> try rfl
    · funext x ⟨i, j⟩
      rw [Fin.eq_zero i]
      rfl
    · simp
  | succ t ih =>
    generalize he : 2 ^ (t + 1) = r at *
    rw [pow_succ, mul_two] at he
    subst r
    let e (M : Type) := (Equiv.sumProdDistrib (Fin (2 ^ t)) (Fin (2 ^ t)) M).symm.trans
      (finSumFinEquiv.prodCongr (.refl M))
    have l := ih (fun i => f (Fin.castAdd _ i)) fun i => h _
    have r := ih (fun i => f (Fin.natAdd _ i)) fun i => h _
    rw [add_mul]
    convert (l.parallel r).rename (e I) (e J) using 1
    funext x y
    obtain ⟨⟨i, j⟩ | ⟨i, j⟩, rfl⟩ := (e J).surjective y <;>
      simp only [Function.comp_apply, Equiv.symm_apply_apply] <;> rfl

theorem share [Fintype I] [Fintype J] (t : ℕ)
    (f : Fin (2 ^ t) → (I → Bool) → (J → Bool)) (h : ∀ i, BNet F (f i) m) :
    BNet F (fun x (p : Fin (2 ^ t) × J) => f p.1 x p.2)
      (2 ^ t * (3 * Fintype.card I + m)) := by
  apply ((family t f h).pull Prod.snd).mono
  simp only [Fintype.card_prod, Fintype.card_fin]
  nlinarith [Nat.mul_le_mul_right (Fintype.card I) (Nat.one_le_pow t 2 (by decide))]

private theorem any_word (F : Type) [Field F] (n : ℕ) :
    DNet F (word n) .bit (fun x => decide (∃ j, bits (word n) x j = true)) (2 * n + 1) := by
  induction n with
  | zero => exact .table _ _ _ _ (by decide)
  | succ n ih =>
    have gate := DNet.table F (.pair .bit .bit) .bit (fun x => x.1 || x.2) (by decide)
    convert ((DNet.id F .bit).par ih).comp gate using 1 <;> try rfl
    · funext x
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, Bool.or_eq_true]
      constructor
      · rintro ⟨j | j, hj⟩
        · exact .inl hj
        · exact .inr ⟨j, hj⟩
      · rintro (hj | ⟨j, hj⟩)
        · exact ⟨.inl (), hj⟩
        · exact ⟨.inr j, hj⟩
    · simp [wd]; omega

theorem any (F I : Type) [Field F] [Fintype I] :
    BNet F (fun (x : I → Bool) (_ : Unit) => decide (∃ i, x i = true)) (2 * Fintype.card I + 1) := by
  let n := Fintype.card I
  let i : I ≃ slots (word (Fintype.card I)) := Fintype.equivOfCardEq (by simp)
  apply of_layout (a := word n) (b := .bit) i (.refl Unit)
  convert any_word F n using 1
  funext x
  change decide (∃ j, bits (word n) x (i j) = true) = _
  simp only [decide_eq_decide]
  exact ⟨fun ⟨j, hj⟩ => ⟨_, hj⟩, fun ⟨j, hj⟩ => ⟨i.symm j, by simpa⟩⟩

end OAI.LinearAlgebra.MatrixExponent.Install.BNet
end

section
/-!
# Scalar weights on named exterior bits

Deterministic preprocessing selects exactly one assignment in a contraction.
Disjoint copies of a weight multiply, with no extra vertices.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Install

def Weight (F : Type) [Field F] {I : Type} (f : (I → Bool) → F) (m : ℕ) : Prop :=
  ∀ (a : Wire) (i : I ≃ slots a), ∃ v ≤ m, Net F a .unit (fun x _ => f (bits a x ∘ i)) v

variable {F I J : Type} [Field F] {m n : ℕ}

theorem BNet.weight [Fintype J] {f : (I → Bool) → J → Bool} {g : (J → Bool) → F}
    (h : BNet F f m) (k : Weight F g n) : Weight F (g ∘ f) (m + n) := by
  intro a i
  let b := word (Fintype.card J)
  let j : J ≃ slots (word (Fintype.card J)) := Fintype.equivOfCardEq (by simp)
  obtain ⟨v, hv, h⟩ := h a b i j
  obtain ⟨w, hw, k⟩ := k b j
  refine ⟨v + w, Nat.add_le_add hv hw, ?_⟩
  simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Function.comp_def, Equiv.apply_symm_apply, Equiv.symm_apply_apply] using h.comp k

namespace Weight

variable {f : (I → Bool) → F}

theorem mono (h : Weight F f m) (le : m ≤ n) : Weight F f n := by
  intro a i
  obtain ⟨v, hv, h⟩ := h a i
  exact ⟨v, hv.trans le, h⟩

theorem of_layout {a : Wire} (i : I ≃ slots a)
    (h : ∃ v ≤ m, Net F a .unit (fun x _ => f (bits a x ∘ i)) v) : Weight F f m := by
  intro b j
  obtain ⟨v, hv, h⟩ := h
  refine ⟨v, hv, ?_⟩
  simpa [Function.comp_def] using h.pre (rewire_reindex (i.symm.trans j))

theorem rename (h : Weight F f m) (e : I ≃ J) : Weight F (fun x => f (x ∘ e)) m :=
  fun a i => h a (e.trans i)

private theorem twice [Fintype I] (h : Weight F f m) :
    Weight F (fun x => f (x ∘ Sum.inl) * f (x ∘ Sum.inr)) (m + m) := by
  let a := word (Fintype.card I)
  let i : I ≃ slots (word (Fintype.card I)) := Fintype.equivOfCardEq (by simp)
  obtain ⟨v, hv, h⟩ := h a i
  apply of_layout (a := .pair a a) (i.sumCongr i)
  exact ⟨v + v, Nat.add_le_add hv hv, (h.par h).post (.unit' _)⟩

theorem prod [Fintype I] (h : Weight F f m) (w : ℕ) :
    Weight F (fun x : Fin (2 ^ w) × I → Bool => ∏ i : Fin (2 ^ w), f (fun j => x (i, j)))
      (2 ^ w * m) := by
  induction w with
  | zero =>
    rw [pow_zero, one_mul]
    simpa [Function.comp_def] using h.rename (Equiv.uniqueProd I (Fin 1)).symm
  | succ w ih =>
    rw [pow_succ, mul_two, add_mul]
    let e := (Equiv.sumProdDistrib (Fin (2 ^ w)) (Fin (2 ^ w)) I).symm.trans
      (finSumFinEquiv.prodCongr (.refl I))
    convert ih.twice.rename e using 1
    funext x
    rw [Fin.prod_univ_add]
    rfl

end Weight
end OAI.LinearAlgebra.MatrixExponent.Install
end
