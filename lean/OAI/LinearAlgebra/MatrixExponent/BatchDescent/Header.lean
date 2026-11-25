import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Plan
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Transform

/-!
# Splitting posted diagrams into ordered pieces

A positive internal span is one entire unit. Exterior spans may
contain several units. Their ordering is supplied independently.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent

namespace BatchDescent
open Assembly

variable {F : Type} {S : Scheme F} {r : S.format.obj} {z : ℕ}

def unitSpan (t : units S r z) : S.Span := ((t.1, t.2.1, t.2.2.1.1), t.2.2.1.2)

abbrev outer (S : Scheme F) (r : S.format.obj) (z : ℕ) :=
  {t : units S r z // S.peer r (unitSpan t) = none}

theorem unit_ext {a b : units S r z} (h : unitSpan a = unitSpan b)
    (hk : a.2.2.2.val = b.2.2.2.val) : a = b := by
  obtain ⟨i, j, ⟨k, s⟩, t⟩ := a
  obtain ⟨i', j', ⟨k', s'⟩, t'⟩ := b
  simp only [unitSpan, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
  have he : t = t' := Fin.ext hk
  rw [he]

end BatchDescent

namespace Assembly.Scheme.Posting
open BatchDescent BatchDescent.PackRows Packing Coloring
open scoped Classical

variable {F T : Type} [Field F] {x y : Wire} {L : Fringe x y T} {h z : ℕ}
    {S : Scheme F} {r : S.format.obj} {G : HostNet F L h z} (p : S.Posting r G) (hz : 0 < z)

def unitOf (i : G.E) (b : Bool) : units S r z :=
  ⟨p.host (side G i b), p.block (G.ix i), (0, p.stub i b), ⟨0, by
    change 0 < S.width r (p.span i b) / z
    rw [p.length, Nat.div_self hz]
    decide⟩⟩

@[simp] theorem unitSpan_unitOf (i : G.E) (b : Bool) :
    unitSpan (p.unitOf hz i b) = p.span i b := rfl

include hz in
theorem span_peer (i : G.E) (b : Bool) :
    S.peer r (p.span i b) = some (p.span i (!b)) := by
  rw [peer, p.link]
  simp only [Option.map_some, span, spanAt, p.neighbor hz]

private theorem unitOf_eq {u : units S r z} (i : G.E) (b : Bool) (hs : unitSpan u = p.span i b) :
    u = p.unitOf hz i b := by
  refine unit_ext hs ?_
  have hl : u.2.2.2.val < S.width r (unitSpan u) / z := u.2.2.2.isLt
  rw [hs, p.length, Nat.div_self hz] at hl
  exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hl)

theorem unit_cases (u : units S r z) :
    S.peer r (unitSpan u) = none ∨ ∃ i b, u = p.unitOf hz i b := by
  cases hs : S.peer r (unitSpan u) with
  | none => exact .inl rfl
  | some t =>
    have hl : 0 < S.width r (unitSpan u) :=
      (show 0 < S.width r (unitSpan u) / z from u.2.2.2.pos).trans_le (Nat.div_le_self _ _)
    obtain ⟨⟨i, b⟩, he⟩ := p.found _ hl (by simp [hs])
    exact .inr ⟨i, b, p.unitOf_eq hz i b he.symm⟩

theorem joined (uniform : ∀ i j, Parts.Uniform (BatchDescent.pattern S r i j) z)
    {s t : units S r z} {i j : Fin z}
    (he : S.Joins r (BatchDescent.join S r z uniform (s, i)) (BatchDescent.join S r z uniform (t, j))) :
    i = j ∧ ∃ e b, s = p.unitOf hz e b ∧ t = p.unitOf hz e (!b) := by
  have hs : S.peer r (unitSpan s) = some (unitSpan t) := he.1
  rcases p.unit_cases hz s with hn | ⟨e, b, rfl⟩
  · rw [hn] at hs; cases hs
  rw [unitSpan_unitOf, p.span_peer hz] at hs
  have ht := p.unitOf_eq hz e (!b) (Option.some.inj hs).symm
  subst t
  exact ⟨Fin.ext he.2, e, b, rfl, rfl⟩

private theorem unitOf_inj : Function.Injective (Function.uncurry (p.unitOf hz)) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ hh
  have he : p.span i b = p.span j c := congrArg unitSpan hh
  have ho := congrArg (S.direction r) he
  rw [p.dir, p.dir] at ho
  subst c
  have eq : i = j := by
    apply p.distinct hz
    cases b
    · exact he
    · have h' := congrArg (S.peer r) he
      rw [p.span_peer hz, p.span_peer hz] at h'
      exact Option.some.inj h'
  rw [eq]

def unitLayout : (G.E × Bool) ⊕ outer S r z ≃ units S r z :=
  Equiv.ofBijective (Sum.elim (Function.uncurry (p.unitOf hz)) Subtype.val) (by
    have ne (i : G.E × Bool) (j : outer S r z) : p.unitOf hz i.1 i.2 ≠ j.val := by
      intro eq
      have h := j.property
      rw [← eq, unitSpan_unitOf, p.span_peer hz] at h
      cases h
    constructor
    · rintro (i|i) (j|j) he
      · exact congrArg Sum.inl (p.unitOf_inj hz he)
      · exact (ne i j he).elim
      · exact (ne j i he.symm).elim
      · exact congrArg Sum.inr (Subtype.ext he)
    · intro i
      rcases p.unit_cases hz i with he | ⟨e, b, rfl⟩
      · exact ⟨.inr ⟨i, he⟩, rfl⟩
      · exact ⟨.inl (e, b), rfl⟩)

include p in
theorem all_uniform (hm : ∀ a, S.peer r a = none → z ∣ S.width r a) (i j) :
    Parts.Uniform (BatchDescent.pattern S r i j) z := by
  intro k t
  let a : S.Span := ((i, j, k), t)
  change z ∣ S.width r a
  by_cases he : S.width r a = 0
  · rw [he]; exact dvd_zero _
  cases hp : S.peer r a with
  | none => exact hm _ hp
  | some v =>
    obtain ⟨⟨e, b⟩, h⟩ := p.found a (Nat.pos_of_ne_zero he) (by simp [hp])
    rw [← h, p.length]

private theorem localize {I J : Type} {U V : I → J → Type}
    (f : (Σ i, Σ j, U i j) ≃ Σ i, Σ j, V i j)
    (hf : ∀ x, (f x).1 = x.1 ∧ (f x).2.1 = x.2.1) (i : I) (j : J) :
    ∃ e : U i j ≃ V i j, ∀ x, f ⟨i, j, x⟩ = ⟨i, j, e x⟩ := by
  have hit (x : U i j) : ∃ y : V i j, f ⟨i, j, x⟩ = ⟨i, j, y⟩ := by
    have he := hf ⟨i, j, x⟩
    generalize f ⟨i, j, x⟩ = v at *
    obtain ⟨a, b, t⟩ := v
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨t, rfl⟩
  choose g hg using hit
  have bij : Function.Bijective g := by
    constructor
    · intro a b he
      have ht : f ⟨i, j, a⟩ = f ⟨i, j, b⟩ := by rw [hg, hg, he]
      simpa using f.injective ht
    · intro y
      obtain ⟨⟨a, b, x⟩, he⟩ := f.surjective ⟨i, j, y⟩
      have ht := hf ⟨a, b, x⟩
      rw [he] at ht
      obtain ⟨rfl, rfl⟩ := ht
      exact ⟨x, by simpa [hg] using he⟩
  exact ⟨Equiv.ofBijective g bij, hg⟩

variable {v q d : ℕ} {G' : HostNet F L h (bundleSize v q)}
  (p : S.Posting r G') (hz : 0 < bundleSize v q)
  (hm : ∀ a, S.peer r a = none → bundleSize v q ∣ S.width r a)
  {l : Inventory (2 ^ S.m) (2 ^ S.h) d}
  (ex : outer S r (bundleSize v q) ≃ Endpoints l)
  (hx : ∀ j, (ex j).1 = j.val.1 ∧ (ex j).2.1 = j.val.2.1)

include hm hx in
private theorem exists_pieces :
    ∃ b : Pieces S r (append (p.channels hz).inventory l) v q,
      (∀ i t, b.equiv (p.unitOf hz i t) = extendL _ l ((p.channels hz).point (i, t))) ∧
      ∀ j, b.equiv j.val = extendR (p.channels hz).inventory l (ex j) := by
  let A := p.channels hz
  let e := p.unitLayout hz
  let f := e.symm.trans ((A.point.sumCongr ex).trans (combined A.inventory l))
  have inner (i : G'.E × Bool) : f (p.unitOf hz i.1 i.2) = extendL A.inventory l (A.point i) := by
    change f (e (.inl i)) = _
    simp only [f, Equiv.trans_apply, Equiv.symm_apply_apply]
    rfl
  have out (i : outer S r (bundleSize v q)) : f i.val = extendR A.inventory l (ex i) := by
    change f (e (.inr i)) = _
    simp only [f, Equiv.trans_apply, Equiv.symm_apply_apply]
    rfl
  have hf (i) : (f i).1 = i.1 ∧ (f i).2.1 = i.2.1 := by
    rcases p.unit_cases hz i with he | ⟨j, b, rfl⟩
    · rw [out ⟨i, he⟩]
      exact hx _
    · rw [inner (j, b)]
      exact ⟨rfl, rfl⟩
  choose g hg using localize f hf
  let b : Pieces S r (append A.inventory l) v q := ⟨p.all_uniform hm, g⟩
  have he (i) : b.equiv i = f i := by obtain ⟨s, t, i⟩ := i; exact (hg s t i).symm
  exact ⟨b, fun i t => (he _).trans (inner (i, t)), fun j => (he _).trans (out j)⟩

def pieces : Pieces S r (append (p.channels hz).inventory l) v q :=
  (p.exists_pieces hz hm ex hx).choose

theorem pieces_inner (i : G'.E) (b : Bool) :
    (p.pieces hz hm ex hx).equiv (p.unitOf hz i b) = extendL _ l ((p.channels hz).point (i, b)) :=
  (p.exists_pieces hz hm ex hx).choose_spec.1 i b

theorem pieces_outer (j : outer S r (bundleSize v q)) :
    (p.pieces hz hm ex hx).equiv j.val = extendR (p.channels hz).inventory l (ex j) :=
  (p.exists_pieces hz hm ex hx).choose_spec.2 j

end Assembly.Scheme.Posting
end OAI.LinearAlgebra.MatrixExponent
end

/-!
# Checking an injective scatter

A source presents its variable destination address. At each named
destination, a flag activates the opposite packet. Pairing checks
the flags as well as the transmitted payloads.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent

open Transcript Messages Install
open scoped Classical

variable {F X I J D : Type} {A j z w u : ℕ}

private theorem pairing (name : J ↪ Val (word A)) (e : I ↪ J) (r : I ⊕ J ↪ Fin (2 ^ j))
    (v : Fin (2 ^ j) → Val (row A z)) (active : J → Bool)
    (src : I → Val (word z)) (dst : J → Val (word z))
    (left : ∀ i, v (r (.inl i)) = assemble (true, false, name (e i)) (src i))
    (right : ∀ k, v (r (.inr k)) = assemble (active k, true, name k) (dst k))
    (pad : ∀ k, k ∉ Set.range r → v k = Lookup.zero _) :
    paired (List.ofFn v) ↔ (∀ k, active k = true ↔ k ∈ Set.range e) ∧ ∀ i, dst (e i) = src i := by
  constructor
  · intro h
    have mate (k) (hk : (v k).1 = true) : ∃ l, v (r l) = reverse A z (v k) := by
      have hs : reverse A z (v k) ∈ List.ofFn v :=
        h.subset (List.mem_map_of_mem (List.mem_ofFn.mpr ⟨k, rfl⟩))
      obtain ⟨l, hl⟩ := List.mem_ofFn.mp hs
      by_cases h' : l ∈ Set.range r
      · obtain ⟨i, rfl⟩ := h'
        exact ⟨i, hl⟩
      rw [pad _ h'] at hl
      have he := congrArg Prod.fst hl
      change false = (v k).1 at he
      rw [hk] at he
      contradiction
    have send (i) : active (e i) = true ∧ dst (e i) = src i := by
      obtain ⟨k, hk⟩ := mate (r (.inl i)) (by rw [left]; rfl)
      rw [left, reverse_assemble] at hk
      cases k with
      | inl l =>
        rw [left] at hk
        have h' := congrArg (header A z) hk
        simp [header_assemble, opposite] at h'
      | inr l =>
        rw [right] at hk
        have h' := congrArg (header A z) hk
        simp [header_assemble, opposite] at h'
        obtain ⟨hflag, rfl⟩ := h'
        rw [hflag] at hk
        exact ⟨hflag, assemble_injective _ hk⟩
    refine ⟨fun k => ⟨fun hk => ?_, by rintro ⟨i, rfl⟩; exact (send i).1⟩, fun i => (send i).2⟩
    obtain ⟨l, hl⟩ := mate (r (.inr k)) (by rw [right]; exact hk)
    rw [right, hk, reverse_assemble] at hl
    cases l with
    | inl i =>
      rw [left] at hl
      have h' := congrArg (header A z) hl
      simp [header_assemble, opposite] at h'
      exact ⟨i, h'⟩
    | inr i =>
      rw [right] at hl
      have h' := congrArg (header A z) hl
      simp [header_assemble, opposite] at h'
  · rintro ⟨flags, payload⟩
    let g := ((Function.Embedding.refl I).sumMap e).trans r
    let s : Equiv.Perm (I ⊕ I) := Equiv.sumComm I I
    have on (i) := (flags (e i)).mpr ⟨i, rfl⟩
    have he : reverse A z ∘ v = v ∘ s.viaEmbedding g := by
      funext k
      simp only [Function.comp_apply]
      by_cases hk : k ∈ Set.range g
      · obtain ⟨p, rfl⟩ := hk
        rw [Equiv.Perm.viaEmbedding_apply]
        cases p with
        | inl i =>
          change reverse A z (v (r (.inl i))) = v (r (.inr (e i)))
          rw [left, right, on, payload, reverse_assemble]
          rfl
        | inr i =>
          change reverse A z (v (r (.inr (e i)))) = v (r (.inl i))
          rw [left, right, on, payload, reverse_assemble]
          rfl
      rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hk]
      by_cases hp : k ∈ Set.range r
      · obtain ⟨i | l, rfl⟩ := hp
        · exact (hk ⟨.inl i, rfl⟩).elim
        · have hoff : active l = false := Bool.eq_false_iff.mpr fun h => by
            obtain ⟨i, rfl⟩ := (flags l).mp h
            exact hk ⟨.inr i, rfl⟩
          rw [right, hoff, reverse_assemble]
          rfl
      rw [pad _ hp]
      rfl
    unfold paired
    rw [List.map_ofFn, he]
    exact Equiv.Perm.ofFn_comp_perm _ _

variable [Field F] [Fintype X] [Fintype J] [Fintype D]

private def blank (used : J → X ⊕ Bool) (dst : J → D → X ⊕ Bool) (x : X → Bool) :=
  ∀ v k, Sum.elim x id (used v) ≠ true → Sum.elim x id (dst v k) = false

private theorem blank_net (used : J → X ⊕ Bool) (dst : J → D → X ⊕ Bool) :
    Weight F (fun x => if blank used dst x then 1 else 0)
      (Fintype.card X + 70 * (Fintype.card J * Fintype.card D) + 17) := by
  let bad (x : X → Bool) (p : J × D) :=
    decide (Sum.elim x id (used p.1) ≠ true ∧ Sum.elim x id (dst p.1 p.2) ≠ false)
  have h : Depends bad 2 := by
    rintro ⟨v, k⟩
    obtain ⟨S, hS, hs⟩ := tap_depends used v
    obtain ⟨T, hT, ht⟩ := tap_depends (dst v) k
    refine ⟨S ∪ T, (Finset.card_union_le S T).trans (by omega), fun x y he => ?_⟩
    have h₁ := hs x y (fun i hi => he i (Finset.mem_union_left _ hi))
    have h₂ := ht x y (fun i hi => he i (Finset.mem_union_right _ hi))
    simp only [Function.comp_apply] at h₁ h₂
    simp only [bad, h₁, h₂]
  have net := ((h.bnet F).comp (BNet.any F (J × D))).weight
    (Weight.dense F Unit (fun v => if v () then 0 else 1))
  convert net using 1
  · funext x
    have e : (∃ p, bad x p = true) ↔ ¬ blank used dst x := by
      simp [bad, blank]
    simp only [Function.comp_apply, decide_eq_true_eq, e, ite_not]
  · simp [localCost]
    omega

theorem wide_mul {G : Set (Table F)} (hu : 3 ≤ u)
    {f g : (X → Bool) → F} {m n : ℕ} (hf : WideWeight F u G f m) (hg : WideWeight F u G g n) :
    WideWeight F u G (fun x => f x * g x) (4 * Fintype.card X + m + n) := by
  intro a i
  obtain ⟨v, hv, hf⟩ := hf a i
  obtain ⟨r, hr, hg⟩ := hg a i
  obtain ⟨d, hd, dup⟩ := DWide.of_dnet (L := G) hu (DNet.dup F a)
  rw [Fintype.card_congr i, card_slots]
  refine ⟨d + (v + r), by omega, ?_⟩
  simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    using dup.comp ((hf.par hg).post (.unit' _))

/-- A fixed checker works for every injective address assignment. It
forces values outside the image to zero and determines the use flags. -/
theorem scatter (F : Type) [Field F] [Fintype I] (name : J ↪ Val (word A))
    (addr : I → slots (word A) → X ⊕ Bool) (src : I → D → X ⊕ Bool)
    (dst : J → D → X ⊕ Bool) (used : J → X ⊕ Bool)
    (hj : w ≤ j) (hj' : j ≤ 2 * w) (hu : 3 ≤ u) (ha : 2 * 2 ^ j * (4 * w) ≤ u)
    (hh : A + Fintype.card D + 2 ≤ 4 * w) (hi : Fintype.card I + Fintype.card J ≤ 2 ^ j) :
    ∃ f : (X → Bool) → F, WideWeight F u (SortTables F w) f (10000 * (Fintype.card X + 2 ^ j * w)) ∧
      ∀ (x : X → Bool) (e : I ↪ J),
        (∀ i, bits (word A) (name (e i)) = Sum.elim x id ∘ addr i) →
        f x = if (∀ v, Sum.elim x id (used v) = true ↔ v ∈ Set.range e) ∧
          ∀ v k, Sum.elim x id (dst v k) =
            Function.extend e (fun i => Sum.elim x id (src i k)) (fun _ => false) v
          then 1 else 0 := by
  let z := 4 * w - (A + 2)
  have hz : A + z + 2 = 4 * w := by unfold z; omega
  let r : I ⊕ J ↪ Fin (2 ^ j) := (Function.Embedding.nonempty_of_card_le (by simpa using hi)).some
  let p : D ↪ slots (word z) := (Function.Embedding.nonempty_of_card_le (by
    rw [card_slots, wd_word]; omega)).some
  let body (k : D → X ⊕ Bool) := Function.extend p k (fun _ => Sum.inr false)
  let head : I ⊕ J → slots (word (A + 2)) → X ⊕ Bool := Sum.elim
    (fun i => Sum.elim (fun _ => .inr true) (Sum.elim (fun _ => .inr false) (addr i)))
    (fun v => Sum.elim (fun _ => used v) (Sum.elim (fun _ => .inr true) (Sum.inr ∘ bits (word A) (name v))))
  let tap := Function.extend r (fun k => joinTap (head k) (body (Sum.elim src dst k)))
    (fun _ => Sum.inr ∘ bits (row A z) (Lookup.zero _))
  have net := wide_mul hu (packet F hj hj' hu (by rw [hz]; exact ha) (by omega) hz.le tap)
    (of_weight hu (blank_net (F := F) used dst))
  refine ⟨fun x => (if paired (packetRows tap x) then 1 else 0) *
    (if blank used dst x then 1 else 0), ?_, fun x e he => ?_⟩
  · intro a ix
    obtain ⟨n, hn, hnet⟩ := net a ix
    refine ⟨n, ?_, hnet⟩
    have hJD := Nat.mul_le_mul (show Fintype.card J ≤ 2 ^ j by omega)
      (show Fintype.card D ≤ 4 * w by omega)
    have hp := Nat.le_mul_of_pos_right (2 ^ j) (by omega : 0 < w)
    have hp' := Nat.two_pow_pos j
    ring_nf at hn hJD hp ⊢
    omega
  let val := Sum.elim x id
  let data (k : D → X ⊕ Bool) := (bits (word z)).symm (val ∘ body k)
  let v (k : Fin (2 ^ j)) := (bits (row A z)).symm (val ∘ tap k)
  have left (i) : v (r (.inl i)) = assemble (true, false, name (e i)) (data (src i)) := by
    unfold v tap
    rw [r.injective.extend_apply, decode_join]
    have hh : bits (word (A + 2)) (true, false, name (e i)) = val ∘ head (.inl i) := by
      funext k
      rcases k with _ | _ | k
      · rfl
      · rfl
      · exact congrFun (he i) k
    rw [← hh, Equiv.symm_apply_apply]
    rfl
  have right (k) : v (r (.inr k)) = assemble (val (used k), true, name k) (data (dst k)) := by
    unfold v tap
    rw [r.injective.extend_apply, decode_join]
    have hh : bits (word (A + 2)) (val (used k), true, name k) = val ∘ head (.inr k) := by
      funext l
      rcases l with _ | _ | l <;> rfl
    rw [← hh, Equiv.symm_apply_apply]
    rfl
  have pad (k) (hk : k ∉ Set.range r) : v k = Lookup.zero _ := by
    unfold v tap
    rw [Function.extend_apply' _ _ _ hk]
    exact (bits _).symm_apply_apply _
  have same (k l : D → X ⊕ Bool) : data k = data l ↔ ∀ i, val (k i) = val (l i) := by
    unfold data
    rw [(bits _).symm.injective.eq_iff]
    constructor
    · intro h i
      simpa [body, p.injective.extend_apply] using congrFun h (p i)
    · intro h
      funext j
      by_cases hj : j ∈ Set.range p
      · obtain ⟨i, rfl⟩ := hj
        simp [body, p.injective.extend_apply, h]
      · simp [body, Function.extend_apply' _ _ _ hj]
  have iff' : paired (packetRows tap x) ∧ blank used dst x ↔
      (∀ v, val (used v) = true ↔ v ∈ Set.range e) ∧
      ∀ v k, val (dst v k) = Function.extend e (fun i => val (src i k)) (fun _ => false) v := by
    change paired (List.ofFn v) ∧ _ ↔ _
    rw [pairing name e r v (val ∘ used) (data ∘ src) (data ∘ dst) left right pad]
    simp only [Function.comp_apply, same]
    constructor
    · rintro ⟨⟨flags, payload⟩, blank⟩
      refine ⟨flags, fun j k => ?_⟩
      by_cases hj : j ∈ Set.range e
      · obtain ⟨i, rfl⟩ := hj
        rw [e.injective.extend_apply, payload]
      · rw [Function.extend_apply' _ _ _ hj]
        exact blank j k (fun h => hj ((flags j).mp h))
    · rintro ⟨flags, payload⟩
      refine ⟨⟨flags, fun i k => ?_⟩, fun j k hj => ?_⟩
      · rw [payload, e.injective.extend_apply]
      · have h : j ∉ Set.range e := fun he => hj ((flags j).mpr he)
        exact (payload j k).trans (Function.extend_apply' _ _ _ h)
  simp only [ite_mul, one_mul, zero_mul, ← ite_and, iff']
  rfl

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

/-!
# Pairing internal port rows

A key contains the two ordered hosts and a row ordinal shared by
both ends. Exterior slots use other lanes and never participate in
this test. Padding makes comparison of entire rows exact.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent

namespace BatchDescent.PackRows.Channels

variable {E : Type} [Fintype E] {H m d d' u v K n : ℕ}
    (A : Channels E H m d) {r : Inventory H m d'}
    (L : Layout (append A.inventory r) u v K) (hs : ∀ i, size (append A.inventory r i) u ≤ v)

include hs in
private theorem number_lt (i : E) : rank A.inventory (A.point (i, false)) / (2 * u) < v := by
  let a := append A.inventory r
  let t := extendL A.inventory r (A.point (i, false))
  have hl : rank a t / (2 * u) < ports (a t.1) u t.2.2.1 := (portRow a u t).2.2.isLt
  have hp : ports (a t.1) u t.2.2.1 ≤ size (a t.1) u := by
    have he := Finset.single_le_sum (f := ports (a t.1) u) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ t.2.2.1)
    unfold size
    omega
  have hn := hl.trans_le (hp.trans (hs t.1))
  simpa only [a, t, rank_extendL] using hn

def label (_L : Layout (append A.inventory r) u v K) (hs : ∀ i, size (append A.inventory r i) u ≤ v)
    (x : E × Bool) : Bool × (Fin H × Fin H × Fin v) :=
  (x.2, A.host false x.1, A.host true x.1,
    ⟨rank A.inventory (A.point (x.1, false)) / (2 * u), A.number_lt hs _⟩)

private theorem same (x y : E × Bool) :
    A.label L hs x = A.label L hs y ↔ (A.loc L x.1 x.2).1 = (A.loc L y.1 y.2).1 := by
  rw [A.row_eq]
  simp [label, Prod.ext_iff, Fin.ext_iff]

variable (code : (Fin H × Fin H × Fin v) ↪ Val (word n))

def header (i : Address v K) :=
  Links.header (fun x : E × Bool => (A.loc L x.1 x.2).1) (A.label L hs) code i

theorem header_at (i : E) (b : Bool) :
    A.header L hs code (A.loc L i b).1 = (true, b, code (A.label L hs (i, b)).2) :=
  Links.header_at _ _ _ (A.same L hs) (i, b)

theorem header_other (j : Address v K) (hj : ∀ i b, (A.loc L i b).1 ≠ j) :
    A.header L hs code j = (false, false, Lookup.zero n) := by
  apply Links.header_other
  rintro ⟨⟨i, b⟩, he⟩
  exact hj i b he

theorem header_outer (t : Endpoints r) :
    A.header L hs code (L.portSlots (extendR A.inventory r t)).1 = (false, false, Lookup.zero n) := by
  apply header_other
  intro i b he
  exact channels_disjoint _ _ _ _ ((L.row_eq _ _).mp he).1.2

private theorem plan :
    ∃ plan : PacketPlan (Address v K) n, plan.head = A.header L hs code ∧
      ∀ i b, plan.peer (A.loc L i b).1 = (A.loc L i (!b)).1 := by
  obtain ⟨plan, hp, hr⟩ := Links.build_packet (fun x : E × Bool => (A.loc L x.1 x.2).1)
    (A.label L hs) code (A.same L hs) (fun x => ⟨(x.1, !x.2), rfl⟩)
  exact ⟨plan, hp, fun i b => hr (i, b) (i, !b) rfl⟩

end BatchDescent.PackRows.Channels
namespace Assembly.Scheme.Posting
open BatchDescent BatchDescent.PackRows Packing Coloring

variable {F T : Type} [Field F] {x y : Wire} {e : Fringe x y T} {h q v u K d n : ℕ}
    {S : Scheme F} {r : S.format.obj} {G : HostNet F e h (bundleSize v q)}
    (p : S.Posting r G) (hz : 0 < bundleSize v q)
    (hm : ∀ a, S.peer r a = none → bundleSize v q ∣ S.width r a)
    {l : Inventory (2 ^ S.m) (2 ^ S.h) d}
    (ex : outer S r (bundleSize v q) ≃ Endpoints l)
    (hx : ∀ j, (ex j).1 = j.val.1 ∧ (ex j).2.1 = j.val.2.1)
    (L : PackRows.Layout (append (p.channels hz).inventory l) u v K)
    (hs : ∀ i, size (append (p.channels hz).inventory l i) u ≤ v)
    (code : (Fin (2 ^ S.m) × Fin (2 ^ S.m) × Fin v) ↪ Val (word n))

theorem core_plan :
    let B := p.pieces hz hm ex hx
    ∃ plan : PacketPlan (Address v K) n, plan.head = (p.channels hz).header L hs code ∧
      ∀ y : Address v K × Row (Fin (2 * v)) (Fin (2 * u)) (Fin q) → Bool,
        Links.pad (B.inside L) y →
        ((∀ i, (plan.head i).1 = true → Function.curry y (plan.peer i) = Function.curry y i) ↔
          ∀ a b, S.Joins r a b → y (B.inside L a) = y (B.inside L b)) := by
  let B := p.pieces hz hm ex hx
  let A := p.channels hz
  let join := BatchDescent.join S r _ B.uniform
  let pin (i : G.E) (b : Bool) (t : Fin (bundleSize v q)) := join (p.unitOf hz i b, t)
  have loc (i b t) : B.inside L (pin i b t) =
      ((A.loc L i b).1, (A.loc L i b).2, finProdFinEquiv.symm t) := by
    unfold pin join
    rw [B.inside_join, p.pieces_inner]
    rfl
  have pair (i b t) : S.Joins r (pin i b t) (pin i (!b) t) := ⟨p.span_peer hz _ _, rfl⟩
  obtain ⟨plan, he, peer⟩ := A.plan L hs code
  refine ⟨plan, he, fun y hy => ?_⟩
  constructor
  · intro check s t hst
    obtain ⟨⟨s, i⟩, rfl⟩ := join.surjective s
    obtain ⟨⟨t, j⟩, rfl⟩ := join.surjective t
    obtain ⟨rfl, k, b, rfl, rfl⟩ := p.joined hz B.uniform hst
    have hh := check (A.loc L k b).1 (by rw [he, A.header_at])
    change y (B.inside L (pin k b i)) = y (B.inside L (pin k (!b) i))
    rw [loc, loc, ← A.col_eq L k b, ← peer]
    exact (congrFun hh _).symm
  · intro links
    have present (i : Address v K) (hi : (plan.head i).1 = true)
        (t : Row (Fin (2 * v)) (Fin (2 * u)) (Fin q)) (ht : y (i, t) = true) :
        y (plan.peer i, t) = true := by
      obtain ⟨a, ha⟩ : (i, t) ∈ Set.range (B.inside L) := by
        by_contra hh
        exact Bool.false_ne_true ((hy _ hh).symm.trans ht)
      obtain ⟨⟨a, j⟩, rfl⟩ := join.surjective a
      rcases p.unit_cases hz a with ha' | ⟨k, b, rfl⟩
      · have hf := show B.equiv a = _ from p.pieces_outer hz hm ex hx ⟨a, ha'⟩
        unfold join at ha
        rw [B.inside_join, hf] at ha
        rw [he, ← (Prod.mk.inj ha).1, A.header_outer] at hi
        cases hi
      · have hval := links _ _ (pair k b j)
        change B.inside L (pin k b j) = (i, t) at ha
        rw [loc] at ha
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha
        rw [loc, loc, ← A.col_eq L k b, ← peer] at hval
        exact hval.symm.trans ht
    intro i hi
    have hp : (plan.head (plan.peer i)).1 = true := by rw [plan.pairs]; exact hi
    funext t
    apply Bool.eq_iff_iff.mpr
    exact ⟨fun h => by simpa [plan.square] using present _ hp t h, present i hi t⟩

end Assembly.Scheme.Posting
end OAI.LinearAlgebra.MatrixExponent
end

/-!
# Generating the internal packet headers

The group of rows at a port shares a pair of host names. Local
lengths suffice to determine whether a row is active and to produce
its direction and ordinal. No payload bits enter these decisions.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows.Channels

variable {E : Type} [Fintype E] {H m d e u v K n : ℕ}

def decodeLane (j : Fin (2 * d)) : Bool × Fin d :=
  Prod.map finTwoEquiv id (finProdFinEquiv.symm j)

def source (d e u v : ℕ) (l : Lengths m (2 * d + e)) (j : Fin (2 * d + e)) (k : ℕ) :
    Option (Bool × Fin v) :=
  if h : j.val < 2 * d ∧ k < v ∧ k * (2 * u) < ∑ i, l i j then
    some ((decodeLane ⟨j.val, h.1⟩).1, ⟨k, h.2.1⟩)
  else none

def names (neighbor : Fin H → Fin d → Fin H) (i : Fin H) (j : Fin (2 * d + e)) : Fin H × Fin H :=
  if h : j.val < 2 * d then
    let lane := decodeLane ⟨j.val, h⟩
    let other := neighbor i lane.2
    if lane.1 then (other, i) else (i, other)
  else (i, i)

def fill (code : (Fin H × Fin H × Fin v) ↪ Val (word n)) (names : Fin H × Fin H) :
    Option (Bool × Fin v) → Val (word (n + 2))
  | some (b, k) => (true, b, code (names.1, names.2, k))
  | none => (false, false, Lookup.zero n)

variable (A : Channels E H m (2 * d)) {x : Inventory H m e}
    (L : Layout (append A.inventory x) u v K) (hs : ∀ i, size (append A.inventory x i) u ≤ v)
    (code : (Fin H × Fin H × Fin v) ↪ Val (word n))

def Names (neighbor : Fin H → Fin d → Fin H) : Prop :=
  ∀ i b, (decodeLane (A.lane b i)).1 = b ∧
    neighbor (A.host b i) (decodeLane (A.lane b i)).2 = A.host (!b) i

omit [Fintype E] in
private theorem names_at (neighbor : Fin H → Fin d → Fin H) (hn : A.Names neighbor)
    (i : E) (b : Bool) :
    names neighbor (A.host b i) (Fin.castAdd e (A.lane b i)) = (A.host false i, A.host true i) := by
  unfold names
  rw [dite_eq_left (show (Fin.castAdd e (A.lane b i)).val < 2 * d from (A.lane b i).isLt)]
  change (if (decodeLane (A.lane b i)).1 then _ else _) = _
  rw [(hn i b).1]
  cases b
  · exact Prod.ext rfl (hn i false).2
  · exact Prod.ext (hn i true).2 rfl

private theorem rank_lt {d' : ℕ} (l : Inventory H m d') (t : Endpoints l) :
    rank l t < ∑ i, l t.1 i t.2.2.1 :=
  (order (port (l t.1) t.2.2.1) ⟨t.2.1, t.2.2.2⟩).isLt

private theorem live (i : Fin H) (j : Fin (2 * d + e)) (k : Fin (ports (append A.inventory x i) u j))
    (hu : 0 < u) (hj : j.val < 2 * d) (hk : k.val * (2 * u) < ∑ t, append A.inventory x i t j) :
    ∃ t b, (A.loc L t b).1 = L.portLoc ⟨i, j, k⟩ := by
  let l : Fin (2 * d) := ⟨j.val, hj⟩
  have he : Fin.castAdd e l = j := rfl
  have hv : k.val * (2 * u) < ∑ t, port (A.inventory i) l t := by
    simpa only [← he, append_left, port] using hk
  let o := order (port (A.inventory i) l)
  let p := o.symm ⟨_, hv⟩
  let q : Endpoints A.inventory := ⟨i, p.1, l, p.2⟩
  have hr : rank A.inventory q = k.val * (2 * u) := congrArg Fin.val (o.apply_symm_apply ⟨_, hv⟩)
  obtain ⟨⟨t, b⟩, hb⟩ := A.point.surjective q
  refine ⟨t, b, ?_⟩
  unfold loc
  rw [hb, L.locate]
  apply congrArg L.portLoc
  change (⟨i, j, _⟩ : PortRows (append A.inventory x) u) = _
  apply congrArg (fun q => (⟨i, j, q⟩ : PortRows (append A.inventory x) u))
  apply Fin.ext
  change rank _ (extendL A.inventory x q) / (2 * u) = k.val
  rw [rank_extendL, hr, Nat.mul_div_cancel _ (by omega)]

theorem header_eq_fill (hu : 0 < u) (neighbor : Fin H → Fin d → Fin H) (hn : A.Names neighbor)
    (i : Fin H) (j : Fin (2 * d + e)) (k : Fin (ports (append A.inventory x i) u j)) :
    A.header L hs code (L.portLoc ⟨i, j, k⟩) = fill code (names neighbor i j)
      (source d e u v (append A.inventory x i) j k.val) := by
  classical
  by_cases occurs : ∃ t b, (A.loc L t b).1 = L.portLoc ⟨i, j, k⟩
  · obtain ⟨t, b, he⟩ := occurs
    let s := extendL A.inventory x (A.point (t, b))
    have hp : portRow _ u s = ⟨i, j, k⟩ := L.portLoc.injective ((L.locate s).symm.trans he)
    have hi : A.host b t = i := congrArg Sigma.fst hp
    have hj : Fin.castAdd e (A.lane b t) = j := congrArg (·.2.1) hp
    have hk : rank _ s / (2 * u) = k.val := congrArg (·.2.2.val) hp
    have hl : (A.label L hs (t, b)).2.2.2.val = k.val := by
      simpa only [label, s, rank_extendL, A.rank_eq t b] using hk
    have hok : j.val < 2 * d ∧ k.val < v ∧ k.val * (2 * u) < ∑ a, append A.inventory x i a j := by
      refine ⟨hj ▸ (A.lane b t).isLt, hl ▸ (A.label L hs (t, b)).2.2.2.isLt, ?_⟩
      have h := (Nat.div_mul_le_self (rank _ s) (2 * u)).trans_lt (rank_lt _ s)
      rw [hk, show s.2.2.1 = j from hj, show s.1 = i from hi] at h
      exact h
    rw [← he, header_at, source, dite_eq_left hok, fill]
    have eq : (⟨j.val, hok.1⟩ : Fin (2 * d)) = A.lane b t :=
      Fin.ext (congrArg (fun z : Fin (2 * d + e) => z.val) hj.symm)
    have names_eq : names neighbor i j = (A.host false t, A.host true t) := by
      rw [← hi, ← hj, A.names_at neighbor hn]
    rw [names_eq, eq, (hn t b).1, show (⟨k.val, hok.2.1⟩ : Fin v) = _ from Fin.ext hl.symm]
    rfl
  · have he : ∀ t b, (A.loc L t b).1 ≠ L.portLoc ⟨i, j, k⟩ := fun t b hh => occurs ⟨t, b, hh⟩
    have no : ¬ (j.val < 2 * d ∧ k.val < v ∧ k.val * (2 * u) < ∑ t, append A.inventory x i t j) :=
      fun h => occurs (A.live L i j k hu h.1 h.2.2)
    rw [source, dite_eq_right no, fill, A.header_other L hs code _ he]

theorem header_absent (i : Address v K) (h : i ∉ Set.range L.portLoc) :
    A.header L hs code i = (false, false, Lookup.zero n) := by
  apply header_other
  intro e b he
  exact h ⟨_, (L.locate _).symm.trans he⟩

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows.Channels

namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Posting
open BatchDescent BatchDescent.PackRows Packing Coloring

variable {F T : Type} [Field F] {x y : Wire} {f : Fringe x y T} {h z : ℕ}
    {S : Scheme F} {r : S.format.obj} {G : HostNet F f h z} (p : S.Posting r G) (hz : 0 < z)

theorem names : (p.channels hz).Names (fun i => (r i).1) := by
  intro i b
  simp only [channels, lane, Channels.decodeLane, Equiv.symm_apply_apply,
    Prod.map, Equiv.apply_symm_apply, id_eq, true_and]
  exact p.neighbor hz i b

theorem header_eq_fill {d u v K n : ℕ} {l : Inventory (2 ^ S.m) (2 ^ S.h) d}
    (L : PackRows.Layout (append (p.channels hz).inventory l) u v K)
    (hs : ∀ i, size (append (p.channels hz).inventory l i) u ≤ v)
    (code : (Fin (2 ^ S.m) × Fin (2 ^ S.m) × Fin v) ↪ Val (word n)) (hu : 0 < u)
    (i : B S.m) (j : Fin (2 * 2 ^ S.d + d)) (k : Fin (ports (append (p.channels hz).inventory l i) u j)) :
    (p.channels hz).header L hs code (L.portLoc ⟨i, j, k⟩) =
      Channels.fill code (Channels.names (fun i => (r i).1) i j)
        (Channels.source (2 ^ S.d) d u v (append (p.channels hz).inventory l i) j k.val) :=
  (p.channels hz).header_eq_fill L hs code hu _ (p.names hz) i j k

end OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Posting
end

/-!
# Evaluating all terminal tables and checking the internal links

Port rows, including padding, are actual bits on the common tape.
A single tensor works for every layout described on that tape.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows
open Assembly Coloring Transcript Classical

abbrev Body (u v p : ℕ) := Row (Fin (2 * v)) (Fin (2 * u)) (Fin p)
abbrev Tape (u v K p : ℕ) := Address v K × Body u v p

variable {F X : Type} {S : Scheme F} {r : S.format.obj}
    {u v K p d a : ℕ} {l : Inventory (2 ^ S.m) (2 ^ S.h) d}

theorem pad_iff (A : Pieces S r l v p) (L : PackRows.Layout l u v K)
    (y : Tape u v K p → Bool) :
    Links.pad (A.inside L) y ↔ L.Padded (fun i t => y (i.1, i.2, t)) := by
  have eq (i : Address v K × Fin (2 * u)) (t : Payload v (Fin p)) :
      (i.1, i.2, t) ∈ Set.range (A.inside L) ↔ i ∈ Set.range L.portSlots := by
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨(A.slots q).1, congrArg (fun j => (j.1, j.2.1)) hq⟩
    · rintro ⟨q, rfl⟩
      refine ⟨A.slots.symm (q, t), ?_⟩
      unfold Pieces.inside
      simp
  constructor
  · exact fun h i hi t => h (i.1, i.2, t) (mt (eq _ _).mp hi)
  · rintro h ⟨j, k, t⟩ he
    exact h (j, k) (mt (eq _ _).mpr he) t

structure Wires (S : Scheme F) (u v K p a : ℕ) (X : Type) where
  control : Fin K → Route v u → X ⊕ Bool
  format : Address v K → Tag (2 ^ S.h) S.ℓ u → X ⊕ Bool
  head : Address v K → slots (word (a + 2)) → X ⊕ Bool
  body : Tape u v K p → X ⊕ Bool

namespace Wires
variable (t : Wires S u v K p a X)

def port (i : Fin K) (s : Socket v u) (b : Payload v (Fin p)) :=
  t.body ((i, s.1), s.2, b)

def read (x : X → Bool) : Tape u v K p → Bool := Sum.elim x id ∘ t.body

def Supplied (A : Pieces S r l v p) (ha : Pieces.Room (l := l) (u := u))
    (L : PackRows.Layout l u v K) (heads : Address v K → Val (word (a + 2))) (x : X → Bool) : Prop :=
  (∀ g, Sum.elim x id ∘ t.control g = L.moves g) ∧
  (∀ i, Sum.elim x id ∘ t.format i = L.format (A.index ha) (labels S r) i) ∧
  ∀ i, bits (word (a + 2)) (heads i) = Sum.elim x id ∘ t.head i

variable [Field F]

def test (A : Pieces S r l v p) (L : PackRows.Layout l u v K)
    (π : PacketPlan (Address v K) a) (x : X → Bool) : F :=
  let y := t.read x
  if Links.pad (A.inside L) y ∧
      (∀ i, (π.head i).1 = true → Function.curry y (π.peer i) = Function.curry y i)
    then ∏ j, S.table r j (y ∘ A.inside L ∘ S.port r j) else 0

structure Fits (S : Scheme F) (u v K p a w j cap : ℕ) : Prop where
  lower : w ≤ j
  upper : j + 1 ≤ 2 * w
  gates : 3 ≤ cap
  large : 2 * 2 ^ (2 * w) * (4 * w) ≤ cap
  slots : K * (2 * v) ≤ 2 ^ j
  move : (4 * v * u) ^ 2 + 2 * (2 * u * bundleSize v p) < j
  table : 2 ^ S.h * (1 + S.ℓ + 2 * u ^ 2) + 2 * u * bundleSize v p < j
  wide : w ≤ a + 2 * u * bundleSize v p + 2
  narrow : a + 2 * u * bundleSize v p + 2 ≤ 4 * w

theorem service [Fintype X] {w j cap : ℕ} (ok : Fits S u v K p a w j cap) :
    ∃ f : (X → Bool) → F, WideWeight F cap (SortTables F w) f
        (500000 * (Fintype.card X + 2 ^ j * (1 + w))) ∧
      ∀ (r : S.format.obj) (d : ℕ) (l : Inventory (2 ^ S.m) (2 ^ S.h) d)
        (A : Pieces S r l v p) (ha : Pieces.Room (l := l) (u := u))
        (L : PackRows.Layout l u v K) (π : PacketPlan (Address v K) a) x,
        t.Supplied A ha L π.head x → f x = t.test A L π x := by
  have ar : 2 * 2 ^ (j + 1) * (2 * j + 2) ≤ cap := by
    apply le_trans _ ok.large
    have := ok.upper
    gcongr; omega
  have ht : Fintype.card (Body u v p) = 2 * u * bundleSize v p := by simp [Body, bundleSize]
  have rows : Fintype.card (Address v K) ≤ 2 ^ j := by simpa using ok.slots
  have move : Fintype.card (Route v u) + 2 * Fintype.card (Body u v p) < j := by
    rw [width_route, ht]; exact ok.move
  have ev : Fintype.card (Tag (2 ^ S.h) S.ℓ u) + Fintype.card (Body u v p) < j := by
    rw [width_tag, ht]; exact ok.table
  have h₁ := (packTables (entry S u v p) t.control t.format t.port).reassemble
    ok.lower ok.upper ok.gates ar move ev rows
  have h₂ := packed_zero (F := F) t.control t.port ok.lower ok.upper ok.gates ar
    (show Fintype.card (Route v u) + Fintype.card (Body u v p) < j by omega) rows
  let e : slots (word (2 * u * bundleSize v p)) ≃ Body u v p :=
    Fintype.equivOfCardEq (by rw [card_slots, wd_word, ht])
  obtain ⟨g, h₃, hg⟩ := packet_plan F ok.lower (by have := ok.upper; omega) ok.gates
    (show 2 * 2 ^ j * (a + 2 * u * bundleSize v p + 2) ≤ cap by
      apply le_trans _ ok.large
      have := ok.upper
      have := ok.narrow
      gcongr; omega) ok.wide ok.narrow rows t.head (fun i k => t.body (i, e k))
  have H := wide_mul ok.gates h₂ (wide_mul ok.gates h₃ h₁)
  refine ⟨fun x => zeroTest F t.control t.port x *
    (g x * (packTables (entry S u v p) t.control t.format t.port).value x), ?_, ?_⟩
  · intro b i
    obtain ⟨m, hm, hm'⟩ := H b i
    refine ⟨m, ?_, hm'⟩
    have := Nat.mul_le_mul_left (2 ^ j) ok.upper
    linarith
  · rintro r d l A ha L π x ⟨hc, hf, hh⟩
    let y := t.read x
    have check (i k : Address v K) :
        (Sum.elim x id ∘ (fun b => t.body (i, e b))) =
          (Sum.elim x id ∘ (fun b => t.body (k, e b))) ↔
        Function.curry y i = Function.curry y k := by
      constructor
      · intro h
        funext b
        obtain ⟨b, rfl⟩ := e.surjective b
        exact congrFun h b
      · exact fun h => congrArg (· ∘ e) h
    have padded : L.Padded (readPort t.port x) ↔ Links.pad (A.inside L) y :=
      (pad_iff A L y).symm
    have value : (packTables (entry S u v p) t.control t.format t.port).value x =
        ∏ i, S.table r i (y ∘ A.inside L ∘ S.port r i) :=
      (packed_value L (A.index ha) _ x hc hf).trans (A.product ha L y)
    dsimp only
    rw [zeroTest_eq (F := F) L x hc, hg x π hh, value]
    simp only [check, padded, test, y, ite_mul, one_mul, zero_mul, ite_and]

end Wires
end OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows
end
