import OAI.LinearAlgebra.MatrixExponent.Radix.Defs
import OAI.LinearAlgebra.MatrixExponent.Lookup.Scan
import OAI.LinearAlgebra.MatrixExponent.Tagged.Array
import OAI.LinearAlgebra.MatrixExponent.Diagram.Permute
import OAI.LinearAlgebra.MatrixExponent.Radix.WideTag
import OAI.LinearAlgebra.MatrixExponent.Tagged.SortOne
import OAI.LinearAlgebra.MatrixExponent.Radix.Protocol
import OAI.LinearAlgebra.MatrixExponent.Network.Dense

section
/-!
# Checking a tagged permutation by sorting

Mark the labelled inputs and the proposed outputs with opposite bits.
Sort by the common address and payload, ignoring empty slots. Since
input labels are distinct, a permutation is characterized by consecutive
pairs with equal keys and opposite marks. Their order within a pair is free.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Radix

private def side {α : Type} (b : Bool) (xs : List (Bool × α)) : List α :=
  (xs.filter (fun r => r.1 == b)).map Prod.snd

private def paired {α : Type} : List (Bool × α) → Prop
  | [] => True
  | [_] => False
  | x :: y :: xs => x.1 ≠ y.1 ∧ x.2 = y.2 ∧ paired xs

private theorem paired_iff {α : Type} [LinearOrder α] (xs : List (Bool × α))
    (hs : xs.Pairwise (fun i j => i.2 ≤ j.2)) (hn : (side false xs).Nodup) :
    paired xs ↔ (side false xs).Perm (side true xs) := by
  induction xs using List.twoStepInduction with
  | nil => simp [paired, side]
  | singleton x => obtain ⟨_ | _, _⟩ := x <;> simp [paired, side]
  | cons_cons x y xs ih _ =>
    obtain ⟨hx, hys⟩ := List.pairwise_cons.mp hs
    obtain ⟨hy, hxs⟩ := List.pairwise_cons.mp hys
    have mate (h : (side false (x::y::xs)).Perm (side true (x::y::xs))) :
        x.1 ≠ y.1 ∧ x.2 = y.2 := by
      have hn' : (side x.1 (x::y::xs)).Nodup := by
        cases x.1
        · exact hn
        · exact h.nodup hn
      have hp : (side x.1 (x::y::xs)).Perm (side (!x.1) (x::y::xs)) := by
        cases x.1
        · exact h
        · exact h.symm
      have hm := hp.subset (show x.2 ∈ side x.1 (x::y::xs) by simp [side])
      have hmy : x.2 ∈ side (!x.1) (y::xs) := by simpa [side] using hm
      obtain ⟨z, hz, he⟩ := List.mem_map.mp hmy
      have ey : x.2 = y.2 := by
        apply le_antisymm (hx y (by simp))
        rw [← he]
        rcases List.mem_cons.mp (List.mem_filter.mp hz).1 with rfl | h
        · exact le_rfl
        · exact hy _ h
      refine ⟨fun e => ?_, ey⟩
      simp [side, e, ey] at hn'
    by_cases good : x.1 ≠ y.1 ∧ x.2 = y.2
    · have drop (b : Bool) : side b (x::y::xs) = x.2 :: side b xs := by
        obtain ⟨p, u⟩ := x
        obtain ⟨q, v⟩ := y
        cases p <;> cases q <;> cases b <;> simp_all [side]
      rw [drop] at hn
      simp only [paired, good.1, good.2, ne_eq, not_false_eq_true, true_and, drop, List.perm_cons]
      exact ih hxs (List.nodup_cons.mp hn).2
    · exact iff_of_false (fun h => good ⟨h.1, h.2.1⟩) (fun h => good (mate h))

private abbrev recWire (n : ℕ) := word (n + 1)
private abbrev pairState (n : ℕ) := word (n + 3)

private def pairStep (n : ℕ) (s : Val (pairState n)) (r : Val (recWire n)) :
    Val (pairState n) :=
  (s.1 && (!s.2.1 || (decide (s.2.2.1 ≠ r.1) && decide (s.2.2.2 = r.2))), !s.2.1, r)

private def slotStep (n : ℕ) (s : Val (pairState n)) (r : Val (slot (recWire n))) :
    Val (pairState n) := if r.1 then s else pairStep n s r.2

private def finish (n : ℕ) (s : Val (pairState n)) : Bool := s.1 && !s.2.1

private theorem skip_empty (n : ℕ) (xs : List (Val (slot (recWire n)))) (s : Val (pairState n)) :
    xs.foldl (slotStep n) s = (real xs).foldl (pairStep n) s := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨b, r⟩ := x
    cases b <;> simp [slotStep, real, ih]

private theorem check_pairs (n : ℕ) (xs : List (Val (recWire n))) (ok : Bool)
    (last : Val (recWire n)) :
    finish n (xs.foldl (pairStep n) (ok, false, last)) = true ↔ ok = true ∧ paired xs := by
  induction xs using List.twoStepInduction generalizing ok last with
  | nil => simp [finish, paired]
  | singleton x => simp [finish, pairStep, paired]
  | cons_cons x y xs ih _ =>
    simp [pairStep, paired, Bool.and_eq_true, ih, and_assoc]

variable (F : Type) [Field F]

private theorem slot_net (n : ℕ) :
    DNet F (.pair (pairState n) (slot (recWire n))) (pairState n)
      (fun x => slotStep n x.1 x.2) (500 * (n + 1)) := by
  have old := DNet.fst F (pairState n) (slot (recWire n))
  have next := DNet.snd F (pairState n) (slot (recWire n))
  have ok := old.comp (DNet.fst F .bit (word (n + 2)))
  have prev := old.comp (DNet.snd F .bit (word (n + 2)))
  have wait := (prev.comp (DNet.fst F .bit (recWire n))).comp
    (DNet.table F .bit .bit (fun b => !b) (by decide))
  have blank := next.comp (DNet.fst F .bit (recWire n))
  have x := prev.comp (DNet.snd F .bit (recWire n))
  have y := next.comp (DNet.snd F .bit (recWire n))
  have both := DNet.table F (.pair .bit .bit) .bit (fun p => p.1 && p.2) (by decide)
  have either := DNet.table F (.pair .bit .bit) .bit (fun p => p.1 || p.2) (by decide)
  have diff := DNet.table F (.pair .bit .bit) .bit (fun p => decide (p.1 ≠ p.2)) (by decide)
  have test := (((diff.par (Lookup.eq_net F n)).pre (.middle .bit (word n) .bit (word n))).comp both)
  have matchRow := (x.pair y).comp test
  have step := ((ok.pair ((wait.pair matchRow).comp either)).comp both).pair (wait.pair y)
  have h := ((old.pair step).pair blank).comp (selectWord F (n + 3))
  exact h.mono (by simp only [wd, wd_word]; omega)

private def checked (n l : ℕ) (x : Val (tree l (slot (recWire n)))) : Bool :=
  finish n ((flatten l x).foldl (slotStep n) (true, false, Lookup.zero _))

private theorem check_net (n l : ℕ) :
    DNet F (tree l (slot (recWire n))) .bit (checked n l) (1000 * 2 ^ l * (n + 1)) := by
  have seed := ((Lookup.const_net F (pairState n) (true, false, Lookup.zero _)).par
    (DNet.id F (tree l (slot (recWire n))))).pre ((Rewire.unit' _).comp (.swap _ _))
  have done := DNet.table F (.pair .bit .bit) .bit (fun x => x.1 && !x.2) (by decide)
  have readout := ((DNet.id F .bit).par (DNet.fst F .bit (recWire n))).comp done
  have net := (seed.comp (Lookup.fold_net F (slot_net F n) l)).comp readout
  apply net.mono
  simp only [wd_tree, wd, wd_word]
  have h : 1 ≤ 2 ^ l := Nat.one_le_pow _ _ (by decide)
  nlinarith [Nat.mul_le_mul_right n h]

private def blanks (n : ℕ) : (l : ℕ) → Val (tree l (slot (recWire n)))
  | 0 => (true, Lookup.zero _)
  | l + 1 => (blanks n l, blanks n l)

private theorem blanks_empty (n l : ℕ) : real (flatten l (blanks n l)) = [] := by
  induction l with
  | zero => rfl
  | succ l ih =>
    simp only [blanks, flatten, real, List.filter_append, List.map_append] at *
    rw [ih, List.nil_append]

private def mark {a : Wire} {n : ℕ} (e : Val a → Val (word n)) (b : Bool) (x : Val a) :
    Val (slot (recWire n)) := (false, b, e x)

private abbrev addr (w : ℕ) := Tagged.row w (word w)

private def prepare (w : ℕ) (e : Val (addr w) → Val (word (2 * w)))
    (x : Val (Tagged.inputs w (word w))) : Val (tree (w + 2) (slot (recWire (2 * w)))) :=
  ((Tagged.mapRows (mark e false) w (Tagged.label w x.1), Tagged.mapRows (mark e true) w x.2),
    blanks _ _)

private theorem prepared {w : ℕ} (e : Val (addr w) → Val (word (2 * w)))
    (x : Val (Tagged.inputs w (word w))) :
    real (flatten (w + 2) (prepare w e x)) =
      (flatten w (Tagged.label w x.1)).map (fun u => (false, e u)) ++
      (flatten w x.2).map (fun u => (true, e u)) := by
  have hm (b : Bool) (xs : List (Val (addr w))) :
      real (xs.map (mark e b)) = xs.map (fun u => (b, e u)) := by
    induction xs with
    | nil => rfl
    | cons y ys ih => simpa [real, mark] using congrArg (List.cons (b, e y)) ih
  have ha (xs ys : List (Val (slot (recWire (2 * w))))) :
      real (xs ++ ys) = real xs ++ real ys := by simp [real]
  simp only [prepare, blanks, flatten, Tagged.flatten_mapRows, ha, hm]
  rw [blanks_empty (2 * w) w, List.nil_append, List.append_nil]

private theorem prepare_net {w : ℕ} {e : Val (addr w) → Val (word (2 * w))}
    (he : Rewire (addr w) (word (2 * w)) e) :
    DNet F (Tagged.inputs w (word w)) (tree (w + 2) (slot (recWire (2 * w))))
      (prepare w e) (100 * 2 ^ w * (w + 1)) := by
  have hm (b : Bool) : DNet F (addr w) (slot (recWire (2 * w))) (mark e b)
      (2 + wd (addr w)) := by
    have flag := Lookup.const_net F (.pair .bit .bit) (false, b)
    exact (((flag.par ((DNet.id F _).post he)).pre
      ((Rewire.unit' _).comp (.swap _ _))).post (.assoc _ _ _))
  have h₁ := (Tagged.label_net F w (word w)).comp (Tagged.mapRows_net (hm false) w)
  have h₂ := Tagged.mapRows_net (hm true) w
  have padding := Lookup.const_net F _ (blanks (2 * w) (w + 1))
  apply (((h₁.par h₂).par padding).pre (.unit' _)).mono
  simp only [wd_tree, wd_word, wd]
  ring_nf
  omega

private theorem check_spec {w : ℕ} {e : Val (addr w) → Val (word (2 * w))}
    (he : Function.Injective e) (x : Val (Tagged.inputs w (word w)))
    (y : Val (tree (w + 2) (slot (recWire (2 * w)))))
    (hp : (real (flatten (w + 2) y)).Perm (real (flatten (w + 2) (prepare w e x))))
    (hs : (real (flatten (w + 2) y)).Pairwise (fun i j => (wordOrder (2 * w)).le i.2 j.2)) :
    checked (2 * w) (w + 2) y = true ↔ (flatten w x.2).Perm (flatten w (Tagged.label w x.1)) := by
  let ys := real (flatten (w + 2) y)
  have hm (b : Bool) : (side b ys).Perm (side b (real (flatten (w + 2) (prepare w e x)))) :=
    (hp.filter _).map _
  rw [prepared e x] at hm
  have hl : (side false ys).Perm ((flatten w (Tagged.label w x.1)).map e) := by
    simpa [side, List.filter_map, Function.comp_def] using hm false
  have hr : (side true ys).Perm ((flatten w x.2).map e) := by
    simpa [side, List.filter_map, Function.comp_def] using hm true
  have hn := hl.symm.nodup ((Tagged.label_nodup w x.1).map he)
  rw [checked, skip_empty, check_pairs, eq_self_iff_true, true_and, paired_iff _ hs hn]
  exact ⟨fun h => (List.map_perm_map_iff he).mp (hr.symm.trans (h.symm.trans hl)),
    fun h => hl.trans ((h.symm.map e).trans hr.symm)⟩

/-- One sort of the marked union suffices. It uses twice the number of
live rows as payloads, leaving half of its slots empty. -/
theorem tag_of_sort {F : Type} [Field F] {w m : ℕ}
    {sort : Val (tree (w + 2) (slot (word (2 * w + 1)))) → Val (tree (w + 2) (slot (word (2 * w + 1))))}
    (h : DNet F (tree (w + 2) (slot (word (2 * w + 1)))) (tree (w + 2) (slot (word (2 * w + 1)))) sort m)
    (hs : ∀ x, (real (flatten (w + 2) x)).length ≤ 2 ^ (w + 1) →
      (real (flatten (w + 2) (sort x))).Perm (real (flatten (w + 2) x)) ∧
      (real (flatten (w + 2) (sort x))).Pairwise (fun i j => (wordOrder (2 * w)).le i.2 j.2)) :
    ∃ v ≤ m + 100000 * 2 ^ w * (w + 1), Net F (Tagged.inputs w (word w)) .unit
      (Tagged.tag F w (word w)) v := by
  obtain ⟨e, he, hinj⟩ := Rewire.exists_of_width (a := addr w) (b := word (2 * w))
    (by simp [wd, two_mul])
  have good (x : Val (Tagged.inputs w (word w))) :
      checked (2 * w) (w + 2) (sort (prepare w e x)) = true ↔
        (flatten w x.2).Perm (flatten w (Tagged.label w x.1)) := by
    obtain ⟨hp, ho⟩ := hs (prepare w e x) (by
      rw [prepared e x]
      rw [List.length_append, List.length_map, List.length_map, Tagged.length_flatten,
        Tagged.length_flatten, pow_succ]
      omega)
    exact check_spec hinj x _ hp ho
  obtain ⟨v, hv, net⟩ := ((prepare_net F he).comp h).comp (check_net F (2 * w) (w + 2))
  have pin := Net.table (F := F) .bit .unit (fun b _ => if b then 1 else 0) (by decide)
  refine ⟨v + 1, ?_, ?_⟩
  · have hpos : 0 < 2 ^ w := by positivity
    rw [pow_add] at hv
    ring_nf at hv ⊢
    omega
  · convert net.comp pin using 1
    funext x _
    simp only [Tagged.tag, Tagged.permuted, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, good]

end OAI.LinearAlgebra.MatrixExponent.Radix
end

section
/-!
# Sorting a long key by stable digit passes

The last digits are sorted first. When an earlier digit is processed, each
sublist with that digit retains its order. A rewiring keeps the unused key
prefix attached to the suffix during the construction of each digit circuit.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Radix

private theorem split_word (n s : ℕ) :
    ∃ f : Val (word (n + s)) → Val (.pair (word s) (word n)),
      Rewire (word (n + s)) (.pair (word s) (word n)) f ∧
      ∀ x y, x ≤ y ↔ (f x).1 < (f y).1 ∨ (f x).1 = (f y).1 ∧ (f x).2 ≤ (f y).2 := by
  induction s with
  | zero =>
    refine ⟨_, (Rewire.unit' _).comp (.swap _ _), ?_⟩
    intro x y
    simp
  | succ s ih =>
    obtain ⟨f, hf, ho⟩ := ih
    refine ⟨_, ((Rewire.id .bit).par hf).comp (.assoc' _ _ _), ?_⟩
    rintro ⟨b, x⟩ ⟨c, y⟩
    change toLex (b, x) ≤ toLex (c, y) ↔
      toLex (b, (f x).1) < toLex (c, (f y).1) ∨
        (b, (f x).1) = (c, (f y).1) ∧ (f x).2 ≤ (f y).2
    rw [Prod.Lex.toLex_le_toLex, Prod.Lex.toLex_lt_toLex, Prod.mk.injEq, ho]
    tauto

private theorem combine {α : Type} {s n : ℕ} {d : α → Val (word s)}
    {low : α → Val (word n)} {xs ys : List α} (hs : Stable d xs ys)
    (hl : xs.Pairwise (fun x y => low x ≤ low y)) :
    ys.Pairwise (fun x y => d x < d y ∨ d x = d y ∧ low x ≤ low y) := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  rcases (List.pairwise_iff_getElem.mp hs.2.1 i j hi hj hij).lt_or_eq with h | h
  · exact .inl h
  · refine .inr ⟨h, ?_⟩
    have hk := hl.filter (fun x => d x = d ys[j])
    rw [← hs.2.2] at hk
    exact List.pairwise_iff_getElem.mp (List.pairwise_filter.mp hk) i j hi hj hij
      (decide_eq_true h) (decide_eq_true rfl)

variable {F : Type} [Field F] {a : Wire} {n s : ℕ}

private theorem pad_key {p : ℕ} (hp : n ≤ p) (f : Val a → Val (word n))
    (hf : DNet F a (word n) f (wd a)) :
    ∃ g : Val a → Val (word p), DNet F a (word p) g (wd a + p) ∧
      ∀ x y, g x ≤ g y → f x ≤ f y := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hp
  obtain ⟨u, hu, ho⟩ := split_word n j
  obtain ⟨v, hv, hi⟩ := hu.inverse
  have hz := Tagged.literal_net F (word j) (Lookup.zero j)
  have net := ((hz.par hf).pre ((Rewire.unit' a).comp (.swap _ _))).post hv
  refine ⟨_, net.mono (by simp only [wd_word]; omega), ?_⟩
  intro x y h
  have huv (z) : u (v z) = z := (hi _ _).mpr rfl
  rw [ho, huv, huv] at h
  exact (h.resolve_left (lt_irrefl _)).2

/-- A pass can rearrange empty slots freely. Only its action on the real
records matters, and the occupancy bound is preserved by permutation. -/
theorem radix (F : Type) [Field F] (a : Wire) (h s M : ℕ) (hs : 0 < s)
    (H : ∀ d : Val a → Val (word s), DNet F a (word s) d (100 * (1 + wd a + s)) →
      ∃ f, DNet F (tree h (slot a)) (tree h (slot a)) f M ∧
        ∀ x, 2 * (real (flatten h x)).length ≤ 2 ^ h →
          Stable d (real (flatten h x)) (real (flatten h (f x))))
    {n : ℕ} (hn : n ≤ wd a) (f : Val a → Val (word n)) (hf : DNet F a (word n) f (wd a)) :
    ∃ g, DNet F (tree h (slot a)) (tree h (slot a)) g ((n / s + 1) * M + 2 ^ h * (1 + wd a)) ∧
      ∀ x, 2 * (real (flatten h x)).length ≤ 2 ^ h →
        (real (flatten h (g x))).Perm (real (flatten h x)) ∧
        (real (flatten h (g x))).Pairwise (fun i j => (wordOrder n).le (f i) (f j)) := by
  let A := tree h (slot a)
  have aux (k : ℕ) (b : Wire) (hw : wd b + s * k ≤ wd a + s)
      (q : Val a → Val (.pair b (word (s * k))))
      (hq : DNet F a (.pair b (word (s * k))) q (2 * wd a + s)) :
      ∃ g, DNet F A A g (k * M + wd A) ∧
        ∀ x, 2 * (real (flatten h x)).length ≤ 2 ^ h →
          (real (flatten h (g x))).Perm (real (flatten h x)) ∧
          (real (flatten h (g x))).Pairwise (fun i j => (q i).2 ≤ (q j).2) := by
    induction k generalizing b with
    | zero =>
      refine ⟨_, (DNet.id F A).mono (by simp), fun x _ => ⟨.refl _, ?_⟩⟩
      exact List.pairwise_iff_getElem.mpr fun _ _ _ _ _ => (wordOrder 0).le_refl ()
    | succ k ih =>
      obtain ⟨u, hu, ho⟩ := split_word (s * k) s
      have key := hq.post ((Rewire.id b).par hu)
      have low := key.post (.assoc' _ _ _)
      obtain ⟨g, hg, ok⟩ := ih (.pair b (word s))
        (by simp only [wd, wd_word, Nat.mul_succ] at hw ⊢; omega) _ low
      have high := (key.comp (DNet.snd F b _)).comp (DNet.fst F (word s) (word (s * k)))
      obtain ⟨z, hz, ok'⟩ := H (fun x => (u (q x).2).1)
        (high.mono (by simp only [wd, wd_word, Nat.mul_succ] at hw ⊢; omega))
      refine ⟨_, (hg.comp hz).mono (by rw [Nat.succ_mul]; omega), fun x hx => ?_⟩
      obtain ⟨hp, hl⟩ := ok x hx
      have hst := ok' (g x) (by rwa [hp.length_eq])
      refine ⟨hst.1.trans hp, ?_⟩
      exact (combine hst hl).imp fun e => (ho _ _).mpr e
  have hw : s * (n / s + 1) ≤ wd a + s := by
    rw [Nat.mul_succ, Nat.mul_comm s]
    exact Nat.add_le_add_right ((Nat.div_mul_le_self n s).trans hn) s
  obtain ⟨key, hkey, ho⟩ := pad_key (Nat.lt_mul_div_succ n hs).le f hf
  have net := hkey.post ((Rewire.unit' _).comp (.swap _ _))
  obtain ⟨g, hg, ok⟩ := aux (n / s + 1) .unit (by simpa [wd] using hw) _ (net.mono (by omega))
  refine ⟨g, by simpa only [A, wd_tree, wd] using hg, fun x hx => ?_⟩
  obtain ⟨hp, hl⟩ := ok x hx
  exact ⟨hp, hl.imp (fun e => ho _ _ e)⟩

end OAI.LinearAlgebra.MatrixExponent.Radix
end

section
/-!
# Wider payloads at linear cost

Duplicate only the position tags when joining two verifiers. Payloads
go directly to the two networks, so recursive doubling incurs no
logarithmic factor in their total width.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Radix
open Tagged

variable {F : Type} [Field F] {a b c : Wire} {m w : ℕ}

private theorem common_input {k : Val (.pair a b) → Val .unit → F}
    (h : Net F (.pair a b) .unit k m) :
    ∃ v ≤ wd a + 2 * m, Net F (.pair a (.pair b b)) .unit
      (fun x z => k (x.1, x.2.1) z * k (x.1, x.2.2) z) v := by
  obtain ⟨u, hu, dup⟩ := DNet.dup F a
  have both := ((h.par h).pre (.middle a a b b)).post (.unit' _)
  have rin := (Rewire.assoc a (.pair b b) (.pair a a)).comp
    ((Rewire.id a).par (.swap _ _))
  have net := (((dup.par both).pre rin).post (.swap _ _)).trace
  refine ⟨u + (m + m), by omega, ?_⟩
  simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] using net

private theorem map_map (f : Val a → Val b) (g : Val b → Val c) (w : ℕ)
    (x : Val (tree w a)) : mapRows g w (mapRows f w x) = mapRows (fun y => g (f y)) w x := by
  induction w with
  | zero => rfl
  | succ w ih => exact Prod.ext (ih _) (ih _)

private theorem separate (w : ℕ) (a b : Wire) :
    Rewire (tree w (.pair a b)) (.pair (tree w a) (tree w b))
      (fun x => (mapRows (a := .pair a b) Prod.fst w x, mapRows (a := .pair a b) Prod.snd w x)) := by
  induction w with
  | zero => exact .id _
  | succ w ih => exact (ih.par ih).comp (.middle _ _ _ _)

private abbrev data (w : ℕ) (a : Wire) := Wire.pair (tree w a) (tree w a)
private abbrev tags (w : ℕ) := tree w (word w)

private def extract (w : ℕ) (a : Wire) (x : Val (inputs w a)) : Val (.pair (tags w) (data w a)) :=
  (mapRows (a := row w a) Prod.fst w x.2, x.1, mapRows (a := row w a) Prod.snd w x.2)

private theorem extract_wire (w : ℕ) (a : Wire) :
    Rewire (inputs w a) (.pair (tags w) (data w a)) (extract w a) :=
  ((Rewire.id _).par (separate w (word w) a)).comp <|
    (Rewire.assoc' _ _ _).comp <| ((Rewire.swap _ _).par (.id _)).comp (.assoc _ _ _)

private theorem extract_project (f : Val a → Val b) (w : ℕ) (x : Val (inputs w a)) :
    extract w b (project w f x) =
      ((extract w a x).1, mapRows f w (extract w a x).2.1, mapRows f w (extract w a x).2.2) := by
  simp only [extract, project, map_map, Prod.map, id_eq]

private theorem double (h : Net F (inputs w a) .unit (tag F w a) m) :
    ∃ v ≤ 2 ^ w * w + 2 * m, Net F (inputs w (.pair a a)) .unit (tag F w (.pair a a)) v := by
  obtain ⟨join, hj, he⟩ := (extract_wire w a).inverse
  obtain ⟨v, hv, net⟩ := common_input (h.pre hj)
  have sep := separate w a a
  have split := (sep.par sep).comp (.middle _ _ _ _)
  have hn := net.pre ((extract_wire w (.pair a a)).comp ((Rewire.id _).par split))
  refine ⟨v, by simpa [tags, wd_tree] using hv, ?_⟩
  convert hn using 1
  funext x y
  rw [tag_pair]
  congr 2 <;> exact (he _ _).mp (extract_project _ w x)

private theorem double_iter (h : Net F (inputs w a) .unit (tag F w a) m) (k : ℕ) :
    ∃ n, Net F (inputs w (tree k a)) .unit (tag F w (tree k a)) n ∧
      n + 2 ^ w * w ≤ 2 ^ k * (m + 2 ^ w * w) := by
  induction k with
  | zero => exact ⟨m, h, by simp⟩
  | succ k ih =>
    obtain ⟨v, hv, hc⟩ := ih
    obtain ⟨n, hn, g⟩ := double hv
    refine ⟨n, g, ?_⟩
    rw [pow_succ, mul_two, add_mul]
    omega

private theorem dyadic_cover {u v : ℕ} (hu : 1 ≤ u) (hv : u ≤ v) :
    ∃ k : ℕ, v ≤ 2 ^ k * u ∧ 2 ^ k * u ≤ 2 * v := by
  have hex : ∃ k : ℕ, v ≤ 2 ^ k * u :=
    ⟨v, (Nat.lt_two_pow_self.le).trans (by simpa using Nat.mul_le_mul_left (2 ^ v) hu)⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  cases he : Nat.find hex with
  | zero => simpa using (show u ≤ 2 * v by omega)
  | succ k =>
    have h := Nat.find_min hex (show k < Nat.find hex by omega)
    rw [pow_succ, mul_two, add_mul]
    omega

/-- Split the payload into a dyadic number of slices and pad the last
slice. The overhead is uniform in the ratio of the two widths. -/
theorem widen {u v : ℕ} (hw : 1 ≤ w) (hu : w ≤ u) (hv : u ≤ v) (ht : Tag F w u m) :
    ∃ n, Tag F w v n ∧ n * u ≤ 2 * v * m + 100 * 2 ^ w * v * u := by
  obtain ⟨k, h₁, h₂⟩ := dyadic_cover (hw.trans hu) hv
  obtain ⟨l, hl, hc⟩ := double_iter ht k
  obtain ⟨n, hn, net⟩ := tag_shrink (b := word v) (Batch.of_net hl 1)
    (by simpa only [wd_tree, wd_word] using h₁)
  refine ⟨n, ?_, ?_⟩
  · simpa only [power, mul_one, Tag] using (net.pre (.unit' _)).post (.unit' _)
  · simp only [wd_tree, wd_word, one_mul] at hn
    have hb : n ≤ 2 ^ k * m + 3 * 2 ^ w * (2 ^ k * u) := by
      have hw' := Nat.mul_le_mul_left (2 ^ k * 2 ^ w) hu
      ring_nf at hw' hn hc ⊢
      omega
    calc
      n * u ≤ (2 ^ k * m + 3 * 2 ^ w * (2 ^ k * u)) * u := Nat.mul_le_mul_right _ hb
      _ = (2 ^ k * u) * m + 3 * 2 ^ w * (2 ^ k * u) * u := by ring
      _ ≤ (2 * v) * m + 3 * 2 ^ w * (2 * v) * u := by gcongr
      _ ≤ _ := by ring_nf; omega

end OAI.LinearAlgebra.MatrixExponent.Radix
end

section
/-!
# The wide-record recursion

It is enough to install calls at the threshold width. Once the height
ratio `τ` and width ratio `Y` are fixed, take the threshold exponent
`A` large enough that `τ^A ≤ Y`. Every recursive call then still
meets the wide-record threshold. Slicing handles widths above it.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Radix

variable {F : Type} [Field F]

private theorem bounded_heights (A N : ℕ) :
    ∃ B : ℕ, ∀ h < N, ∃ m ≤ B, Tag F h (h ^ A) m := by
  induction N with
  | zero => exact ⟨0, by simp⟩
  | succ N ih =>
    obtain ⟨B, hB⟩ := ih
    obtain ⟨m, hm, _⟩ := Net.dense _ _ (Tagged.tag F N (word (N ^ A)))
    refine ⟨B + m, fun h hh => ?_⟩
    rcases (Nat.lt_succ_iff.mp hh).eq_or_lt with rfl | hn
    · exact ⟨m, by omega, hm⟩
    · obtain ⟨k, hk, ht⟩ := hB h hn
      exact ⟨k, by omega, ht⟩

private theorem widen_bound {D ζ : ℝ} (hD : 204 ≤ D) (hζ : 0 < ζ)
    {h u v m : ℕ} (hh : 1 ≤ h) (hu : h ≤ u) (hv : u ≤ v) (ht : Tag F h u m)
    (hm : (m : ℝ) ≤ (1 + D / 4) * (2 : ℝ) ^ h * u * (h : ℝ) ^ ζ) :
    ∃ n, Tag F h v n ∧ (n : ℝ) ≤ D * (2 : ℝ) ^ h * v * (h : ℝ) ^ ζ := by
  obtain ⟨n, hn, hc⟩ := widen hh hu hv ht
  refine ⟨n, hn, le_of_mul_le_mul_right (a := (u : ℝ)) ?_ (by exact_mod_cast (show 0 < u by omega))⟩
  have hr := Real.one_le_rpow (by exact_mod_cast hh : 1 ≤ (h : ℝ)) hζ.le
  calc
    (n : ℝ) * u ≤ 2 * v * m + 100 * (2 : ℝ) ^ h * v * u := by exact_mod_cast hc
    _ ≤ 2 * v * ((1 + D / 4) * (2 : ℝ) ^ h * u * (h : ℝ) ^ ζ) + 100 * (2 : ℝ) ^ h * v * u * (h : ℝ) ^ ζ :=
      add_le_add (mul_le_mul_of_nonneg_left hm (by positivity))
        (le_mul_of_one_le_right (by positivity) hr)
    _ = (102 + D / 2) * ((2 : ℝ) ^ h * v * (h : ℝ) ^ ζ * u) := by ring
    _ ≤ D * ((2 : ℝ) ^ h * v * (h : ℝ) ^ ζ * u) := by gcongr; linarith
    _ = _ := by ring

theorem wide_of_protocol (prot : Protocol F) : WideTag F := by
  intro ζ hζ
  obtain ⟨C, hC, prop⟩ := prot
  let τ := ((4 * C)⁻¹) ^ ζ⁻¹
  have ht : 0 < τ := by unfold τ; positivity
  have ht' : τ < 1 := Real.rpow_lt_one (by positivity) (inv_lt_one_of_one_lt₀ (by linarith))
    (inv_pos.mpr hζ)
  have hct : C * τ ^ ζ = 1 / 4 := by
    unfold τ
    rw [Real.rpow_inv_rpow (by positivity) hζ.ne']
    field_simp
  obtain ⟨Y, hY, J, rec⟩ := prop τ ht
  obtain ⟨a, ha⟩ := exists_pow_lt_of_lt_one hY ht'
  let A := a + J + 2
  have hA : 2 ≤ A := by omega
  have hratio : τ ^ A ≤ Y := (pow_le_pow_of_le_one ht.le ht'.le (show a ≤ A by omega)).trans ha.le
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (rec A (by omega) ζ hζ)
  obtain ⟨B, hB⟩ := bounded_heights (F := F) A N
  let D : ℝ := 204 + 4 * B
  have hD : 204 ≤ D := by unfold D; linarith
  refine ⟨A, hA, D, ?_⟩
  intro h
  induction h using Nat.strong_induction_on with
  | h h ih =>
    intro v hh hv
    have hh' : 1 ≤ (h : ℝ) := by exact_mod_cast hh
    have base : ∃ m, Tag F h (h ^ A) m ∧ (m : ℝ) ≤ (1 + D / 4) * (2 : ℝ) ^ h * (h : ℝ) ^ A * (h : ℝ) ^ ζ := by
      by_cases hsmall : h < N
      · obtain ⟨m, hm, hs⟩ := hB h hsmall
        refine ⟨m, hs, ?_⟩
        calc
          (m : ℝ) ≤ B := by exact_mod_cast hm
          _ ≤ (1 + D / 4) * 1 * 1 * 1 := by unfold D; linarith
          _ ≤ _ := by
            gcongr
            · exact one_le_pow₀ (by norm_num)
            · exact one_le_pow₀ hh'
            · exact Real.one_le_rpow hh' hζ.le
      obtain ⟨l, u, M, L, hl, hlt, hu, hsize, hM, make⟩ := hN h (le_of_not_gt hsmall)
      have hle : l < h := by
        exact_mod_cast hlt.trans_lt (mul_lt_of_lt_one_left (by linarith) ht')
      have hwide : l ^ A ≤ u := by
        have hp := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) l) hlt A
        rw [mul_pow] at hp
        exact_mod_cast hp.trans ((mul_le_mul_of_nonneg_right hratio (by positivity)).trans hu)
      obtain ⟨s, hs, hc⟩ := ih l hle u hl hwide
      obtain ⟨m, hm, htag⟩ := make s hs
      have hr : (l : ℝ) ^ ζ ≤ τ ^ ζ * (h : ℝ) ^ ζ := by
        rw [← Real.mul_rpow ht.le (by positivity)]
        exact Real.rpow_le_rpow (by positivity) hlt hζ.le
      have hcost : (L : ℝ) * s ≤ (D / 4) * (2 : ℝ) ^ h * (h : ℝ) ^ A * (h : ℝ) ^ ζ := by
        calc
          (L : ℝ) * s ≤ L * (D * (2 : ℝ) ^ l * u * (l : ℝ) ^ ζ) := mul_le_mul_of_nonneg_left hc (by positivity)
          _ = D * (L * (2 : ℝ) ^ l * u) * (l : ℝ) ^ ζ := by ring
          _ ≤ D * (C * (2 : ℝ) ^ h * (h : ℝ) ^ A) * (τ ^ ζ * (h : ℝ) ^ ζ) := by gcongr
          _ = D * (C * τ ^ ζ) * (2 : ℝ) ^ h * (h : ℝ) ^ A * (h : ℝ) ^ ζ := by ring
          _ = _ := by rw [hct]; ring
      refine ⟨m, htag, ?_⟩
      calc
        (m : ℝ) ≤ M + (L : ℝ) * s := by exact_mod_cast hm
        _ ≤ _ := by linarith only [hM, hcost]
    obtain ⟨m, htag, hm⟩ := base
    exact widen_bound hD hζ hh (Nat.le_pow (by omega)) hv htag (by simpa using hm)

end OAI.LinearAlgebra.MatrixExponent.Radix
end
