import OAI.LinearAlgebra.MatrixExponent.Transport.Table
import OAI.LinearAlgebra.MatrixExponent.Install.Weight
import OAI.LinearAlgebra.MatrixExponent.Tagged.Array
import OAI.LinearAlgebra.MatrixExponent.Tagged.SortBack
import OAI.LinearAlgebra.MatrixExponent.Transport.System
import OAI.LinearAlgebra.MatrixExponent.Install.SumOut
import OAI.LinearAlgebra.MatrixExponent.AdjacentDuplicates
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Preparing the exterior records and the permutation

Decode the proposed tags as binary addresses. A fixed permutation of
the source list reconciles enumeration order with the address coding.
Only the tags are sorted to validate the permutation. Payloads are
padded and moved by fixed wiring.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transport

open Coloring
variable {F : Type} [Field F] {h n W z : ℕ}

private abbrev Row (h n : ℕ) := Tagged.row h (word n)
private abbrev Rows (h n : ℕ) := tree h (Row h n)
private abbrev Both (h n : ℕ) := Wire.pair (Rows h n) (Rows h n)
private abbrev Array (h n : ℕ) := B h → Val (Row h n)
private abbrev Table (h n : ℕ) := Layout (Row h n) (Rows h n) (B h)

private def names (y : Array h n) (i : B h) := Control.index h (y i).1

private theorem names_iff (y : Array h n) :
    ((List.ofFn y).map Prod.fst).Nodup ↔ Function.Bijective (names y) := by
  rw [List.map_ofFn, List.nodup_ofFn, ← Finite.injective_iff_bijective]
  constructor
  · exact fun hy => (Control.index h).injective.comp hy
  · exact fun hy i j he => hy (congrArg (Control.index h) he)

private theorem indexed_perm (x y : Array h n) (π : Equiv.Perm (B h)) (hx : names x = π) :
    (List.ofFn y).Perm (List.ofFn x) ↔
      ((List.ofFn y).map Prod.fst).Nodup ∧ ∀ i, (y i).2 = (x (π.symm (names y i))).2 := by
  have ident (i j) : (y i).1 = (x j).1 ↔ π.symm (names y i) = j := by
    rw [Equiv.symm_apply_eq, ← hx]
    exact (Control.index h).injective.eq_iff.symm
  constructor
  · intro he
    have hn := (names_iff x).mpr (hx.symm ▸ π.bijective)
    refine ⟨(he.symm.map _).nodup hn, fun i => ?_⟩
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp (he.subset (List.mem_ofFn.mpr ⟨i, rfl⟩))
    rw [(ident i j).mp (congrArg Prod.fst hj.symm), hj]
  · rintro ⟨hn, hm⟩
    apply ((hn.of_map Prod.fst).subperm ?_).perm_of_length_le (by simp)
    intro v hv
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
    exact List.mem_ofFn.mpr ⟨_, Prod.ext ((ident i _).mpr rfl).symm (hm i).symm⟩

private theorem source_perm (L : Table h n) (hL : ∀ x, List.ofFn (L.read x) = flatten h x) :
    ∃ π : Equiv.Perm (B h), ∀ x : Val (tree h (word n)), names (L.read (Tagged.label h x)) = π := by
  have he (x : Val (tree h (word n))) :
      (List.ofFn (L.read (Tagged.label h x))).map Prod.fst = flatten h (Tagged.indices h) := by
    rw [hL, Tagged.label_tags]
  let x₀ := (bits (tree h (word n))).symm (fun _ => false)
  have hn := (names_iff (L.read (Tagged.label h x₀))).mp (by rw [he]; exact Tagged.indices_nodup _)
  refine ⟨Equiv.ofBijective _ hn, fun x => ?_⟩
  have hh := (he x).trans (he x₀).symm
  simp only [List.map_ofFn] at hh
  exact congrArg (fun f => Control.index h ∘ f) (List.ofFn_injective hh)

private abbrev Embed (W z n : ℕ) := slots (word n) ↪ Fin W × Fin z

private def pad (e : Embed W z n) (x : Val (word n)) (j : Fin W × Fin z) :=
  if h : ∃ i, e i = j then bits (word n) x h.choose else false

private theorem pad_injective (e : Embed W z n) : Function.Injective (pad e) := by
  have atIndex (x : Val (word n)) (i : slots (word n)) : pad e x (e i) = bits (word n) x i := by
    have hp : ∃ j, e j = e i := ⟨i, rfl⟩
    rw [pad, dite_eq_left hp, e.injective hp.choose_spec]
  intro x y he
  apply (bits (word n)).injective
  funext i
  rw [← atIndex, ← atIndex, he]

private def packets (e : Embed W z n) (x : B h → Val (word n)) (i : Site h) : Data W z :=
  if hi : i.val < 2 ^ h then pad e (x ⟨i.val, hi⟩) else fun _ => false

private theorem compare_packets (e : Embed W z n) (x y : B h → Val (word n)) (σ : B h → B h) :
    (∀ i, packets e x i = packets e y (Routing.inflate h σ i)) ↔ ∀ i, x i = y (σ i) := by
  have lo (x : B h → Val (word n)) (i : B h) : packets e x (Routing.lowerHalf h i) = pad e (x i) := by
    simp [packets, Routing.lowerHalf, i.isLt]
  have lower (i : B h) : Routing.inflate h σ (Routing.lowerHalf h i) = Routing.lowerHalf h (σ i) := by
    simp [Routing.inflate, Routing.lowerHalf, i.isLt]
  constructor
  · intro he i
    apply pad_injective e
    simpa only [lower, lo] using he (Routing.lowerHalf h i)
  · intro he i
    by_cases hi : i.val < 2 ^ h
    · rw [show i = Routing.lowerHalf h ⟨i.val, hi⟩ from rfl, lower, lo, lo, he]
    · simp [Routing.inflate, packets, hi]

private abbrev Payload (h W z : ℕ) := Format.pair (Perm h) (.pair (Packet h W z) (Packet h W z))

private def routeData (e : Embed W z n) (L : Table h n) (π : Equiv.Perm (B h))
    (x : Val (Both h n)) : (Payload h W z).obj :=
  (names (L.read x.2), packets e (fun i => (L.read x.2 i).2),
    packets e (fun i => (L.read x.1 (π.symm i)).2))

private theorem read_bit (L : Table h n) (x : slots (Rows h n) → Bool)
    (i : B h) (j : slots (Row h n)) :
    bits (Row h n) (L.read ((bits (Rows h n)).symm x) i) j = x (L.positions (i, j)) := by
  simp [Layout.read]

private theorem packets_depend (e : Embed W z n) (L : Table h n)
    (f : slots (Rows h n) → slots (Both h n)) (r : B h → B h) :
    Install.Depends (fun x (ij : Site h × (Fin W × Fin z)) =>
      packets e (fun i => (L.read ((bits (Rows h n)).symm (x ∘ f)) (r i)).2) ij.1 ij.2) 1 := by
  rintro ⟨i, j⟩
  by_cases hi : i.val < 2 ^ h
  · by_cases hj : ∃ k, e k = j
    · let k := f (L.positions (r ⟨i.val, hi⟩, .inr hj.choose))
      refine ⟨{k}, by simp, fun x y he => ?_⟩
      simp only [packets, dite_eq_left hi, pad, dite_eq_left hj]
      have eq (x : slots (Both h n) → Bool) :
          bits (word n) (L.read ((bits (Rows h n)).symm (x ∘ f)) (r ⟨i.val, hi⟩)).2 hj.choose = x k :=
        read_bit L _ _ (.inr hj.choose)
      rw [eq, eq, he k (by simp)]
    · exact ⟨∅, by simp, fun _ _ _ => by simp [packets, hi, pad, hj]⟩
  · exact ⟨∅, by simp, fun _ _ _ => by simp [packets, hi]⟩

private theorem data_circuit (e : Embed W z n) (L : Table h n) (π : Equiv.Perm (B h)) :
    Circuit F (.wire (Both h n)) (Payload h W z) (routeData e L π)
      (wd (Both h n) + Install.localCost 1 * (Payload h W z).width) := by
  have hc : Install.Depends ((Payload h W z).code ∘ routeData e L π ∘ (bits (Both h n)).symm) 1 := by
    rintro (⟨i, j⟩ | ij | ij)
    · let k : slots (Both h n) := .inr (L.positions (i, .inl j))
      refine ⟨{k}, by simp, fun x y he => ?_⟩
      have eq (x : slots (Both h n) → Bool) :
          (Format.addr h).code (names (L.read ((bits (Rows h n)).symm (x ∘ Sum.inr))) i) j = x k := by
        change ((Control.decode h).symm (Control.index h
          (L.read ((bits (Rows h n)).symm (x ∘ Sum.inr)) i).1)) j = x k
        simp only [Control.decode, Equiv.symm_trans_apply, Equiv.symm_apply_apply]
        exact read_bit L _ _ (.inl j)
      exact (eq x).trans ((he k (by simp)).trans (eq y).symm)
    · exact packets_depend e L Sum.inr id ij
    · exact packets_depend e L Sum.inl π.symm ij
  have hn := hc.bnet F
  rw [card_slots] at hn
  exact hn

private theorem wire_circuit {a b : Wire} {f : Val a → Val b} {m : ℕ} (hf : DNet F a b f m) :
    Circuit F (.wire a) (.wire b) f m := by
  apply Circuit.of_dnet (.refl _) (.refl _) hf
  intro x
  simp [Format.wire]

private def labels (h n : ℕ) (x : Val (input h n)) : Val (Both h n) :=
  (Tagged.label h x.1, x.2)

private def check (h n : ℕ) (x : Val (Both h n)) := decide (((flatten h x.2).map Prod.fst).Nodup)

private theorem check_circuit (F : Type) [Field F] (h n : ℕ) :
    Circuit F (.wire (Both h n)) .bit (check h n)
      (wd (Both h n) + 2 ^ h * wd (Row h n) + 400 * 2 ^ h * (h + 1) ^ 2 * (h + 1)) := by
  have tags := Tagged.mapRows_net (DNet.fst F (word h) (word n)) h
  have readTags := (DNet.snd F (Rows h n) (Rows h n)).comp tags
  have hc := readTags.comp (nodup_net F h h)
  simp only [Tagged.flatten_mapRows] at hc
  exact wire_circuit hc

private theorem compiled (e : Embed W z n) (L : Table h n) (π : Equiv.Perm (B h)) (hv : n ≤ W * z) :
    Circuit F (.wire (input h n)) (Exterior h W z)
      (fun x => (check h n (labels h n x), routeData e L π (labels h n x)))
      (1000000 * 2 ^ h * ((h + 1) ^ 4 + W * z)) := by
  have src := wire_circuit ((Tagged.label_net F h (word n)).par (DNet.id F (Rows h n)))
  have out := (check_circuit F h n).pair (data_circuit (F := F) e L π)
  apply (src.comp out).mono
  have hw : (Format.wire (Both h n)).width = wd (Both h n) := card_slots _
  have hp : (Payload h W z).width = 2 ^ h * h + 2 ^ (h + 1) * (W * z) + 2 ^ (h + 1) * (W * z) := by
    simp only [Format.width_pair, Format.width_vec, Format.width_addr]
    change 2 ^ h * h + (2 ^ (h + 1) * Fintype.card (Fin W × Fin z) +
      2 ^ (h + 1) * Fintype.card (Fin W × Fin z)) = _
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, add_assoc]
  have size := Nat.mul_le_mul_left (2 ^ h) hv
  simp only [hw, hp, wd_tree, wd, wd_word, Install.localCost]
  ring_nf at size ⊢
  omega

theorem prepare (F : Type) [Field F] (h n W z : ℕ) (hv : n ≤ W * z) :
    ∃ f, Circuit F (.wire (input h n)) (Exterior h W z) f
      (1000000 * 2 ^ h * ((h + 1) ^ 4 + W * z)) ∧ Prepared F f := by
  classical
  let e : Embed W z n :=
    ((Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb (by simpa using hv))).trans
      finProdFinEquiv.symm.toEmbedding
  obtain ⟨L, hL⟩ := Layout.exists_tree (Row h n) h
  obtain ⟨π, hπ⟩ := source_perm L hL
  refine ⟨_, compiled e L π hv, fun x => ?_⟩
  let y := L.read x.2
  let v := L.read (Tagged.label h x.1)
  have hcheck : check h n (labels h n x) = true ↔ ((List.ofFn y).map Prod.fst).Nodup := by
    simp only [check, labels, y, hL]
    exact decide_eq_true_iff
  constructor
  · exact fun hc => (names_iff y).mp (hcheck.mp hc)
  · have eq : (flatten h x.2).Perm (flatten h (Tagged.label h x.1)) ↔
        check h n (labels h n x) = true ∧
          ∀ i, packets e (fun j => (y j).2) i =
            packets e (fun j => (v (π.symm j)).2) (Routing.inflate h (names y) i) := by
      rw [compare_packets, hcheck, ← hL, ← hL]
      exact indexed_perm v y π (hπ _)
    unfold Tagged.tag Tagged.permuted
    congr 1
    exact propext eq

end OAI.LinearAlgebra.MatrixExponent.Transport
end

/-! # Naming the two endpoints of a transport -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transport
open Install

structure Book (h p z : ℕ) where
  g : ℕ
  b : ℕ
  pos : Port h p ↪ Idx g × Idx b

namespace Book

variable {h p z : ℕ} (B : Book h p z)

def field : Unit ⊕ slots (word B.b) ⊕ Fin z ≃ Fin (1 + B.b + z) :=
  Fintype.equivOfCardEq (by simp [Nat.add_assoc])

abbrev grid : Grid where
  g := B.g
  b := B.b
  r := 1 + B.b + z
  orientation := B.field (.inl ())
  ids i := B.field (.inr (.inl i))
  disjoint _ he := Sum.inr_ne_inl (B.field.injective he)

def atSlot (v : Idx B.g × Idx B.b) : Option (Port h p) :=
  if hit : ∃ i, B.pos i = v then some hit.choose else none

def src (a : Orders h p) (i : Port h p) : Idx B.b :=
  (B.pos (if (a i).2.1 then (a i).2.2 else i)).2

def data (a : Orders h p) (c : Site h → Channels p z) (i : Port h p) :
    Fin (1 + B.b + z) → Bool :=
  Sum.elim (fun _ => (a i).2.1)
    (Sum.elim ((Control.decode B.b).symm (B.src a i)) (fun t => c i.1 (i.2, t))) ∘ B.field.symm

def render (a : Orders h p) (c : Site h → Channels p z) : B.grid.Ports → Bool
  | (j, .inl k) => (B.atSlot (j, k)).elim false (fun i => (a i).1)
  | (j, .inr (k, v)) => (B.atSlot (j, k)).elim false (fun i => B.data a c i v)

def compatible (f : Port h p → ℕ) : Prop :=
  ∀ i j, f i = f j → (B.pos i).1 = (B.pos j).1

end Book
end OAI.LinearAlgebra.MatrixExponent.Transport
end

section
/-!
# From configured wires to grouped endpoint checks

A transport is identified by the position of its source within the
group. The two oriented ends have the same identifier, and validity
of the commands makes each oriented identifier unique.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Transport.Book
open Install

variable {h p z : ℕ} (B : Book h p z) {g : Port h p → ℕ} {a : Orders h p}
variable (c : Site h → Channels p z)

private theorem at_pos (i : Port h p) : B.atSlot (B.pos i) = some i := by
  have hn : ∃ j, B.pos j = B.pos i := ⟨i, rfl⟩
  rw [atSlot, dite_eq_left hn, B.pos.injective hn.choose_spec]

private theorem marked_iff (j : Idx B.g) (k : Idx B.b) :
    k ∈ marked (B.grid.block (B.render a c) j) ↔ ∃ i ∈ Enabled a, B.pos i = (j, k) := by
  rw [mem_marked]
  change (B.atSlot (j, k)).elim false (fun i => (a i).1) = true ↔ _
  constructor
  · unfold atSlot
    split
    · rename_i hk
      exact fun hi => ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, hk.choose_spec⟩
    · simp
  · rintro ⟨i, hi, he⟩
    rw [← he, at_pos]
    exact (Finset.mem_filter.mp hi).2

private theorem payload_eq {i : Port h p} {j : Idx B.g} {k : Idx B.b} (he : B.pos i = (j, k)) :
    payload (B.grid.block (B.render a c) j) k = B.data a c i := by
  funext t
  change (B.atSlot (j, k)).elim false (fun i => B.data a c i t) = _
  rw [← he, at_pos]
  rfl

private theorem data_id (i : Port h p) : B.grid.idOf (B.data a c i) = B.src a i := by
  have he : B.data a c i ∘ B.grid.ids = (Control.decode B.b).symm (B.src a i) := by
    funext t
    simp [grid, data, Function.comp_def]
  unfold Grid.idOf
  rw [he]
  exact Equiv.apply_symm_apply _ _

private theorem data_orientation (i : Port h p) :
    B.data a c i B.grid.orientation = (a i).2.1 := by simp [data]

private theorem same_src (hv : Valid g a) {i : Port h p} (hi : i ∈ Enabled a) :
    B.src a (a i).2.2 = B.src a i := by
  obtain ⟨_, he, ht, _⟩ := hv i hi
  simp only [src, ht, he]
  cases (a i).2.1 <;> rfl

private theorem unique_end (hc : B.compatible g) (hv : Valid g a) {i j : Port h p}
    (hi : i ∈ Enabled a) (hj : j ∈ Enabled a) (he : (B.pos i).1 = (B.pos j).1)
    (hd : B.src a i = B.src a j) (ho : (a i).2.1 = (a j).2.1) : i = j := by
  obtain ⟨_, hi', _, hgi⟩ := hv i hi
  obtain ⟨_, hj', _, hgj⟩ := hv j hj
  unfold src at hd
  rw [ho] at hd
  cases hjf : (a j).2.1
  · simp [hjf] at hd
    exact B.pos.injective (Prod.ext he hd)
  · simp [hjf] at hd
    have hh := (hc _ _ hgi).trans (he.trans (hc _ _ hgj).symm)
    rw [← hi', ← hj', B.pos.injective (Prod.ext hh hd)]

private theorem total :
    ∑ j, (marked (B.grid.block (B.render a c) j)).card = (Enabled a).card := by
  have he (j) : (marked (B.grid.block (B.render a c) j)).card =
      ((Enabled a).filter fun i => (B.pos i).1 = j).card := by
    symm
    refine Finset.card_bij (fun i _ => (B.pos i).2) ?_ ?_ ?_
    · intro i hi
      obtain ⟨hi, hh⟩ := Finset.mem_filter.mp hi
      exact (B.marked_iff c _ _).mpr ⟨i, hi, Prod.ext hh rfl⟩
    · intro i hi k hk e
      exact B.pos.injective (Prod.ext ((Finset.mem_filter.mp hi).2.trans
        (Finset.mem_filter.mp hk).2.symm) e)
    · intro k hk
      obtain ⟨i, hi, eq⟩ := (B.marked_iff c _ _).mp hk
      exact ⟨i, Finset.mem_filter.mpr ⟨hi, congrArg Prod.fst eq⟩, congrArg Prod.snd eq⟩
  simp only [he]
  exact (Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_univ ((B.pos i).1))).symm

private theorem aligned (hc : B.compatible g) (hv : Valid g a) (j : Idx B.g) :
    Aligned B.grid.orientation B.grid.idOf (B.grid.block (B.render a c) j) := by
  constructor
  · intro k hk
    obtain ⟨i, hi, he⟩ := (B.marked_iff c _ _).mp hk
    rw [B.payload_eq c he, data_id]
    have ep : (B.pos i).1 = j := congrArg Prod.fst he
    apply (B.marked_iff c _ _).mpr
    unfold src
    split
    · obtain ⟨hm, _, _, hg⟩ := hv i hi
      exact ⟨_, hm, Prod.ext ((hc _ _ hg).trans ep) rfl⟩
    · exact ⟨i, hi, Prod.ext ep rfl⟩
  · intro k hk l hl he
    obtain ⟨u, hu, eu⟩ := (B.marked_iff c _ _).mp hk
    obtain ⟨v, hv', ev⟩ := (B.marked_iff c _ _).mp hl
    dsimp only at he
    rw [B.payload_eq c eu, B.payload_eq c ev, data_id, data_id, data_orientation,
      data_orientation] at he
    have eq := B.unique_end hc hv hu hv' ((congrArg Prod.fst eu).trans (congrArg Prod.fst ev).symm)
      (Prod.mk.inj he).1 (Prod.mk.inj he).2
    rw [eq, ev] at eu
    exact (congrArg Prod.snd eu).symm

private theorem data_flip (i j : Port h p) :
    B.data a c j = flip B.grid.orientation (B.data a c i) ↔
      (a j).2.1 = !(a i).2.1 ∧ B.src a j = B.src a i ∧
        ∀ t, c i.1 (i.2, t) = c j.1 (j.2, t) := by
  constructor
  · intro hd
    refine ⟨?_, (Control.decode B.b).symm.injective ?_, fun t => ?_⟩
    · simpa [data, Install.flip, grid] using congrFun hd (B.field (.inl ()))
    · funext k
      simpa [data, Install.flip, grid] using congrFun hd (B.field (.inr (.inl k)))
    · simpa [data, Install.flip, grid] using (congrFun hd (B.field (.inr (.inr t)))).symm
  · rintro ⟨ho, he, hc⟩
    funext k
    obtain ⟨_ | _ | _, rfl⟩ := B.field.surjective k <;> simp [data, Install.flip, grid, ho, he, hc]

private theorem joined (hc : B.compatible g) (hv : Valid g a) :
    (∀ j, Closed B.grid.orientation (B.grid.block (B.render a c) j)) ↔ Joins a c := by
  constructor
  · intro hs i hi
    have hm := (B.marked_iff c (B.pos i).1 (B.pos i).2).mpr ⟨i, hi, rfl⟩
    obtain ⟨k, hk, hh⟩ := hs _ _ hm
    obtain ⟨j, hj, ej⟩ := (B.marked_iff c _ _).mp hk
    rw [B.payload_eq c ej, B.payload_eq c (show B.pos i = ((B.pos i).1, (B.pos i).2) from rfl)] at hh
    obtain ⟨ho, he, hd⟩ := (B.data_flip c i j).mp hh
    obtain ⟨hm, _, ho', hg⟩ := hv i hi
    have eq := B.unique_end hc hv hj hm ((congrArg Prod.fst ej).trans (hc _ _ hg).symm)
      (he.trans (B.same_src hv hi).symm) (ho.trans ho'.symm)
    exact eq ▸ hd
  · intro hs j k hk
    obtain ⟨i, hi, he⟩ := (B.marked_iff c _ _).mp hk
    obtain ⟨hm, _, ho, hg⟩ := hv i hi
    have ep : (B.pos i).1 = j := congrArg Prod.fst he
    have eq : B.pos (a i).2.2 = (j, (B.pos (a i).2.2).2) :=
      Prod.ext ((hc _ _ hg).trans ep) rfl
    refine ⟨_, (B.marked_iff c _ _).mpr ⟨_, hm, eq⟩, ?_⟩
    rw [B.payload_eq c eq, B.payload_eq c he]
    exact (B.data_flip c _ _).mpr ⟨ho, B.same_src hv hi, hs i hi⟩

open Classical in
theorem rendered (B : Book h p z) (F : Type) [Field F] {g : Port h p → ℕ} {a : Orders h p}
    (hc : B.compatible g) (hv : Valid g a) (c : Site h → Channels p z) :
    B.grid.Valid (Enabled a).card (B.render a c) ∧
      B.grid.close F (B.render a c) = if Joins a c then 1 else 0 := by
  refine ⟨⟨B.aligned c hc hv, (B.total c).le⟩, ?_⟩
  unfold Grid.close
  congr 1
  exact propext (B.joined c hc hv)

end OAI.LinearAlgebra.MatrixExponent.Transport.Book
end

/-!
# Installing a transport record

Look up the fixed slot numbers in parallel. Each remaining output bit
uses at most two input bits. An unused position receives only zeros.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transport.Book
open Coloring Install

variable {h p z : ℕ} (B : Book h p z) (A : Format)

private abbrev Input (h p z : ℕ) (A : Format) := (Controls h p A).pair (Buffer h p z)
private abbrev Dest (h p : ℕ) := Format.pair (.addr (h + 1)) (.addr p)
private abbrev Work := (Input h p z A).pins ⊕ (Port h p × slots (word B.b))

private def pin (u : Port h p × (Dest h p).pins) : (Input h p z A).pins :=
  .inl (u.1.1, .inr (u.1.2, .inr (.inr u.2)))

private def number (i : Port h p) := (Control.decode B.b).symm (B.pos i).2

private def mark (i : Port h p) : Work B A := .inl (.inl (i.1, .inr (i.2, .inl ())))
private def dir (i : Port h p) : Work B A := .inl (.inl (i.1, .inr (i.2, .inr (.inl ()))))
private def channel (i : Port h p) (t : Fin z) : Work B A := .inl (.inr (i.1, i.2, t))

private def emit (x : Work B A → Bool) : B.grid.Ports → Bool
  | (j, .inl k) => (B.atSlot (j, k)).elim false (fun i => x (mark B A i))
  | (j, .inr (k, v)) => (B.atSlot (j, k)).elim false fun i =>
    Sum.elim (fun _ => x (dir B A i))
      (Sum.elim (fun t => if x (dir B A i) then x (.inr (i, t)) else number B i t)
        (fun t => x (channel B A i t))) (B.field.symm v)

private theorem emit_local : Depends (emit B A) 2 := by
  classical
  rintro ⟨j, k | ⟨k, v⟩⟩ <;> simp only [emit] <;> cases B.atSlot (j, k)
  · exact ⟨∅, by simp, fun _ _ _ => rfl⟩
  · rename_i i
    exact ⟨{mark B A i}, by simp, fun _ _ he => he _ (by simp)⟩
  · exact ⟨∅, by simp, fun _ _ _ => rfl⟩
  · rename_i i
    rcases B.field.symm v with _ | t | t
    · exact ⟨{dir B A i}, by simp, fun _ _ he => he _ (by simp)⟩
    · refine ⟨{dir B A i, .inr (i, t)}, Finset.card_le_two, fun x y he => ?_⟩
      simp only [Option.elim_some, Sum.elim_inr, Sum.elim_inl]
      rw [he (dir B A i) (by simp), he (.inr (i, t)) (by simp)]
    · exact ⟨{channel B A i t}, by simp, fun _ _ he => he _ (by simp)⟩

private def prepare (x : (Input h p z A).pins → Bool) : Work B A → Bool :=
  Sum.elim x (fun u => number B ((Dest h p).code.symm (fun k => x (pin A (u.1, k)))) u.2)

private theorem emit_eq (x : (Input h p z A).pins → Bool) :
    emit B A (prepare B A x) =
      B.render (commands ((Input h p z A).code.symm x).1) ((Input h p z A).code.symm x).2 := by
  let a := commands ((Input h p z A).code.symm x).1
  let c := ((Input h p z A).code.symm x).2
  change emit B A (prepare B A x) = B.render a c
  funext u
  rcases u with ⟨j, k | ⟨k, v⟩⟩
  · rfl
  · simp only [emit, render]
    cases B.atSlot (j, k) with
    | none => rfl
    | some i =>
      simp only [Option.elim_some, data, Function.comp_apply]
      rcases B.field.symm v with _ | t | t
      · rfl
      · change (if (a i).2.1 then number B (a i).2.2 t else number B i t) =
          number B (if (a i).2.1 then (a i).2.2 else i) t
        split <;> rfl
      · rfl

theorem render_net (F : Type) [Field F] :
    Circuit F ((Controls h p A).pair (Buffer h p z)) (raw B.grid.Ports)
      (fun x => B.render (commands x.1) x.2)
      (1000000 * (2 ^ (h + 1 + p) * (1 + h + 1 + p) ^ 3 * (1 + B.b) +
        ((Controls h p A).pair (Buffer h p z)).width + Fintype.card B.grid.Ports)) := by
  have hi : Fintype.card (Port h p) = 2 ^ (h + 1 + p) := by simp [Fintype.card_prod, pow_add]
  have hk : Fintype.card (Dest h p).pins = h + 1 + p := by
    change (Dest h p).width = _
    rw [Format.width_pair, Format.width_addr, Format.width_addr]
  have hj : Fintype.card (slots (word B.b)) = B.b := by simp
  have get := BNet.table F (Port h p) (Dest h p).pins (slots (word B.b)) (h + 1 + p)
    hi hk (fun x => number B ((Dest h p).code.symm x))
  have left := (BNet.id F (Input h p z A).pins).pair (get.pull (pin (z := z) A))
  have net := left.comp ((emit_local B A).bnet F)
  unfold Circuit
  convert net.mono (n := 1000000 * (2 ^ (h + 1 + p) * (1 + h + 1 + p) ^ 3 * (1 + B.b) +
    (Input h p z A).width + Fintype.card B.grid.Ports)) (by
      simp only [Fintype.card_sum, Fintype.card_prod, hi, hk, hj, localCost, Format.width]
      ring_nf
      omega) using 1
  funext x
  exact (emit_eq B A x).symm

end OAI.LinearAlgebra.MatrixExponent.Transport.Book
end

section
/-! # Total cost allowance for one layer before smaller transports -/

namespace OAI.LinearAlgebra.MatrixExponent.Transport

open Coloring

noncomputable def System.bill {F : Type} {h p W z : ℕ} (S : System F h p W z) (B : Book h p z)
    (n m r : ℕ) : ℕ :=
  10000000 * (m + wd (input h n) + S.frame.width + S.latent.width +
    ((Perm h).pair S.selector).width + 2 ^ (h + 1 + p) * (1 + h + 1 + p) ^ 3 * (1 + B.b) +
    Fintype.card B.grid.Ports + 2 ^ (h + 1) * (r + (h + 1) ^ 4 + W * z) + 1)

end OAI.LinearAlgebra.MatrixExponent.Transport
end

section
/-!
# Joining local weighted kernels

The selector and the core payloads are hidden variables. Invalid
permutation inputs are killed by the exterior check. On a valid input
each surviving term has well-formed endpoints, so closing the grid
implements exactly the prescribed wire equalities.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Transport

open Coloring Install Classical

variable {F : Type} [Field F] {h p W z C n m r : ℕ}
    (S : System F h p W z) (B : Book h p z)

private noncomputable def output (x : S.frame.obj) : B.grid.Ports → Bool :=
  B.render (commands x.2.1) x.2.2

private theorem semantics (hc : B.compatible S.group) (hs : S.Correct C)
    {prep : Val (input h n) → (Exterior h W z).obj} (hp : Prepared F prep)
    (x : Val (input h n)) :
    (∀ l, S.coeff (S.configure prep (x, l)) ≠ 0 →
      B.grid.Valid (C * W * 2 ^ h) (output S B (S.configure prep (x, l)))) ∧
    Tagged.tag F h (word n) x () =
      ∑ l : S.latent.obj, S.coeff (S.configure prep (x, l)) *
        B.grid.close F (output S B (S.configure prep (x, l))) := by
  obtain ⟨hb, he⟩ := hp x
  by_cases hv : (prep x).1 = true
  swap
  · simp only [System.coeff, System.configure]
    simp [he, hv]
  let σ := Equiv.ofBijective (prep x).2.1 (hb hv)
  let a := (prep x).2.2.1
  let b := (prep x).2.2.2
  obtain ⟨valid, value⟩ := hs σ a b
  let run (l : S.latent.obj) := S.dispatch (σ, S.selector.code.symm l.1)
  have score (l : S.latent.obj) :
      S.coeff (S.configure prep (x, l)) = S.value (run l) a b l.2 := by
    exact ite_eq_left hv
  have showPorts (l : S.latent.obj) :
      output S B (S.configure prep (x, l)) = B.render (commands (run l)) l.2 := rfl
  have ok (l : S.latent.obj) (hl : S.value (run l) a b l.2 ≠ 0) :
      B.grid.Valid (C * W * 2 ^ h) (B.render (commands (run l)) l.2) ∧
      B.grid.close F (B.render (commands (run l)) l.2) =
        if Joins (commands (run l)) l.2 then 1 else 0 := by
    obtain ⟨ht, hw⟩ := valid _ _ hl
    obtain ⟨⟨hg, hs⟩, he⟩ := B.rendered F hc ht l.2
    exact ⟨⟨hg, hs.trans hw⟩, he⟩
  simp only [score, showPorts]
  refine ⟨fun l hl => (ok l hl).1, ?_⟩
  simp only [hv, true_and] at he
  rw [he]
  trans ∑ l : S.latent.obj, S.value (run l) a b l.2 * (if Joins (commands (run l)) l.2 then 1 else 0)
  · rw [Fintype.sum_prod_type]
    exact value
  · apply Finset.sum_congr rfl
    intro l _
    by_cases hl : S.value (run l) a b l.2 = 0
    · simp [hl]
    · rw [(ok l hl).2]

theorem assemble (hc : B.compatible S.group) (hv : n ≤ W * z) (hs : S.Correct C)
    (hq : Circuit F ((Perm h).pair S.selector) (Controls h p S.config) S.dispatch m)
    (hk : Weight F S.localWeight r) :
    ∃ t ≤ S.bill B n m r, B.grid.Open F h n t (C * W * 2 ^ h) := by
  obtain ⟨f, hf, hp⟩ := prepare F h n W z hv
  have compute := S.configure_net hf hq
  have weight := (S.coeff_net hk).pre compute
  have proj := Circuit.project (F := F) (A := S.frame) (D := S.terminals)
    (f := Prod.snd) Sum.inr (fun _ _ => rfl)
  have output := (compute.comp proj).comp (B.render_net S.config F)
  obtain ⟨t, ht, net⟩ := emit B.grid S.latent weight output
    (fun x => (semantics S B hc hs hp x).1) (fun x => (semantics S B hc hs hp x).2)
  refine ⟨t, ht.trans ?_, net⟩
  simp only [System.bill, Format.width_pair, pow_succ]
  ring_nf
  omega

end OAI.LinearAlgebra.MatrixExponent.Transport
end

section
/-!
# Installing the grouped protocol

The slot book and the exponent in the cost bound are independent of
all input records. The height of the address and that of the payload
have separate polynomial costs.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Transport
open Coloring Install

variable {F : Type} {h p W z n b m r : ℕ}

private theorem book (f : Port h p → ℕ) (hb : 1 ≤ b) (hb' : b ≤ h)
    (hs : ∀ i, (Finset.univ.filter (fun k => f k = i)).card ≤ 2 ^ (b - 1)) :
    ∃ B : Book h p z, B.compatible f ∧ B.g = h + p + 2 - b ∧ B.b = b := by
  have hcard : Fintype.card (Port h p) ≤ 2 ^ (h + p + 2 - b) * 2 ^ (b - 1) := by
    simp only [Fintype.card_prod, Fintype.card_fin, ← pow_add]
    rw [show h + p + 2 - b + (b - 1) = h + 1 + p by omega]
  have hh := exists_bins f _ _ hs (Nat.two_pow_pos _) hcard
  rw [← pow_succ', Nat.sub_add_cancel hb] at hh
  obtain ⟨e, he⟩ := hh
  exact ⟨⟨_, _, e⟩, he, rfl, rfl⟩

private theorem boundary (S : System F h p W z) :
    S.frame.width + S.latent.width = (Controls h p S.config).width +
      ((Perm h).pair S.selector).width + 1 + 2 * 2 ^ (h + 1) * (W * z + 2 ^ p * z) := by
  unfold System.frame System.terminals System.latent Exterior
  rw [Format.width_pair, Format.width_pair, Format.width_pair, Format.width_pair,
    Format.width_pair, Format.width_pair, Format.width_pair, Format.width_bit,
    Format.width_vec (h + 1) (raw _), Format.width_vec (h + 1) (raw _)]
  simp only [Format.width, raw, Fintype.card_prod, Fintype.card_fin]
  ring

private theorem grid_bound (B : Book h p z) (hg : B.g + B.b = h + p + 2) :
    Fintype.card B.grid.Ports = 2 ^ h * (4 * 2 ^ p) * (2 + B.b + z) := by
  simp only [Book.grid, Grid.Ports, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]
  rw [show 2 ^ B.b + 2 ^ B.b * (1 + B.b + z) = 2 ^ B.b * (2 + B.b + z) by ring, ← mul_assoc, ← pow_add, hg]
  ring

private def factor (p W : ℕ) := 10000000 * (100 + 100 * W + 100 * 2 ^ p * (2 + p) ^ 3)

private theorem bill_le (S : System F h p W z) (B : Book h p z) (hg : B.g + B.b = h + p + 2)
    (hb : B.b ≤ h) (hn : n ≤ W * z) {T : ℕ}
    (hT : (100 + h) ^ 4 ≤ T) (hz : z ≤ T) (hr : r ≤ T)
    (hm : ((Perm h).pair S.selector).width + (Controls h p S.config).width + m ≤ 2 ^ (h + 1) * T) :
    S.bill B n m r ≤ 2 ^ h * factor p W * T := by
  have hp := Nat.one_le_pow h 2 (by decide)
  have hu : 2 + h ≤ T := by
    have := Nat.pow_le_pow_right (show 0 < 100 + h by omega) (by decide : 1 ≤ 4)
    simp only [pow_one] at this
    omega
  have hu' : (h + 1) ^ 4 ≤ T := (Nat.pow_le_pow_left (by omega) _).trans hT
  have he : wd (input h n) ≤ 2 ^ h * (2 * W + 1) * T := by
    simp only [wd, wd_tree, wd_word]
    calc
      _ ≤ 2 ^ h * (W * T) + 2 ^ h * (T + W * T) := by
        have := hn.trans (Nat.mul_le_mul_left W hz)
        gcongr; omega
      _ = _ := by ring
  have hh : (1 + h + 1 + p) ^ 3 * (1 + B.b) ≤ (2 + p) ^ 3 * T := calc
    _ ≤ ((2 + p) * (100 + h)) ^ 3 * (100 + h) := by gcongr <;> nlinarith only [hb]
    _ = (2 + p) ^ 3 * (100 + h) ^ 4 := by ring
    _ ≤ _ := by gcongr
  have hwide := Nat.mul_le_mul_left (2 ^ (h + 1 + p)) hh
  have hgrid : Fintype.card B.grid.Ports ≤ 2 ^ h * (4 * 2 ^ p) * (2 * T) := by
    rw [grid_bound B hg]; gcongr; omega
  have ht := Nat.mul_le_mul_left (2 * 2 ^ (h + 1)) (Nat.add_le_add
    (Nat.mul_le_mul_left W hz) (Nat.mul_le_mul_left (2 ^ p) hz))
  have endpt := Nat.mul_le_mul_left (2 ^ (h + 1))
    (Nat.add_le_add (Nat.add_le_add hr hu') (Nat.mul_le_mul_left W hz))
  have hone : 1 ≤ 2 ^ h * T := Nat.mul_pos (by omega) (by omega)
  have hframe := boundary S
  rw [← mul_assoc] at hwide
  calc
    _ ≤ 10000000 * (2 * (2 ^ (h + 1) * T) + 2 * (2 ^ h * T) + 2 * 2 ^ (h + 1) * (W * T + 2 ^ p * T) +
        2 ^ h * (2 * W + 1) * T + 2 ^ (h + 1 + p) * ((2 + p) ^ 3 * T) + 2 ^ h * (4 * 2 ^ p) * (2 * T) +
        2 ^ (h + 1) * (T + T + W * T)) := by unfold System.bill; apply Nat.mul_le_mul_left; omega
    _ ≤ _ := by unfold factor; ring_nf; omega

private theorem absorb (K a j : ℕ) :
    K * (100 + j) ^ a ≤ (100 + j) ^ (Nat.clog 2 K + a) := by
  rw [pow_add]
  exact Nat.mul_le_mul_right _ ((Nat.le_pow_clog (by decide : 1 < 2) K).trans
    (Nat.pow_le_pow_left (by omega) _))

theorem realize (F : Type) [Field F] (p W D : ℕ) :
    ∃ E : ℕ, ∀ (h n b j C : ℕ) (S : System F h p W (2 ^ j)),
      1 ≤ b → b ≤ h → n ≤ W * 2 ^ j → S.Correct C →
      (∀ i, (Finset.univ.filter (fun k => S.group k = i)).card ≤ 2 ^ (b - 1)) →
      Cheap F (h + 1) (h + 1) ((Perm h).pair S.selector) (Controls h p S.config) S.dispatch D →
      Weight F S.localWeight (2 ^ j * (100 + j) ^ D) →
      ∃ (G : Grid) (m : ℕ), G.g = h + p + 2 - b ∧ G.b = b ∧ G.r = 1 + b + 2 ^ j ∧
        G.Open F h n m (C * W * 2 ^ h) ∧ m ≤ 2 ^ h * ((100 + h) ^ E + 2 ^ j * (100 + j) ^ E) := by
  let a := 2 * D + 4
  let K := factor p W
  refine ⟨Nat.clog 2 K + a, ?_⟩
  rintro h n b j C S hb hb' hn hcor hgrp ⟨m, hm, hc⟩ hw
  obtain ⟨B, hv, hg, hB⟩ := book (z := 2 ^ j) S.group hb hb' hgrp
  obtain ⟨t, ht, hopen⟩ := assemble S B hv hn hcor hm hw
  refine ⟨B.grid, t, hg, hB, congrArg (fun x => 1 + x + 2 ^ j) hB, hopen, ?_⟩
  let T := (100 + h) ^ a + 2 ^ j * (100 + j) ^ a
  have hh : (100 + h) ^ a ≤ T := Nat.le_add_right _ _
  have hj : 2 ^ j * (100 + j) ^ a ≤ T := Nat.le_add_left _ _
  have hd : (100 + (h + 1)) ^ D ≤ T := calc
    _ ≤ ((100 + h) ^ 2) ^ D := Nat.pow_le_pow_left (by nlinarith) _
    _ = (100 + h) ^ (2 * D) := (pow_mul ..).symm
    _ ≤ _ := (Nat.pow_le_pow_right (by omega) (by omega)).trans hh
  have h4 : (100 + h) ^ 4 ≤ T := (Nat.pow_le_pow_right (by omega) (by omega)).trans hh
  have hz : 2 ^ j ≤ T := (Nat.le_mul_of_pos_right _ (by positivity)).trans hj
  have hr : 2 ^ j * (100 + j) ^ D ≤ T := (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega)
    (by omega))).trans hj
  have hcost := bill_le S B (by omega) (by omega) hn h4 hz hr (hc.trans (Nat.mul_le_mul_left _ hd))
  calc
    _ ≤ 2 ^ h * K * T := ht.trans hcost
    _ = 2 ^ h * (K * (100 + h) ^ a + 2 ^ j * (K * (100 + j) ^ a)) := by unfold T; ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.add_le_add (absorb K a h)
      (Nat.mul_le_mul_left _ (absorb K a j)))

end OAI.LinearAlgebra.MatrixExponent.Transport
end

section
/-!
# Scaling the chunk width

Choose the first height j with W times the dyadic width at least h^A.
The padding costs at most a factor of two. A polynomial in j is
absorbed by any positive power of h at this width.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Transport
open Filter

private theorem eventual_exp (E : ℕ) {r : ℝ} (hr : 1 < r) :
    ∀ᶠ j : ℕ in atTop, (j : ℝ) ^ E ≤ r ^ j := by
  filter_upwards [(tendsto_pow_const_div_const_pow_of_one_lt E hr).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with j hj
  exact ((div_lt_one (pow_pos (by linarith) j)).mp hj).le

private theorem polynomial {j E A : ℕ} (hj : 100 ≤ j) (hA : 2 * E ≤ A) :
    (100 + j) ^ E ≤ j ^ A := by
  calc
    _ ≤ (j ^ 2) ^ E := Nat.pow_le_pow_left (by nlinarith) _
    _ = j ^ (2 * E) := (pow_mul ..).symm
    _ ≤ j ^ A := Nat.pow_le_pow_right (by omega) hA

private theorem dyadic {W A : ℕ} (hw : 4 ≤ W) (ha : 2 ≤ A) :
    ∀ᶠ h : ℕ in atTop, ∃ j ≤ h, h ^ A ≤ W * 2 ^ j ∧ W * 2 ^ j ≤ 2 * h ^ A ∧ 1 + h ≤ 2 ^ j := by
  filter_upwards [eventual_exp A (by norm_num : (1 : ℝ) < 2), eventually_ge_atTop (2 * W)]
    with h he hh
  have hh' : h ^ A ≤ 2 ^ h := by exact_mod_cast he
  have lb : W * (1 + h) ≤ h ^ A := calc
    _ ≤ h ^ 2 := by nlinarith
    _ ≤ _ := Nat.pow_le_pow_right (by omega) ha
  have ub : h ^ A ≤ W * 2 ^ h := hh'.trans (Nat.le_mul_of_pos_left _ (by omega))
  have ex : ∃ j : ℕ, h ^ A ≤ W * 2 ^ j := ⟨h, ub⟩
  have hj := Nat.find_spec ex
  refine ⟨Nat.find ex, Nat.find_min' ex ub, hj, ?_, Nat.le_of_mul_le_mul_left (lb.trans hj) (by omega)⟩
  cases e : Nat.find ex with
  | zero => simp only [pow_zero, mul_one]; nlinarith
  | succ j =>
    have small := Nat.find_min ex (show j < Nat.find ex by omega)
    rw [pow_succ, ← mul_assoc]
    omega

private theorem scales {W E A : ℕ} (hw : 4 ≤ W) (ha : max 2 (2 * E) ≤ A)
    {ζ : ℝ} (hz : 0 < ζ) :
    ∀ᶠ h : ℕ in atTop, ∃ j ≤ h, h ^ A ≤ W * 2 ^ j ∧ W * 2 ^ j ≤ 2 * h ^ A ∧ 1 + h ≤ 2 ^ j ∧
      (((100 + h) ^ E + 2 ^ j * (100 + j) ^ E : ℕ) : ℝ) ≤ (h : ℝ) ^ A * (h : ℝ) ^ ζ := by
  have ha' : 0 < (A : ℝ) := by exact_mod_cast (show 0 < A by omega)
  let r := ζ / A
  have hr : 0 < r := div_pos hz ha'
  have hex := eventual_exp (2 * E) (Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hr)
  obtain ⟨n, hn⟩ := eventually_atTop.mp (hex.and (eventually_ge_atTop 100))
  have ht := (tendsto_rpow_atTop hz).comp tendsto_natCast_atTop_atTop
  filter_upwards [dyadic hw (le_trans (le_max_left ..) ha), eventually_ge_atTop (2 ^ n),
    ht.eventually_ge_atTop 2] with h hh hbig hζ
  change 2 ≤ (h : ℝ) ^ ζ at hζ
  obtain ⟨j, hj, hl, hu, hlarge⟩ := hh
  have hn' : n ≤ j := by
    by_contra! h'
    have := Nat.pow_le_pow_right (by decide : 0 < 2) h'.le
    omega
  obtain ⟨hsmall, h100⟩ := hn j hn'
  have hhalf : 2 * 2 ^ j ≤ h ^ A := by
    have := Nat.mul_le_mul_right (2 ^ j) hw
    omega
  have hhalf' : 2 * (2 : ℝ) ^ j ≤ (h : ℝ) ^ A := by exact_mod_cast hhalf
  have hpay : ((100 + j : ℕ) : ℝ) ^ E ≤ (h : ℝ) ^ ζ := calc
    _ ≤ (j : ℝ) ^ (2 * E) := by exact_mod_cast polynomial h100 (le_refl (2 * E))
    _ ≤ ((2 : ℝ) ^ r) ^ j := hsmall
    _ = ((2 : ℝ) ^ j) ^ r := by
      rw [← Real.rpow_mul_natCast (by norm_num), mul_comm, Real.rpow_natCast_mul (by norm_num)]
    _ ≤ ((h : ℝ) ^ A) ^ r := Real.rpow_le_rpow (by positivity)
      (by linarith [show 0 < (2 : ℝ) ^ j by positivity]) hr.le
    _ = _ := by rw [← Real.rpow_natCast_mul (by positivity), show (A : ℝ) * r = ζ from mul_div_cancel₀ _ ha'.ne']
  have hctrl : ((100 + h : ℕ) : ℝ) ^ E ≤ (h : ℝ) ^ A := by
    exact_mod_cast polynomial (h100.trans hj) (le_trans (le_max_right ..) ha)
  refine ⟨j, hj, hl, hu, hlarge, ?_⟩
  simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] at hpay hctrl ⊢
  nlinarith only [hctrl, mul_le_mul_of_nonneg_left hpay (by positivity : 0 ≤ (2 : ℝ) ^ j),
    mul_le_mul_of_nonneg_right hhalf' (by positivity : 0 ≤ (h : ℝ) ^ ζ),
    mul_le_mul_of_nonneg_left hζ (by positivity : 0 ≤ (h : ℝ) ^ A)]

/-- A local protocol yields grouped transports at every sufficiently
large polynomial width. The total active width is uniform in τ. -/
theorem groups_of_local {F : Type} [Field F] (ht : LocalProtocol F) :
    Install.GroupProtocol F := by
  obtain ⟨C, hC⟩ := ht
  refine ⟨4 * C + 1, by exact_mod_cast (show 1 ≤ 4 * C + 1 by omega), fun τ hτ => ?_⟩
  obtain ⟨p, W, D, hW, hsite⟩ := hC τ hτ
  obtain ⟨E, hE⟩ := realize F p W D
  have hW' : 0 < (W : ℝ) := by exact_mod_cast (show 0 < W by omega)
  refine ⟨(W : ℝ)⁻¹, inv_pos.mpr hW', p + 2, max 2 (2 * E), fun A hA ζ hζ => ?_⟩
  filter_upwards [hsite, scales hW hA hζ] with h hs hj
  obtain ⟨b, hpb, hbh, hb, hS⟩ := hs
  obtain ⟨j, hjh, hl, hu, he, hcost⟩ := hj
  obtain ⟨S, hcor, hgrp, hd, hw⟩ := hS j hjh
  obtain ⟨G, m, hg, hb', hr, hopen, hm⟩ :=
    hE h (h ^ A) b j C S (by omega) hbh hl hcor hgrp hd hw
  have hwidth : W * G.r ≤ 4 * h ^ A := calc
    _ ≤ W * (2 * 2 ^ j) := Nat.mul_le_mul_left _ (by omega)
    _ = 2 * (W * 2 ^ j) := by ring
    _ ≤ _ := by omega
  refine ⟨G, m, C * W * 2 ^ h, by rwa [hb'], by omega, by omega, ?_, by omega, ?_, ?_, ?_, hopen⟩
  · apply (inv_mul_le_iff₀ hW').mpr
    exact_mod_cast hl.trans (Nat.mul_le_mul_left W (show 2 ^ j ≤ G.r by omega))
  · have := Nat.mul_le_mul_right G.r hW
    omega
  · have hv : C * W * 2 ^ h * G.r ≤ (4 * C + 1) * 2 ^ h * h ^ A := calc
      _ = C * 2 ^ h * (W * G.r) := by ring
      _ ≤ C * 2 ^ h * (4 * h ^ A) := Nat.mul_le_mul_left _ hwidth
      _ ≤ _ := by ring_nf; omega
    exact_mod_cast hv
  · calc
      (m : ℝ) ≤ (2 : ℝ) ^ h * (((100 + h) ^ E + 2 ^ j * (100 + j) ^ E : ℕ) : ℝ) := by exact_mod_cast hm
      _ ≤ (2 : ℝ) ^ h * ((h : ℝ) ^ A * (h : ℝ) ^ ζ) := mul_le_mul_of_nonneg_left hcost (by positivity)
      _ = _ := by ring

end OAI.LinearAlgebra.MatrixExponent.Transport
end
