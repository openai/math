import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Presents
import OAI.LinearAlgebra.MatrixExponent.Assembly.AppendAddress
import OAI.LinearAlgebra.MatrixExponent.Assembly.Volumes
import OAI.LinearAlgebra.MatrixExponent.Assembly.SpanSupplies
import OAI.LinearAlgebra.MatrixExponent.Assembly.Serial

/-!
# Concatenating spans at one station

The channel and direction identify the new lane. The two ends of
each contact order old spans by the lane at the source. Exposed spans
retain their old relative order on each side.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Merge
open Coloring Finset
open scoped Classical

variable {F : Type} {d k e : ℕ}

abbrev Key (d : ℕ) := Option (B d) × Bool

def code (d : ℕ) : Key d ↪ B (d + 2) :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (by
    simp only [Key, Fintype.card_prod, Fintype.card_option, Fintype.card_bool, Fintype.card_fin, pow_add]
    have := Nat.one_le_pow d 2 (by decide)
    omega))

def parse (i : B (d + 2)) : Key d := Function.invFun (code d) i

@[simp] theorem parse_code (p : Key d) : parse (code d p) = p :=
  Function.leftInverse_invFun (code d).injective _

variable (P : Pattern F d k e) (v : B k)

def lane (i : B e) := code d ((P.peer v i).map Prod.fst, P.direction v i)

def mate (i : B e) := ((P.peer v i).map fun z => z.2.2).getD i

def order (i : B e) := if P.direction v i then mate P v i else i

def length (s : B (d + 2)) := ∑ i with lane P v i = s, P.width v i

def offset (i : B e) :=
  ∑ j with lane P v j = lane P v i ∧ order P v j < order P v i, P.width v j

private theorem prefix_le (i : B e) (a : Finset (B e)) (ha : i ∈ a)
    (hall : ∀ j, lane P v j = lane P v i → order P v j < order P v i → j ∈ a) :
    offset P v i + P.width v i ≤ ∑ j ∈ a, P.width v j := by
  unfold offset
  rw [add_comm, ← sum_insert (by simp)]
  refine sum_le_sum_of_subset (insert_subset ha ?_)
  intro j hj
  exact hall j (mem_filter.mp hj).2.1 (mem_filter.mp hj).2.2

theorem inside (i : B e) : offset P v i + P.width v i ≤ length P v (lane P v i) :=
  prefix_le P v i _ (by simp) (fun _ h _ => mem_filter.mpr ⟨mem_univ _, h⟩)

theorem before {i j : B e} (h : lane P v i = lane P v j) (h' : order P v i < order P v j) :
    offset P v i + P.width v i ≤ offset P v j :=
  prefix_le P v i _ (mem_filter.mpr ⟨mem_univ _, h, h'⟩)
    (fun _ a b => mem_filter.mpr ⟨mem_univ _, a.trans h, b.trans h'⟩)

def index (p : P.Pin v) : Σ s, Fin (length P v s) :=
  ⟨lane P v p.1, offset P v p.1 + p.2.val,
    (Nat.add_lt_add_left p.2.isLt _).trans_le (inside P v p.1)⟩

theorem bijective (uniq : ∀ i j, 0 < P.width v i → 0 < P.width v j →
    lane P v i = lane P v j → order P v i = order P v j → i = j) :
    Function.Bijective (index P v) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · rintro ⟨i, x⟩ ⟨j, y⟩ he
    have hc : lane P v i = lane P v j := congrArg Sigma.fst he
    have hw : offset P v i + x.val = offset P v j + y.val :=
      congrArg (fun p => p.2.val) he
    have hi := x.isLt
    have hj := y.isLt
    rcases lt_trichotomy (order P v i) (order P v j) with h|h|h
    · have := before P v hc h; omega
    · have h' := uniq _ _ (by omega) (by omega) hc h
      subst j
      rw [show x = y from Fin.ext (by omega)]
    · have := before P v hc.symm h; omega
  · simp only [Pattern.Pin, Fintype.card_sigma, Fintype.card_fin, length, sum_filter]
    rw [sum_comm]; simp

variable (back : B d → B d)

def pattern : Pattern F d k (d + 2) where
  width := length P
  direction _ s := (parse s).2
  peer v s := if length P v s = 0 then none else (parse s).1.map fun c =>
    (c, 0, code d (some (back c), !(parse s).2))
  value v x := P.value v fun i j => x (index P v ⟨i, j⟩).1 (index P v ⟨i, j⟩).2

end OAI.LinearAlgebra.MatrixExponent.Assembly.Merge
end

/-! # Short labels for merging spans. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Merge
open Coloring Finset
open scoped Classical

variable {F : Type} (S : Scheme F)

abbrev key := Format.pair (.addr S.ℓ) (.vec S.d (.addr S.d))

abbrev scheme : Scheme F :=
  { S with e := S.d + 2, ℓ := (key S).width,
           decode := fun c => let a := (key S).serial.symm c
             pattern (S.decode a.1) a.2 }

theorem label_width : (scheme S).ℓ = S.ℓ + 2 ^ S.d * S.d := by simp [key]

def back (r : S.format.obj) (i : B S.m) (j : B S.d) : B S.d :=
  ∑ k, if (r ((r i).1 j)).1 k = i then k else 0

def rows (r : S.format.obj) : (scheme S).format.obj :=
  fun i => ((r i).1, fun z => (key S).serial ((r i).2 z, back S r i))

abbrev template (D : Template F) : Template F :=
  { D with scheme := scheme D.scheme, order := Equiv.refl _ }

def record (D : Template F) (r : D.format.obj) : (template D).format.obj :=
  (rows D.scheme r.1, r.2)

variable (r : S.format.obj)

theorem at_row (v : S.Vtx) :
    (scheme S).pattern (rows S r) v = pattern (S.pattern r v) (back S r v.1) := by
  simp only [Scheme.pattern, rows, scheme, Equiv.symm_apply_apply]

theorem width (v : S.Vtx) (c : B (S.d + 2)) :
    (scheme S).width (rows S r) (v, c) = length (S.pattern r v) v.2.2 c := by
  rw [Scheme.width, at_row]; rfl

theorem direction (v : S.Vtx) (c : B (S.d + 2)) :
    (scheme S).direction (rows S r) (v, c) = (parse c).2 := by
  rw [Scheme.direction, at_row]; rfl

theorem peer (v : S.Vtx) (c : B (S.d + 2)) :
    (scheme S).peer (rows S r) (v, c) =
      if length (S.pattern r v) v.2.2 c = 0 then none else
      (parse c).1.map fun j => (((r v.1).1 j, v.2.1, 0),
        code S.d (some (back S r v.1 j), !(parse c).2)) := by
  rw [Scheme.peer, at_row]
  simp only [pattern]
  split
  · rfl
  · cases (parse c).1 <;> rfl

abbrev Recip := Fmt.Reciprocal (.vec S.h (.addr S.ℓ)) r

theorem back_eq (hr : Recip S r) {i l : B S.m} {j k : B S.d}
    (hj : (r i).1 j = l) (hk : (r l).1 k = i) (hne : i ≠ l) : back S r i j = k := by
  have hu := hr i j (by rw [hj]; exact hne.symm)
  rw [hj] at hu
  have eq a : (r l).1 a = i ↔ a = k := ⟨fun h => hu.unique h hk, fun h => h ▸ hk⟩
  simp only [back, hj, eq, sum_ite_eq', mem_univ, ite_true]

abbrev band (v : S.Vtx) (i : B S.e) := lane (S.pattern r v) v.2.2 i
abbrev priority (v : S.Vtx) (i : B S.e) := order (S.pattern r v) v.2.2 i
abbrev start (v : S.Vtx) (i : B S.e) := offset (S.pattern r v) v.2.2 i

/-- On the destination side the source lane is unique by reciprocity. -/
theorem distinct (h : S.Proper r) (v : S.Vtx) (i j : B S.e)
    (hc : band S r v i = band S r v j) (hp : priority S r v i = priority S r v j)
    (hk : S.k = 0) : i = j := by
  have : Subsingleton (B S.k) := by rw [hk]; exact inferInstanceAs (Subsingleton (Fin 1))
  obtain ⟨he, hd⟩ := Prod.mk.inj ((code S.d).injective hc)
  unfold priority order at hp
  rw [hd] at hp
  split at hp
  · unfold mate at hp
    cases hi : (S.pattern r v).peer v.2.2 i with
    | none =>
      have hj : (S.pattern r v).peer v.2.2 j = none := by simpa [hi] using he.symm
      simpa [hi, hj] using hp
    | some a =>
      cases hj : (S.pattern r v).peer v.2.2 j with
      | none => simp [hi, hj] at he
      | some b =>
        have hab : a = b := Prod.ext (by simpa [hi, hj] using he)
          (Prod.ext (Subsingleton.elim ..) (by simpa [hi, hj] using hp))
        subst b
        have hi' : S.peer r (v, i) = some (((r v.1).1 a.1, v.2.1, a.2.1), a.2.2) := by simp [Scheme.peer, hi]
        have hj' : S.peer r (v, j) = some (((r v.1).1 a.1, v.2.1, a.2.1), a.2.2) := by simp [Scheme.peer, hj]
        exact congrArg Prod.snd (Option.some.inj ((h _ _ hi').1.symm.trans (h _ _ hj').1))
  · exact hp

end OAI.LinearAlgebra.MatrixExponent.Assembly.Merge
end

/-! # Matching the two ordered lists of spans on a contact -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Merge
open Coloring Finset
open scoped Classical

variable {F : Type} {S : Scheme F} {r : S.format.obj} {v w : S.Vtx} {c d : B S.d}

private abbrev other (S : Scheme F) (r : S.format.obj) (v : S.Vtx) := mate (S.pattern r v) v.2.2

structure Contact (S : Scheme F) (r : S.format.obj) (v w : S.Vtx) (c d : B S.d) : Prop where
  left : (r v.1).1 c = w.1
  right : (r w.1).1 d = v.1
  block : v.2.1 = w.2.1
  ne : v.1 ≠ w.1

theorem Contact.symm (h : Contact S r v w c d) : Contact S r w v d c :=
  ⟨h.right, h.left, h.block.symm, h.ne.symm⟩

variable {i j : B S.e}

theorem contact (pr : S.Proper r) (h : S.peer r (v, i) = some (w, j)) (ne : v.1 ≠ w.1) :
    ∃ c d, Contact S r v w c d := by
  have hw := (pr _ _ h).1
  unfold Scheme.peer at h hw
  obtain ⟨q, _, hq⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨z, _, hz⟩ := Option.map_eq_some_iff.mp hw
  exact ⟨q.1, z.1, congrArg (fun x => x.1.1) hq, congrArg (fun x => x.1.1) hz,
    congrArg (fun x => x.1.2.1) hq, ne⟩

namespace Contact
variable (h : Contact S r v w c d) (pr : S.Proper r) (hr : Recip S r) (hk : S.k = 0)
include h

include hr in
theorem band_of (he : S.peer r (v, i) = some (w, j)) :
    band S r v i = code S.d (some c, S.direction r (v, i)) ∧ other S r v i = j := by
  obtain ⟨q, hq, ep⟩ := Option.map_eq_some_iff.mp he
  have ea : (r v.1).1 q.1 = w.1 := congrArg (fun x => x.1.1) ep
  have ej : q.2.2 = j := congrArg Prod.snd ep
  have ec : q.1 = c := (back_eq S r hr h.right ea h.ne.symm).symm.trans
    (back_eq S r hr h.right h.left h.ne.symm)
  simp [band, lane, other, mate, Scheme.direction, hq, ec, ej]

include hk in
private theorem peer_of {b : Bool} (hi : band S r v i = code S.d (some c, b)) :
    S.peer r (v, i) = some (w, other S r v i) ∧ S.direction r (v, i) = b := by
  have : Subsingleton (B S.k) := by rw [hk]; exact inferInstanceAs (Subsingleton (Fin 1))
  obtain ⟨hp, hd⟩ := Prod.mk.inj ((code S.d).injective hi)
  obtain ⟨q, hq, hc⟩ := Option.map_eq_some_iff.mp hp
  refine ⟨?_, hd⟩
  simp only [Scheme.peer, other, mate, hq, Option.map_some, Option.getD_some, hc, h.left, h.block,
    Subsingleton.elim q.2.1 w.2.2]

include pr hr hk in
private theorem pair {b : Bool} (hi : band S r v i = code S.d (some c, b)) :
    let j := other S r v i
    band S r w j = code S.d (some d, !b) ∧ other S r w j = i ∧
      priority S r v i = priority S r w j ∧ S.width r (v, i) = S.width r (w, j) := by
  intro j
  obtain ⟨hv, hd⟩ := h.peer_of hk hi
  obtain ⟨hw, he, hne⟩ := pr _ _ hv
  obtain ⟨hb, hm⟩ := h.symm.band_of hr hw
  have hs : S.direction r (w, j) = !b := by
    rw [hd] at hne
    change b ≠ S.direction r (w, j) at hne
    cases b <;> simpa using hne.symm
  refine ⟨hb.trans (by rw [hs]), hm, ?_, he⟩
  change (if S.direction r (v, i) then j else i) = (if S.direction r (w, j) then other S r w j else j)
  rw [hd, hs, hm]
  cases b <;> rfl

include pr hr hk in
private theorem sums (b : Bool) (f : B S.e → Prop) [DecidablePred f] :
    (∑ i with band S r v i = code S.d (some c, b) ∧ f (priority S r v i), S.width r (v, i)) =
    (∑ j with band S r w j = code S.d (some d, !b) ∧ f (priority S r w j), S.width r (w, j)) := by
  apply sum_bij' (fun i _ => other S r v i) (fun j _ => other S r w j)
  · intro i hi
    obtain ⟨hc, hf⟩ := (mem_filter.mp hi).2
    obtain ⟨ha, _, he, _⟩ := h.pair pr hr hk hc
    exact mem_filter.mpr ⟨mem_univ _, ha, he ▸ hf⟩
  · intro j hj
    obtain ⟨hd, hf⟩ := (mem_filter.mp hj).2
    obtain ⟨ha, _, he, _⟩ := h.symm.pair pr hr hk hd
    rw [Bool.not_not] at ha
    exact mem_filter.mpr ⟨mem_univ _, ha, he ▸ hf⟩
  · intro i hi; exact (h.pair pr hr hk (mem_filter.mp hi).2.1).2.1
  · intro j hj; exact (h.symm.pair pr hr hk (mem_filter.mp hj).2.1).2.1
  · intro i hi; exact (h.pair pr hr hk (mem_filter.mp hi).2.1).2.2.2

include pr hr hk in
theorem agree (hi : S.peer r (v, i) = some (w, j)) :
    band S r w j = code S.d (some d, !(S.direction r (v, i))) ∧
    length (S.pattern r v) v.2.2 (band S r v i) = length (S.pattern r w) w.2.2 (band S r w j) ∧
    start S r v i = start S r w j := by
  obtain ⟨hc, hj⟩ := h.band_of hr hi
  obtain ⟨hd, _, he, _⟩ := h.pair pr hr hk hc
  rw [hj] at hd he
  refine ⟨hd, ?_, ?_⟩
  · rw [hc, hd]
    have eq := h.sums pr hr hk (S.direction r (v, i)) (fun _ => True)
    simp only [and_true] at eq
    exact eq
  · have eq := h.sums pr hr hk (S.direction r (v, i)) (fun k => k < priority S r v i)
    rw [←hc, ←hd] at eq
    conv at eq => rhs; rw [he]
    exact eq

end Contact
end OAI.LinearAlgebra.MatrixExponent.Assembly.Merge
end

/-! # Reciprocal contacts and payload offsets after merging -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Merge
open Coloring Finset
open scoped Classical

variable {F : Type} (S : Scheme F) (r : S.format.obj)

/-- Every nonempty internal span crosses to a different host. -/
def Across := ∀ v w i j, 0 < S.width r (v, i) → S.peer r (v, i) = some (w, j) → v.1 ≠ w.1

def span (q : S.Span) : (scheme S).Span := (q.1, band S r q.1 q.2)

local notation "M" => scheme S
local notation "R" => rows S r

theorem side (q : S.Span) : (M).direction R (span S r q) = S.direction r q := by
  rw [span, direction, band, lane, parse_code]; rfl

theorem exterior {q : S.Span} (he : S.peer r q = none) : (M).peer R (span S r q) = none := by
  have h := Option.map_eq_none_iff.mp he
  rw [span, peer]
  simp [band, lane, h]

variable (pr : S.Proper r) (hr : Recip S r) (hk : S.k = 0) (ne : Across S r)
include pr hr hk ne

theorem linked {p q : S.Span} (hp : 0 < S.width r p) (he : S.peer r p = some q) :
    (M).peer R (span S r p) = some (span S r q) ∧
    (M).width R (span S r p) = (M).width R (span S r q) ∧
    start S r p.1 p.2 = start S r q.1 q.2 := by
  obtain ⟨v, i⟩ := p
  obtain ⟨w, j⟩ := q
  obtain ⟨c, d, h⟩ := contact pr he (ne v w i j hp he)
  obtain ⟨hb, hsize, hoff⟩ := h.agree pr hr hk he
  have ha := (h.band_of hr he).1
  refine ⟨?_, ?_, hoff⟩
  · have hn : length (S.pattern r v) v.2.2 (band S r v i) ≠ 0 := by
      have ht := inside (S.pattern r v) v.2.2 i
      change start S r v i + S.width r (v, i) ≤ length (S.pattern r v) v.2.2 (band S r v i) at ht
      omega
    have : Subsingleton (B S.k) := by rw [hk]; exact inferInstanceAs (Subsingleton (Fin 1))
    rw [span, peer, ite_eq_right hn, ha, parse_code]
    simp only [span, Option.map_some, h.left, h.block, back_eq S r hr h.left h.right h.ne, hb,
      Subsingleton.elim (0 : B S.k) w.2.2]
  · exact (width S r _ _).trans (hsize.trans (width S r _ _).symm)

theorem proper : (M).Proper R := by
  rintro ⟨v, c⟩ y hy
  have hp : length (S.pattern r v) v.2.2 c ≠ 0 := by
    intro h
    have hh := (peer S r v c).symm.trans hy
    rw [ite_eq_left h] at hh; cases hh
  obtain ⟨i, hi, hpos⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
  have hl : band S r v i = c := (mem_filter.mp hi).2
  have hw : 0 < S.width r (v, i) := Nat.pos_of_ne_zero hpos
  have hx : (v, c) = span S r (v, i) := by simp only [span, hl]
  rw [hx] at hy ⊢
  cases he : S.peer r (v, i) with
  | none => rw [exterior S r he] at hy; cases hy
  | some q =>
    obtain ⟨hq, hl, _⟩ := linked S r pr hr hk ne hw he
    have hb := pr _ _ he
    have heq := Option.some.inj (hy.symm.trans hq)
    rw [heq]
    refine ⟨(linked S r pr hr hk ne (hw.trans_eq hb.2.1) hb.1).1, hl, ?_⟩
    simpa only [side] using hb.2.2

end OAI.LinearAlgebra.MatrixExponent.Assembly.Merge
end

/-! # Local pin bijections and table values after merging -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Merge
open Coloring
open scoped Classical

variable {F : Type} {d k e : ℕ} (P : Pattern F d k e) (Q : Pattern F d k (d + 2))
  (b : B d → B d) (h : Q = pattern P b)

private def rename (j : B k) (p : P.Pin j) : Q.Pin j :=
  ⟨lane P j p.1, offset P j p.1 + p.2.val, by
    rw [h]; exact (index P j p).2.isLt⟩

private theorem rename_bijective (j : B k) (hu : Function.Bijective (index P j)) :
    Function.Bijective (rename P Q b h j) := by subst Q; exact hu

private theorem rename_table (j : B k) (t : Q.Pin j → Bool) :
    Q.value j (fun q i => t ⟨q, i⟩) =
    P.value j (fun q i => t (rename P Q b h j ⟨q, i⟩)) := by subst Q; rfl

variable (S : Scheme F) (r : S.format.obj) (pr : S.Proper r) (hk : S.k = 0)
local notation "M" => scheme S
local notation "R" => rows S r

def pins (v : S.Vtx) : S.LocalPin r v ≃ (M).LocalPin R v :=
  Equiv.ofBijective (rename _ _ _ (at_row S r v) v.2.2)
    (rename_bijective _ _ _ (at_row S r v) v.2.2
      (bijective _ _ (fun i j _ _ hl ho => distinct S r pr v i j hl ho hk)))

theorem table (v : S.Vtx) (t : (M).LocalPin R v → Bool) :
    (M).table R v t = S.table r v (t ∘ pins S r pr hk v) :=
  rename_table _ _ _ (at_row S r v) v.2.2 t

variable [Field F] {x y : Wire} {G : Diagram F x y}
  (a : S.Seating r G)

def seat : (M).Seating R G where
  vertex := a.vertex
  pin v := (a.pin v).trans (pins S r pr hk (a.vertex v))
  cover p := a.cover (S.port r p.1.1 ((pins S r pr hk p.1.1).symm ⟨p.1.2, p.2⟩))
  sample v t := (table S r pr hk _ t).trans (a.sample v _)
  vacant v hv t := (table S r pr hk _ t).trans (a.vacant v hv _)

/-- All offsets refer to the original source lane, including at a
destination with a different local lane enumeration. -/
theorem seat_ends (t : G.End) :
    let p := a.ends t
    let q := (seat S r pr hk a).ends t
    q.1 = span S r p.1 ∧ q.2.val = start S r p.1.1 p.1.2 + p.2.val := by
  obtain ⟨⟨v, i⟩, rfl⟩ := G.portEquiv.surjective t
  dsimp only
  rw [Scheme.Seating.ends_at, Scheme.Seating.ends_at]
  exact ⟨rfl, rfl⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.Merge
end

/-! # Merging the bundles of a loopless board -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Merge
open Coloring
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {D : Template F} {r : D.format.obj}
  {P : Rounds.Board F x y D.scheme.h} (p : D.Presents r P)
  (hl : ∀ e, P.diagram.source e ≠ P.diagram.target e)

local notation "S" => D.scheme
local notation "M" => scheme D.scheme
local notation "R" => rows D.scheme (Prod.fst r)

private theorem ends_host (t : P.diagram.End) :
    (p.pres.toSeating.ends t).1.1.1 = p.host (P.place (P.diagram.station t)).1 := by
  obtain ⟨⟨v, i⟩, rfl⟩ := P.diagram.portEquiv.surjective t
  rw [p.pres.toSeating.ends_at, Diagram.station_port]
  exact congrArg Prod.fst (p.vertex v)

include p hl in
theorem across : Across (S) r.1 := by
  have sep (e : P.diagram.E) :
      (p.pres.toSeating.ends (.inl (.inr e))).1.1.1 ≠
      (p.pres.toSeating.ends (.inr (.inr e))).1.1.1 := by
    rw [ends_host, ends_host]
    exact fun he => hl e (P.one (Prod.ext (p.host.injective he) (P.edge e).1.symm))
  intro v w i j hp he
  obtain ⟨t, ht⟩ := p.pres.toSeating.ends.surjective ⟨(v, i), 0, hp⟩
  have h : (p.pres.toSeating.ends t).1 = (v, i) := congrArg Sigma.fst ht
  rw [← h] at he
  rcases t with (q|q)|(q|q)
  · rw [p.pres.input] at he; cases he
  · have hw := Option.some.inj ((p.pres.internal q).1.symm.trans he)
    simpa only [h, hw] using sep q
  · rw [p.pres.output] at he; cases he
  · have hw := Option.some.inj (((p.pres.internal q).symm p.pres.proper).1.symm.trans he)
    simpa only [h, hw] using (sep q).symm

variable (hk : D.scheme.k = 0)

def presentation : (M).Presentation R P.diagram where
  toSeating := seat (S) r.1 p.pres.proper hk p.pres.toSeating
  proper := proper (S) r.1 p.pres.proper p.reciprocal hk (across p hl)
  internal e := by
    obtain ⟨h, h'⟩ := p.pres.internal e
    obtain ⟨he, _, ho⟩ := linked (S) r.1 p.pres.proper p.reciprocal hk (across p hl)
      (Nat.zero_lt_of_lt (p.pres.toSeating.ends (.inl (.inr e))).2.isLt) h
    have a := seat_ends (S) r.1 p.pres.proper hk p.pres.toSeating (.inl (.inr e))
    have b := seat_ends (S) r.1 p.pres.proper hk p.pres.toSeating (.inr (.inr e))
    exact ⟨by rw [a.1, b.1, he], by rw [a.2, b.2, ho, h']⟩
  input i := by
    rw [(seat_ends (S) r.1 p.pres.proper hk p.pres.toSeating _).1]
    exact exterior (S) r.1 (p.pres.input i)
  output i := by
    rw [(seat_ends (S) r.1 p.pres.proper hk p.pres.toSeating _).1]
    exact exterior (S) r.1 (p.pres.output i)

def present : (template D).Presents (record D r) P where
  pres := presentation p hl hk
  host := p.host
  vertex := p.vertex
  directed t := by
    have he := (seat_ends (S) r.1 p.pres.proper hk p.pres.toSeating t).1
    exact (congrArg ((M).direction R) he).trans ((side (S) r.1 _).trans (p.directed t))
  live := p.live
  closed := p.closed
  reciprocal := p.reciprocal
  edge := p.edge
  core := p.core
  load := p.load

theorem ends (t : P.diagram.End) :
    let x := p.pres.toSeating.ends t
    let y := (present p hl hk).pres.toSeating.ends t
    y.1 = span (S) r.1 x.1 ∧ y.2.val = start (S) r.1 x.1.1 x.1.2 + x.2.val :=
  seat_ends (S) r.1 p.pres.proper hk p.pres.toSeating t

end OAI.LinearAlgebra.MatrixExponent.Assembly.Merge
end

/-! # Preparing the reciprocal channel array once per host -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Merge
open Coloring Finset

variable (F : Type) [Field F] {m d t : ℕ} (hm : m ≤ t) (hd : 2 ^ d ≤ t)
include hm hd

private theorem check_code (k : B d) :
    Cheap F 0 t (.pair (.addr m) (.addr m)) (.addr d)
      (fun x => if x.1 = x.2 then k else 0) 7 := by
  have hw : d ≤ t := Nat.lt_two_pow_self.le.trans hd
  have ha : (Format.pair (.addr m) (.addr m)).width ≤ 2 ^ 0 * (100 + t) ^ 2 := by simp; ring_nf; omega
  have hb : (Format.pair (.addr d) (.addr d)).width ≤ 2 ^ 0 * (100 + t) ^ 2 := by simp; ring_nf; omega
  have kk := Cheap.const F ha hb (k, 0)
  have h := (kk.pair (cheap_eq F hm)).comp ((cheap_select F d).widen hw)
  convert h.mono (d := 7) (by decide) using 1
  funext x
  simp

abbrev Masks (m d : ℕ) := Format.vec m (.vec d (.addr d))

def reverse (x : (Neighborhood.Rows m d).obj) : (Masks m d).obj :=
  fun i j => ∑ k, if x (x i j) k = i then k else 0

theorem cheap_reverse : Cheap F m t (Neighborhood.Rows m d) (Masks m d) reverse 24 := by
  have hw : d ≤ t := Nat.lt_two_pow_self.le.trans hd
  have hp : (Perm m).width ≤ 2 ^ m * (100 + t) ^ 2 :=
    (column_width m hm).trans (by gcongr; omega)
  have pos := Cheap.const F (Neighborhood.width hm hd) hp id
  have get := Cheap.lookup F m t (.addr m) hm (by simpa)
  have pair (j k : B d) : Cheap F m t (Neighborhood.Rows m d) (Column m d)
      (fun x i => if x (x i j) k = i then k else 0) 14 := by
    have col := ((Neighborhood.column F hm hd k).pair (Neighborhood.column F hm hd j)).comp get
    exact ((col.pair pos).zip.comp (Cheap.map _ fun _ => check_code F hm hd k)).mono (by decide)
  let D := Format.vec d (.vec d (.vec m (.addr d)))
  let A := Format.vec m (.vec d (.vec d (.addr d)))
  have ha : A.width ≤ 2 ^ m * (100 + t) ^ 3 := by
    simp only [A, Format.width_vec, Format.width_addr]
    apply Nat.mul_le_mul_left
    calc
      _ ≤ t * (t * t) := by gcongr
      _ ≤ _ := by ring_nf; omega
  have eq : D.width = A.width := by simp only [D, A, Format.width_vec]; ring
  have all := Cheap.share _ (fun j => Cheap.share _ (pair j) hd) hd
  have swap : Cheap F m t D A (fun x i j k => x j k i) 4 :=
    Cheap.project F (eq.le.trans ha) ha (fun i => (i.2.1, i.2.2.1, i.1, i.2.2.2)) (fun _ _ => rfl)
  have sums : Cheap F 0 t (.vec d (Column d d)) (Column d d) (fun x j => ∑ k, x j k) 12 := by
    have lift {A D : Format} {f : A.obj → D.obj} {c} (h : Cheap F d t A D f c) :
        Cheap F 0 t A D f (c + 1) := by
      obtain ⟨n, hn, hc⟩ := h
      refine ⟨n, hn, hc.trans ?_⟩
      rw [pow_zero, one_mul, pow_succ']
      exact Nat.mul_le_mul_right _ (by omega)
    exact lift (Cheap.map _ fun _ => lift (SpanPlan.cheap_sum F hw))
  exact ((all.comp swap).comp (Cheap.map _ fun _ => sums)).mono (by decide)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Merge
end

/-! # Local relabeling after reciprocal channels have been computed -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Merge
open Coloring

variable {F : Type} [Field F] (D : Template F)

local notation "m" => D.scheme.m
local notation "d" => D.scheme.d
local notation "Q" => Masks m d
local notation "A" => D.format.pair Q

private def nav (r : D.format.obj) : (Neighborhood.Rows m d).obj := D.nav r

private def emit (x : (A).obj) : (template D).format.obj :=
  (fun i => ((x.1.1 i).1, fun z => (key D.scheme).serial ((x.1.1 i).2 z, x.2 i)), x.1.2)

private theorem emit_net : Circuit F (A) (template D).format (emit D)
    ((A).width + 2 * (template D).format.width) := by
  let K := key D.scheme
  let e : slots (word K.width) ≃ K.pins :=
    @Fintype.equivOfCardEq _ _ (slotsFintype _) K.finite ((card_slots _).trans (wd_word _))
  have he (x : K.obj) (i) : (Format.addr K.width).code (K.serial x) i = K.code x (e i) := by
    rw [Format.serial, Equiv.trans_apply, Equiv.apply_symm_apply]
    rfl
  let pick (i : B m) (j : B D.scheme.h) : K.pins → (A).pins
    | .inl a => .inl (.inl (i, .inr (j, a)))
    | .inr a => .inr (i, a)
  let read : (template D).format.pins → (A).pins
    | .inl (i, .inl a) => .inl (.inl (i, .inl a))
    | .inl (i, .inr (j, a)) => pick i j (e a)
    | .inr a => .inl (.inr a)
  refine Circuit.project read ?_
  rintro x (⟨i, j | ⟨j, a⟩⟩ | z)
  · rfl
  · refine (he ((x.1.1 i).2 j, x.2 i) a).trans ?_
    change _ = (A).code x (pick i j (e a))
    cases e a <;> rfl
  · rfl

def cost := 8 * D.format.width + 2 * (template D).format.width + 2 * (2 ^ m * (100 + m + 2 ^ d) ^ 24)

/-- Long-address comparisons are shared by all blocks. Per occurrence
only the old label and the short reciprocal array are copied. -/
theorem record_net : Circuit F D.format (template D).format (record D) (cost D) := by
  have get : Circuit F D.format (Neighborhood.Rows m d) (nav D)
      (D.format.width + 2 * (Neighborhood.Rows m d).width) :=
    Circuit.project (fun q => .inl (q.1, .inl q.2)) (fun _ _ => rfl)
  obtain ⟨n, hn, hc⟩ := cheap_reverse F (Nat.le_add_right m (2 ^ d)) (Nat.le_add_left (2 ^ d) m)
  have c := ((Circuit.id F D.format).pair (get.comp hn)).comp (emit_net D)
  refine c.mono ?_
  unfold cost
  rw [show (A).width = D.format.width + (Q).width from Format.width_pair .., add_assoc 100]
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.Merge
end

/-!
# Merged exterior payloads

Each old span is one fragment. At the sending end use the old order.
At the receiving end group by destination lane, then old lane. Both
lists name each fragment by its sending index.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Merge
open Coloring
open scoped Classical

variable {F : Type} (S : Scheme F) (r : S.format.obj)

theorem ordered {v : S.Vtx} {i j : B S.e}
    (hi : S.peer r (v, i) = none) (hj : S.peer r (v, j) = none)
    (hc : band S r v i = band S r v j) (ho : i < j) :
    start S r v i + S.width r (v, i) ≤ start S r v j := by
  apply before _ _ hc
  have hi' := Option.map_eq_none_iff.mp hi
  have hj' := Option.map_eq_none_iff.mp hj
  simpa [order, mate, hi', hj'] using ho

abbrev dim := S.k + (S.d + 2 + S.e)

abbrev cat {i j : ℕ} (a : B i) (b : B j) : B (i + j) := (Match.rowIndex i j).symm (a, b)

def slot (b : Bool) (P : Pattern F S.d S.k S.e) (v : B S.k) (i : B S.e) :=
  cat v (cat (if b then lane P v i else 0) i)

def pos (b : Bool) (t : S.Span) : B (S.h + dim S) :=
  cat t.1.2.1 (slot S b (S.pattern r t.1) t.1.2.2 t.2)

def fragment (w : ℕ) (b : Bool) (P : Pattern F S.d S.k S.e)
    (z : B S.h) (j : B (dim S)) : (SpanPlan.header w 0 (S.h + dim S)).obj :=
  let v := (Match.rowIndex S.k (S.d + 2 + S.e) j).1
  let i := (Match.rowIndex (S.d + 2) S.e (Match.rowIndex S.k (S.d + 2 + S.e) j).2).2
  let n := if P.peer v i = none ∧ j = slot S b P v i then P.width v i else 0
  (0, Fin.ofNat (2 ^ w) n, cat z (slot S false P v i))

def program (w : ℕ) : SpanProgram S 0 w (dim S) :=
  fun l z => (fragment S w false (S.decode l) z, fun _ => fragment S w true (S.decode l) z)

def list (w : ℕ) (b : Bool) (i : B S.m) (j : B (S.h + dim S)) :=
  let z := Match.rowIndex S.h (dim S) j
  fragment S w b (S.decode ((r i).2 z.1)) z.1 z.2

theorem send (w : ℕ) : (program S w).send r = list S r w false := rfl

theorem no_suffix {m : ℕ} (v : B m) : Match.rowIndex m 0 v = (v, 0) := by
  apply (Match.rowIndex m 0).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Fin.ext
  change v.val = 0 + 1 * v.val
  omega

theorem take (w : ℕ) : (program S w).take r = list S r w true := by
  funext i j
  simp only [SpanProgram.take, SpanProgram.plan, SpanProgram.reorder, no_suffix, program, list]

theorem row_entry (w : ℕ) (b : Bool) (q : S.Span) :
    list S r w b q.1.1 (pos S r b q) =
      (0, Fin.ofNat (2 ^ w) (S.borderLen r q), pos S r false q) := by
  simp only [list, fragment, pos, slot, cat, Equiv.apply_symm_apply, Scheme.pattern, and_true]
  simp only [Scheme.borderLen, Scheme.peer, Scheme.pattern, Scheme.width, Option.map_eq_none_iff]

theorem row_cover (w : ℕ) (b : Bool) (i : B S.m) (j : B (S.h + dim S))
    (hj : 0 < (list S r w b i j).2.1.val) :
    ∃ q, 0 < S.borderLen r q ∧ q.1.1 = i ∧ pos S r b q = j := by
  obtain ⟨⟨z, a⟩, rfl⟩ := (Match.rowIndex S.h (dim S)).symm.surjective j
  let p := S.decode ((r i).2 z)
  let v := (Match.rowIndex S.k (S.d + 2 + S.e) a).1
  let n := (Match.rowIndex (S.d + 2) S.e (Match.rowIndex S.k (S.d + 2 + S.e) a).2).2
  simp only [list, Equiv.apply_symm_apply, fragment] at hj
  change 0 < (Fin.ofNat (2 ^ w) (if p.peer v n = none ∧ a = slot S b p v n then p.width v n else 0)).val at hj
  split at hj
  · rename_i he
    refine ⟨((i, z, v), n), ?_, rfl, ?_⟩
    · have hw := lt_of_lt_of_le hj (Nat.mod_le _ _)
      simp only [Scheme.borderLen, Scheme.peer, Option.map_eq_none_iff, Scheme.width]
      change 0 < if p.peer v n = none then p.width v n else 0
      rwa [ite_eq_left he.1]
    · exact congrArg (cat z) he.2.symm
  · simp at hj

end OAI.LinearAlgebra.MatrixExponent.Assembly.Merge
end
