import OAI.LinearAlgebra.MatrixExponent.Rounds.Stack.Mates
import OAI.LinearAlgebra.MatrixExponent.Assembly.Compute
import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Presents
import OAI.LinearAlgebra.MatrixExponent.Rounds.Sweep
import OAI.LinearAlgebra.MatrixExponent.Rounds.Scale
import OAI.LinearAlgebra.MatrixExponent.Diagram.Canonical
import OAI.LinearAlgebra.MatrixExponent.Transcript.Seats
import OAI.LinearAlgebra.MatrixExponent.Rounds.Levels.Log
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Access

/-! # A short record at each station in an initial board -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Stack.Codec
open Assembly Coloring Packing Label
open scoped Classical

variable {F : Type} [Field F] {a b : Wire} {h t m ℓ : ℕ} {G : Diagram F a b}
  {f : ∀ v, Device (G.table v) t} (L : Codec G f ℓ) (A : Directory (Device.neighbors G f) m)

abbrev scheme (m h : ℕ) : Scheme F := ⟨m, 3, h, 0, 4, ℓ, L.decode⟩

def guide (p : Location G f) : Device.Guide := fun j =>
  ((f p.1).line p.2 j).bind fun s =>
    (mate G f ⟨p.1, s⟩).map fun k => (A.index p (site G f k), 0, slot G f k)

def records (h : ℕ) : (L.scheme m h).format.obj := fun i =>
  (A.nav i, fun _ => Function.extend A.host
    (fun p => L.label p.1 p.2 (guide A p)) (fun _ => L.blank) i)

local notation "S" => L.scheme m h
local notation "r" => L.records A h

def atSite (p : Location G f) (z : B h) : B m × B h × B 0 := (A.host p, z, 0)

theorem pattern_at (p : Location G f) (z : B h) :
    (S).pattern r (atSite A p z) = (f p.1).pattern p.2 (guide A p) := by
  exact (congrArg L.decode (A.host.injective.extend_apply
    (fun x => L.label x.1 x.2 (guide A x)) (fun _ => L.blank) p)).trans (L.read ..)

theorem pattern_off {v : (S).Vtx} (hv : v.1 ∉ Set.range A.host) :
    (S).pattern r v = emptyPattern F := by
  exact (congrArg L.decode (Function.extend_apply'
    (fun x => L.label x.1 x.2 (guide A x)) (fun _ => L.blank) v.1 hv)).trans L.empty

def span (z : B h) (s : Stub G f) := (atSite A (site G f s) z, slot G f s)

theorem width_at (z : B h) (s : Stub G f) :
    (S).width r (span A z s) = Label.width G f s := by
  unfold Scheme.width span
  rw [pattern_at]
  exact (f s.1).sizeAt_slot _ s.2 rfl

theorem direction_at (z : B h) (s : Stub G f) :
    (S).direction r (span A z s) = side G f s := by
  unfold Scheme.direction span
  rw [pattern_at]
  change ((f s.1).line ((f s.1).site s.2) ((f s.1).slot s.2)).elim false (f s.1).side = _
  rw [((f s.1).line_eq _ _ s.2).mpr ⟨rfl, rfl⟩]; rfl

theorem peer_at (z : B h) (s : Stub G f) :
    (S).peer r (span A z s) = (mate G f s).map (span A z) := by
  unfold Scheme.peer
  change (((S).pattern r (atSite A (site G f s) z)).peer 0 (slot G f s)).map _ = _
  rw [pattern_at]
  have hg : guide A (site G f s) (slot G f s) =
      (mate G f s).map (fun k => (A.index (site G f s) (site G f k), 0, slot G f k)) := by
    unfold guide site slot
    rw [((f s.1).line_eq _ _ s.2).mpr ⟨rfl, rfl⟩]; rfl
  change (guide A (site G f s) (slot G f s)).map _ = _
  rw [hg]
  cases e : mate G f s with
  | none => rfl
  | some k =>
    have ha := A.nav_link _ _ (mate_props G f e).2.2.2
    exact congrArg (fun i => some ((i, z, (0 : B 0)), slot G f k)) ha

private theorem peer_source {p q : (S).Span} (hp : (S).peer r p = some q) :
    ∃ (z : B h) (s : Stub G f), span A z s = p := by
  rcases p with ⟨⟨i, z, k⟩, j⟩
  have hk : k = 0 := Fin.eq_zero k
  subst k
  by_cases hv : i ∈ Set.range A.host
  · obtain ⟨v, rfl⟩ := hv
    change (((S).pattern r (atSite A v z)).peer 0 j).map _ = _ at hp
    rw [pattern_at] at hp
    change (guide A v j).map _ = _ at hp
    cases e : (f v.1).line v.2 j with
    | none => simp [guide, e] at hp
    | some s =>
      obtain ⟨hv, hj⟩ := ((f v.1).line_eq ..).mp e
      refine ⟨z, ⟨v.1, s⟩, ?_⟩
      simp only [span, site, slot, hv, hj]; rfl
  · unfold Scheme.peer at hp
    rw [pattern_off L A hv] at hp
    cases hp

theorem proper : (S).Proper r := by
  intro p q hp
  obtain ⟨z, s, rfl⟩ := L.peer_source A hp
  rw [peer_at] at hp
  cases hm : mate G f s with
  | none => simp [hm] at hp
  | some k =>
    rw [hm] at hp
    obtain rfl := Option.some.inj hp
    obtain ⟨he, hw, hs, _⟩ := mate_props G f hm
    rw [peer_at, he, width_at, width_at, direction_at, direction_at]
    exact ⟨rfl, hw, hs⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Stack.Codec
end

/-! # Seating product stations by their local span ordinals -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Stack.Codec
open Assembly Coloring Packing Label Transcript
open scoped Classical

variable {F : Type} [Field F] {a b : Wire} {h t m ℓ n : ℕ} {G : Diagram F a b}
  {f : ∀ v, Device (G.table v) t} (L : Codec G f ℓ) (A : Directory (Device.neighbors G f) m)
  (c : Cell h × Fin (2 ^ t) ≃ Fin n)

local notation "S" => L.scheme m h
local notation "r" => L.records A h
local notation "H" => built G f c

def vertex : (H).V ↪ (S).Vtx where
  toFun v := atSite A (Device.place G f c v).1 (cellIndex h (Device.place G f c v).2)
  inj' _ _ e := (Device.place G f c).injective (Prod.ext (A.host.injective (congrArg Prod.fst e))
    ((cellIndex h).injective (congrArg (fun i => i.2.1) e)))

private theorem occupied (v : (S).Vtx) (e : v.1 ∈ Set.range A.host) :
    v ∈ Set.range (L.vertex A c) := by
  obtain ⟨p, hp⟩ := e
  refine ⟨(Device.place G f c).symm (p, (cellIndex h).symm v.2.1), ?_⟩
  exact Prod.ext hp (Prod.ext ((cellIndex h).apply_symm_apply v.2.1) (Fin.eq_zero _).symm)

private theorem pattern_vertex (v : (H).V) :
    (S).pattern r (L.vertex A c v) =
      (f v.1.2).pattern v.2 (guide A (Device.place G f c v).1) :=
  L.pattern_at A _ _

private theorem size_vertex (v : (H).V) (s : B 4) :
    (f v.1.2).sizeAt v.2 s = (S).width r (L.vertex A c v, s) := by
  unfold Scheme.width
  rw [pattern_vertex]
  rfl

def pins (v : (H).V) : (H).Port v ≃ (S).LocalPin r (L.vertex A c v) :=
  (Equiv.ofBijective _ ((f v.1.2).bijective v.2)).trans
    (Equiv.sigmaCongrRight fun s => finCongr (L.size_vertex A c v s))

private theorem value_at {T : Table F} (D : Device T t) (v : D.diagram.V) (g : Device.Guide)
    (p : Pattern F 3 0 4) (hp : p = D.pattern v g) (x : ∀ s, Fin (p.width 0 s) → Bool)
    (w : ∀ s, D.sizeAt v s = p.width 0 s) :
    p.value 0 x = sample (D.diagram.table v) (fun i =>
      x (D.address v i).1 ((D.address v i).2.cast (w _))) := by subst p; rfl

private theorem idle (p : Pattern F 3 0 4) (hp : p = emptyPattern F)
    (v : B 0) (x : ∀ s, Fin (p.width v s) → Bool) : p.value v x = 1 := by subst p; rfl

def seating : (S).Seating r H where
  vertex := L.vertex A c
  pin := L.pins A c
  cover p := by
    apply L.occupied A c
    by_contra hv
    have hw := Nat.zero_lt_of_lt p.2.isLt
    unfold Scheme.width at hw
    rw [pattern_off L A hv] at hw
    exact Nat.not_lt_zero _ hw
  sample v x := value_at (f v.1.2) _ _ _ (L.pattern_vertex A c v)
    (fun s i => x ⟨s, i⟩) (L.size_vertex A c v)
  vacant v hv x := idle _ (L.pattern_off A (fun he => hv (L.occupied A c v he))) _ _

theorem ends_read (q : (H).End) :
    let i := Label.read G f c q
    ((L.seating A c).ends q).1 = span A (cellIndex h i.1) i.2.1 ∧
    ((L.seating A c).ends q).2.val = i.2.2 := by
  obtain ⟨⟨⟨⟨z, v⟩, u⟩, p⟩, rfl⟩ := (H).portEquiv.surjective q
  rw [Scheme.Seating.ends_at]
  have he := (BatchDescent.Stack.gathered G c).plugEnd_port
    (fun k => (f k.2).diagram) (z, v) ⟨u, p⟩
  have hr : (lift G f c).symm ((H).portEquiv ⟨⟨(z, v), u⟩, p⟩) =
      ⟨(z, v), (f v).diagram.portEquiv ⟨u, p⟩⟩ := (lift G f c).symm_apply_eq.mpr he.symm
  unfold Label.read
  rw [hr]
  refine ⟨?_, rfl⟩
  change (atSite A ⟨v, u⟩ (cellIndex h z), _) =
    (atSite A ⟨v, (f v).site ((f v).localBit u p).1⟩ (cellIndex h z), _)
  rw [Device.local_site]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Rounds.Stack.Codec
end

/-! # A directed presentation of the replicated board -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Stack.Codec
open Assembly Coloring Packing Label
open scoped Classical

variable {F : Type} [Field F] {a b : Wire} {h t m ℓ n : ℕ} {G : Diagram F a b}
  {f : ∀ v, Device (G.table v) t} (L : Codec G f ℓ) (A : Directory (Device.neighbors G f) m)
  (c : Cell h × Fin (2 ^ t) ≃ Fin n)

local notation "S" => L.scheme m h
local notation "r" => L.records A h
local notation "H" => built G f c

private theorem joins (e : (H).E) :
    (S).Joins r ((L.seating A c).ends (wireEnd H e false)) ((L.seating A c).ends (wireEnd H e true)) := by
  obtain ⟨hv, hi⟩ := L.ends_read A c (wireEnd H e false)
  obtain ⟨hw, hj⟩ := L.ends_read A c (wireEnd H e true)
  refine ⟨?_, ?_⟩
  · rw [hv, hw, peer_at]
    rcases e with ⟨k, e⟩|⟨⟨z, v⟩, e⟩
    · rw [read_edge, read_edge, mate_edge]; rfl
    · rw [read_inner, read_inner, mate_inner]; rfl
  · rw [hi, hj]
    rcases e with ⟨k, e⟩|⟨⟨z, v⟩, e⟩
    · rw [read_edge, read_edge]
    · rw [read_inner, read_inner]

private theorem exposed (i : slots (copies a n) ⊕ slots (copies b n)) :
    (S).peer r ((L.seating A c).ends (boundaryEnd H i)).1 = none := by
  rw [(L.ends_read A c _).1, read_boundary, peer_at, mate_boundary]
  rfl

def presentation : (S).Presentation r H where
  toSeating := L.seating A c
  proper := L.proper A
  internal := L.joins A c
  input i := L.exposed A c (.inl i)
  output i := L.exposed A c (.inr i)

theorem directed : (L.presentation A c).Directed := by
  intro e
  change (S).direction r ((L.seating A c).ends e).1 = _
  rw [(L.ends_read A c e).1, direction_at]
  obtain ⟨⟨⟨z, v⟩, q⟩, rfl⟩ := (lift G f c).surjective e
  unfold Label.read
  rw [Equiv.symm_apply_apply]
  exact ((f v).side_codec q).trans (by cases q <;> rfl)

abbrev template (m h : ℕ) : Template F where
  scheme := L.scheme m h
  count := 0
  load _ := 4 * (2 : ℝ) ^ t
  park _ := 0
  past _ := 0
  order := Equiv.refl _

def entry (h : ℕ) : (L.template m h).format.obj :=
  (L.records A h, fun i => ((decide (i ∈ Set.range A.host), false),
    fun j => (A.flags i j, A.flags i j), fun _ => 0))

def presents : (L.template m h).Presents (L.entry A h) (Device.board G f c) where
  pres := L.presentation A c
  host := A.host
  vertex _ := rfl
  directed := L.directed A c
  live _ := decide_eq_true_iff
  closed := A.closed
  reciprocal := A.reciprocal
  edge := A.marks
  core := A.marks
  load v i := by
    change 4 * (2 : ℝ) ^ t = push (Device.place G f c) (fun _ => 4 * (2 : ℝ) ^ t) (v, i)
    unfold push
    simp only [← (Device.place G f c).eq_symm_apply, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end OAI.LinearAlgebra.MatrixExponent.Rounds.Stack.Codec
end

/-!
# Initial layer

Normalize the input diagram and use a common local device for
equal tables. Isolated station values move into one scalar before
the rounds begin. This also covers an empty exterior or zero scalar.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Stack
open Assembly Packing
open scoped Classical

variable {F : Type} [Field F] [Fintype F] {a b : Wire}

/-- The initial layer represents independent copies of the whole input
tensor. Host and dictionary addresses have independent length bounds. -/
theorem start (G : Diagram F a b) {M u D t h : ℕ} {L : Finset (Table F)} {θ : ℝ}
    (admits : G.Admits u ↑L) (size : G.cost ≤ M) (ht : 0 < t) (hu : u ≤ 2 ^ t)
    (hD : 8 ≤ D) (hθ : θ ≤ 4) :
    let d := 2 ^ t * 2 ^ h
    ∃ (P : Layer F (copies a d) (copies b d)) (i : P.State) (z : F),
      (fun x y => z * (P.graph i).eval x y) = power G.eval d ∧
      P.Ready D (2 ^ t) (256 * (M : ℝ) * d * (t + 1)) θ ∧ P.Loopless ∧
      P.template.scheme.m = Nat.clog 2 (16 * M * (t + 1)) ∧
      P.template.scheme.h = h ∧ P.template.scheme.d = 3 ∧
      P.template.scheme.e = 4 ∧ P.template.scheme.ℓ =
        Nat.clog 2 (1 + (L.card + 16 * Fintype.card F ^ 8) * 4 * (1 + 2 ^ t) * (t + 1) * Nat.card Device.Guide) ∧
      P.template.count = 0 ∧
      P.volume = 2 ^ P.template.scheme.m + d * (wd a + wd b) ∧ P.height = h + t + 2 := by
  let d := 2 ^ t * 2 ^ h
  let H := G.normalized.canonical
  let m := Nat.clog 2 (16 * M * (t + 1))
  obtain ⟨he, hs, ha, _, hl⟩ := G.canonical_normalized admits
  have hwidth (v : H.V) : H.arity v ≤ 2 ^ t :=
    (ha v).trans (max_le (Nat.le_self_pow ht.ne' 2) hu)
  obtain ⟨f, ⟨codec⟩⟩ := codec H ht hwidth hl
  have hcard : Fintype.card (Location H f) ≤ 16 * M * (t + 1) := by
    refine (Device.location_bound H f).trans (Nat.mul_le_mul_right _ ?_)
    change 4 * G.normalized.canonical.cost ≤ _
    omega
  obtain ⟨dir⟩ := directory (Device.neighbors H f) m (Device.sym_neighbors H f)
    (fun v => (Device.neighbors_bound H f v).trans (by decide))
    (hcard.trans (Nat.le_pow_clog (by decide) _))
  let c : Cell h × Fin (2 ^ t) ≃ Fin d := Fintype.equivOfCardEq (by simp [d, Cell, mul_comm])
  let p := codec.presents dir c
  have height (v : (built H f c).V) : (built H f c).arity v ≤ 2 ^ (t + 2) := by
    change (f v.1.2).diagram.arity v.2 ≤ _
    simpa [pow_add, mul_comm] using (f v.1.2).arity v.2
  let B := p.singleton height
  refine ⟨B, PUnit.unit, Fmt.weight (codec.template m h).scheme.scalar (codec.entry dir h).1,
    ?_, ?_, fun _ => Device.built_loopless H f c, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
  · funext x y
    refine (p.pres.sweep_eval x y).symm.trans ?_
    change (built H f c).eval x y = _
    rw [Device.exact_value, he]
  · refine ⟨rfl, fun _ => (built H f c).sweep_neutral, fun _ => ?_⟩
    have hseat : (Device.board H f c).seats ≤ 16 * M * (t + 1) * 2 ^ h := Nat.mul_le_mul_right _ hcard
    have budget : 16 * (2 : ℝ) ^ t * (Device.board H f c).seats ≤ 256 * (M : ℝ) * d * (t + 1) := calc
      _ ≤ 16 * (2 : ℝ) ^ t * (16 * M * (t + 1) * 2 ^ h : ℕ) := by gcongr
      _ = _ := by unfold d; push_cast; ring
    exact (Device.ready H f c hD hθ).relax le_rfl budget le_rfl
  · change 2 ^ m + wd (copies a d) + wd (copies b d) = 2 ^ m + d * (wd a + wd b)
    rw [wd_copies, wd_copies, mul_add, add_assoc]

end OAI.LinearAlgebra.MatrixExponent.Rounds.Stack
end

/-!
# Cost of installing the initial stack

Long identifiers are counted per host. The shorter table labels are
counted per host and block. The exposed bit cost scales with the full
tensor power.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Stack

variable {F : Type} [Field F] {x y : Wire} {d : ℕ}

theorem start_cost (P : Layer F (copies x d) (copies y d))
    {H B : ℕ} (hosts : 2 ^ P.template.scheme.m ≤ H) (blocks : P.template.scheme.h = B)
    (degree : P.template.scheme.d = 3) (empty : P.template.count = 0)
    (volume : P.volume = 2 ^ P.template.scheme.m + d * (wd x + wd y)) :
    140 * (P.snapshot.port.width + d * (wd x + wd y)) + 1 ≤
      140 * (H * (8 * (P.template.scheme.m + 2) + 2) +
        H * 2 ^ B * (P.template.scheme.ℓ + 2 * (P.height + 1)) +
        (2 * (P.height + 1) + 1) * (d * (wd x + wd y))) + 1 := by
  let e := d * (wd x + wd y)
  have fmt : P.template.format.width ≤
      H * (8 * (P.template.scheme.m + 2) + 2) + H * 2 ^ B * P.template.scheme.ℓ := by
    rw [P.template.width, degree, blocks, empty, add_zero]
    norm_num
    rw [Nat.mul_add, ← Nat.mul_assoc]
    exact Nat.add_le_add (Nat.mul_le_mul_right _ hosts)
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hosts))
  have bits : P.volume ≤ H * 2 ^ B + e := by
    rw [volume]
    exact Nat.add_le_add_right (hosts.trans
      (Nat.le_mul_of_pos_right _ (by positivity))) e
  have hw := P.width.trans (Nat.add_le_add fmt
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 bits)))
  refine Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right hw e)) _ |>.trans_eq ?_
  congr 1
  ring

end OAI.LinearAlgebra.MatrixExponent.Rounds.Stack
end

section
/-! # Sizes of the initial stack addresses -/

namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Stack

private theorem sum_pow_bound {x y i j : ℕ} (hx : x ≤ 2 ^ i) (hy : y ≤ 2 ^ j) :
    x + y ≤ 2 ^ (i + j + 1) := by
  have hi : (2 : ℕ) ^ i ≤ 2 ^ (i + j) := Nat.pow_le_pow_right (by decide) (by omega)
  have hj : (2 : ℕ) ^ j ≤ 2 ^ (i + j) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [pow_succ]
  omega

private theorem mul_pow_bound {x y i j : ℕ} (hx : x ≤ 2 ^ i) (hy : y ≤ 2 ^ j) :
    x * y ≤ 2 ^ (i + j) :=
  (Nat.mul_le_mul hx hy).trans_eq (pow_add 2 i j).symm

theorem label_bits {L f g t E B : ℕ} (hL : L ≤ 2 ^ B) (hf : f ≤ 2 ^ E) :
    Nat.clog 2 (1 + (L + 16 * f ^ 8) * 4 * (1 + 2 ^ t) * (t + 1) * g) ≤
      B + 8 * E + 2 * t + Nat.clog 2 g + 10 := by
  have h8 : f ^ 8 ≤ 2 ^ (E * 8) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left hf _
  have h16 : 16 * f ^ 8 ≤ 2 ^ (4 + E * 8) :=
    mul_pow_bound (by decide : 16 ≤ 2 ^ 4) h8
  have hleft := sum_pow_bound hL h16
  have hpow := sum_pow_bound (show 1 ≤ (2 : ℕ) ^ 0 by decide) (le_refl ((2 : ℕ) ^ t))
  have ht : t + 1 ≤ (2 : ℕ) ^ (t + 1) := Nat.lt_two_pow_self.le
  have hg := Nat.le_pow_clog (by decide : 1 < 2) g
  have hprod := mul_pow_bound (mul_pow_bound
    (mul_pow_bound (mul_pow_bound hleft (by decide : 4 ≤ 2 ^ 2)) hpow) ht) hg
  apply Nat.clog_le_of_le_pow
  simpa only [show 0 + (B + (4 + E * 8) + 1 + 2 + (0 + t + 1) + (t + 1) + Nat.clog 2 g) + 1 =
    B + 8 * E + 2 * t + Nat.clog 2 g + 10 by omega] using
    sum_pow_bound (show 1 ≤ (2 : ℕ) ^ 0 by decide) hprod

theorem host_bits {m n t : ℕ} (hm : m ≤ n ^ 2) :
    Nat.clog 2 (16 * m * (t + 1)) ≤ 2 * Nat.clog 2 n + t + 5 := by
  have hn := Nat.le_pow_clog (by decide : 1 < 2) n
  have h2 : m ≤ 2 ^ (Nat.clog 2 n * 2) := by
    rw [pow_mul]
    exact hm.trans (Nat.pow_le_pow_left hn _)
  have ht : t + 1 ≤ (2 : ℕ) ^ (t + 1) := Nat.lt_two_pow_self.le
  apply Nat.clog_le_of_le_pow
  rw [show 2 * Nat.clog 2 n + t + 5 = 4 + Nat.clog 2 n * 2 + (t + 1) by omega]
  exact mul_pow_bound (mul_pow_bound (by decide : 16 ≤ 2 ^ 4) h2) ht

theorem padded_hosts {m t : ℕ} (hm : 0 < m) :
    2 ^ (Nat.clog 2 (16 * m * (t + 1))) ≤ 32 * m * (t + 1) :=
  (Transcript.pow_clog_le_twice (by positivity)).trans_eq (by ring)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Stack
end

/-!
# The invariant at the boundaries of complete rounds

Consuming group bits can increase the number of addresses. We bound
the product of the number of addresses and the number of blocks.
The full record length can grow by a constant factor per round.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
open Assembly

variable {δ : ℝ} {p : Design δ} {M : ℕ} (v : Levels p M) {F : Type} [Field F] {x y : Wire}

structure Current (s : Plan) (n m i E : ℕ) (Q : Layer F x y) : Prop where
  ready : Q.Ready s.D (v.width i) (v.budget m i) s.floor
  loopless : Q.Loopless
  address : Nat.clog 2 n ≤ Q.template.scheme.m
  blocks : Q.template.scheme.h + p.steps * i * v.group = v.blocks
  seats : 2 ^ (Q.template.scheme.m + Q.template.scheme.h) ≤ p.overhead ^ i * v.allocation m
  ports : Q.template.scheme.e ≤ 5
  degree : Q.template.scheme.d = 3
  volume : Q.volume = 2 ^ Q.template.scheme.m + wd x + wd y
  height : Q.height ≤ v.span + s.d + s.p
  labels : Q.template.scheme.ℓ + Q.template.count ≤ E ^ i * v.box E

variable {v} {s : Plan} {n m i E : ℕ} {Q : Layer F x y}

theorem initial {Q : Layer F (copies x v.batch) (copies y v.batch)}
    (positive : 0 < m) (hm : n ≤ m)
    (ready : Q.Ready s.D (2 ^ v.stack) (256 * (m : ℝ) * v.batch * (v.stack + 1)) s.floor)
    (loopless : Q.Loopless) (addr : Q.template.scheme.m = Nat.clog 2 (16 * m * (v.stack + 1)))
    (blk : Q.template.scheme.h = v.blocks) (deg : Q.template.scheme.d = 3)
    (port : Q.template.scheme.e = 4) (bits : Q.template.scheme.ℓ ≤ v.box E)
    (ct : Q.template.count = 0) (vol : Q.volume = 2 ^ Q.template.scheme.m + v.batch * (wd x + wd y))
    (ht : Q.height = v.blocks + v.stack + 2) : v.Current s n m 0 E Q where
  ready := by simpa only [budget_zero, width_eq, mul_zero, add_zero] using ready
  loopless := loopless
  address := by
    rw [addr]
    exact Nat.clog_mono_right _ (hm.trans ((Nat.le_mul_of_pos_left _ (by decide : 0 < 16)).trans
      (Nat.le_mul_of_pos_right _ (by omega))))
  blocks := by simp only [blk, mul_zero, zero_mul, add_zero]
  seats := by
    rw [addr, blk, pow_add, pow_zero, one_mul]
    exact Nat.mul_le_mul_right _ (Stack.padded_hosts positive)
  ports := by omega
  degree := deg
  volume := by rw [vol, wd_copies, wd_copies, mul_add, add_assoc]
  height := by rw [ht]; unfold span; omega
  labels := by simpa only [ct, add_zero, pow_zero, one_mul] using bits

namespace Current
variable (h : v.Current s n m i E Q)
include h

theorem left (hi : i ≤ v.j) :
    Q.template.scheme.h = v.remaining + p.steps * (v.j - i) * v.group := by
  apply Nat.add_right_cancel (m := p.steps * i * v.group)
  rw [h.blocks, Levels.blocks, add_assoc, ← add_mul, ← mul_add, Nat.sub_add_cancel hi]

theorem enough (hi : i < v.j) : p.steps * v.group ≤ Q.template.scheme.h := by
  rw [h.left hi.le]
  exact (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by omega))).trans (Nat.le_add_left ..)

theorem bits (hi : i ≤ v.j) : Q.template.scheme.ℓ + Q.template.count ≤ v.box (E + E) := by
  rw [v.box_add]
  refine h.labels.trans (Nat.mul_le_mul_right _ ?_)
  unfold box
  rw [pow_mul]
  exact (Nat.pow_le_pow_left Nat.lt_two_pow_self.le _).trans
    (Nat.pow_le_pow_right (by positivity) (by omega))

end Current
end OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
end

/-! # Passing through the one-group concentration before the contractions -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
open Assembly

variable {δ : ℝ} {p : Design δ} {M : ℕ} (v : Levels p M) {F : Type} [Field F] {x y : Wire}

/-- The excess over the consumed block coordinates is constant. -/
structure Passage (Q : Layer F x y) (D : Template F) (J : ℕ) : Prop where
  height : D.scheme.h + v.group = Q.template.scheme.h
  lower : Q.template.scheme.m ≤ D.scheme.m
  upper : D.scheme.m ≤ Q.template.scheme.m + v.group + J

variable {v} {s : Plan} {n m i E J : ℕ} {Q : Layer F x y} {D : Template F}
  (cur : v.Current s n m i E Q)

include cur in
theorem Current.expand {w c : ℕ} (hc : c * 2 ^ J ≤ p.overhead)
    (hw : w ≤ Q.template.scheme.m + Q.template.scheme.h + J) :
    c * 2 ^ w ≤ p.overhead ^ (i + 1) * v.allocation m := calc
  _ ≤ c * 2 ^ (Q.template.scheme.m + Q.template.scheme.h + J) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hw)
  _ = (c * 2 ^ J) * 2 ^ (Q.template.scheme.m + Q.template.scheme.h) := by rw [pow_add]; ring
  _ ≤ p.overhead * (p.overhead ^ i * v.allocation m) := Nat.mul_le_mul hc cur.seats
  _ = _ := by rw [pow_succ]; ring

include cur in
theorem Current.height_le : Q.template.scheme.h ≤ v.blocks := by have := cur.blocks; omega

include cur in
theorem Current.long {C B : ℕ} (fit : v.Fits n B C) (hi : i ≤ v.j) (hm : m ≤ n ^ 2) :
    Q.template.scheme.m + Q.template.scheme.h ≤ 4 * Nat.clog 2 n := by
  apply fit.address hm hi
  exact cur.seats.trans (Nat.mul_le_mul_right _
    (Nat.pow_le_pow_right (by have := p.overhead_large; omega) (Nat.le_succ _)))

include cur in
theorem Current.slack (hi : i ≤ v.j) {k : ℕ} (hk : k ≤ p.overhead) :
    (k : ℝ) * (v.width i : ℝ) * (2 ^ (Q.template.scheme.m + Q.template.scheme.h) : ℕ) ≤ v.budget m i * (2 : ℝ) ^ v.group := by
  have h := Levels.slack hi (cur.expand (J := 0) (by simpa using hk) le_rfl)
  simpa only [Nat.cast_mul, mul_right_comm, add_zero] using h

end OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
end

/-! # Instantiating the initial stack at the chosen levels -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
open Assembly

variable {δ : ℝ} {p : Design δ} {M n m B C E T₀ : ℕ} {v : Levels p M}
  {a b ξ : ℝ} {s : Plan} {F : Type} [Field F] [Fintype F] {x y : Wire}

private theorem dictionary_le_box (fit : v.Fits n B C) :
    Shaving.dictionary n ≤ 2 ^ (v.box 2) := by
  have hcl : Nat.clog 2 (Nat.clog 2 n) ≤ v.height := Nat.clog_le_of_le_pow fit.height
  have hx : v.height ≤ v.span := Nat.le_add_left ..
  have hy : v.span ≤ (2 : ℕ) ^ v.j :=
    (Nat.le_mul_of_pos_left _ (by omega : 0 < B + 4)).trans fit.span
  have h := Nat.pow_le_pow_left ((hcl.trans hx).trans hy) 2
  rw [← pow_mul] at h
  apply Nat.pow_le_pow_right (by decide)
  exact h.trans (Nat.pow_le_pow_right (by decide) (by omega))

omit [Field F] in
theorem startup_labels_of_box (fit : v.Fits n B C)
    {L : ℕ} (labels : L ≤ 2 ^ (v.box 2))
    (hF : Fintype.card F ≤ (Nat.clog 2 n) ^ B)
    (allow : 15 + 8 * B + Nat.clog 2 (Nat.card Stack.Device.Guide) ≤ E) :
    Nat.clog 2 (1 + (L + 16 * Fintype.card F ^ 8) * 4 * (1 + 2 ^ v.stack) * (v.stack + 1)*
      Nat.card Stack.Device.Guide) ≤ v.box E := by
  have hcard : Fintype.card F ≤ 2 ^ (B * v.height) := by
    rw [mul_comm, pow_mul]
    exact hF.trans (Nat.pow_le_pow_left fit.height _)
  let g := Nat.clog 2 (Nat.card Stack.Device.Guide)
  let D := 13 + 8 * B + g
  have hspan : v.span ≤ v.box 2 :=
    ((Nat.le_mul_of_pos_left _ (by omega : 0 < B + 4)).trans fit.span).trans
      (Nat.pow_le_pow_right (by decide) (by omega))
  have ht : v.stack ≤ v.box 2 := (show v.stack ≤ v.span by unfold Levels.span; omega).trans hspan
  have hh : v.height ≤ v.box 2 := (Nat.le_add_left ..).trans hspan
  have hb : 0 < v.box 2 := Nat.two_pow_pos _
  have hbound : v.box 2 + 8 * (B * v.height) + 2 * v.stack + g + 10 ≤ D * v.box 2 := by
    have := Nat.mul_le_mul_left (8 * B) hh
    have := Nat.le_mul_of_pos_right (g + 10) hb
    unfold D
    simp only [add_mul, mul_assoc] at *
    omega
  have he : D + 2 ≤ E := by unfold D g; omega
  exact (Stack.label_bits labels hcard).trans (hbound.trans
    ((Nat.mul_le_mul_right _ (v.le_box D)).trans
      ((v.box_add D 2).symm.le.trans (v.box_mono he))))

theorem startup_labels {F : Type} [Field F] [Fintype F] (fit : v.Fits n B C)
    {L : ℕ} (labels : L ≤ Shaving.dictionary n)
    (hF : Fintype.card F ≤ (Nat.clog 2 n) ^ B)
    (allow : 15 + 8 * B + Nat.clog 2 (Nat.card Stack.Device.Guide) ≤ E) :
    Nat.clog 2 (1 + (L + 16 * Fintype.card F ^ 8) * 4 * (1 + 2 ^ v.stack) * (v.stack + 1)*
      Nat.card Stack.Device.Guide) ≤ v.box E :=
  startup_labels_of_box fit (labels.trans (dictionary_le_box fit)) hF allow

theorem starting_layer_of_box (ok : v.Suits n T₀ a b ξ) (fit : v.Fits n B C)
    (hb : 0 < b) (hm : n ≤ m) (hD : 8 ≤ s.D) (hθ : s.floor ≤ 4)
    (hF : Fintype.card F ≤ (Nat.clog 2 n) ^ B)
    (allow : 15 + 8 * B + Nat.clog 2 (Nat.card Stack.Device.Guide) ≤ E)
    (G : Diagram F x y) {u : ℕ} {L : Finset (Table F)}
    (hints : G.Admits u L) (size : G.cost ≤ m) (labels : L.card ≤ 2 ^ (v.box 2))
    (arity : (u : ℝ) ≤ (Nat.clog 2 n : ℝ) ^ b) :
    ∃ (P : Layer F (copies x v.batch) (copies y v.batch)) (i : P.State) (z : F),
      (fun f g => z * (P.graph i).eval f g) = power G.eval v.batch ∧
        v.Current s n m 0 E P ∧ P.template.count = 0 := by
  have hh : 1 < (Nat.clog 2 n : ℝ) := ok.2.1
  have ht' : (Nat.clog 2 n : ℝ) ^ b ≤ (2 : ℝ) ^ v.stack := ok.2.2.2.2.1
  have hpos : 0 < v.stack := by
    by_contra! h
    have hz := Nat.eq_zero_of_le_zero h
    rw [hz, pow_zero] at ht'
    exact (Real.one_lt_rpow hh hb).not_ge ht'
  have hn : 0 < n := by
    by_contra! h
    have hz := Nat.eq_zero_of_le_zero h
    norm_num [hz] at hh
  have hu : u ≤ 2 ^ v.stack := by exact_mod_cast arity.trans ht'
  obtain ⟨P, i, z, exactPower, ready, loopless, addr, blk, deg, port, l, ct, vol, ht⟩ :=
    Stack.start G hints size hpos hu hD hθ
  have bits : P.template.scheme.ℓ ≤ v.box E := l.le.trans (startup_labels_of_box fit labels hF allow)
  exact ⟨P, i, z, exactPower, initial (hn.trans_le hm) hm ready loopless addr blk deg port bits ct vol ht, ct⟩

theorem starting_layer (ok : v.Suits n T₀ a b ξ) (fit : v.Fits n B C)
    (hb : 0 < b) (hm : n ≤ m) (hD : 8 ≤ s.D) (hθ : s.floor ≤ 4)
    (hF : Fintype.card F ≤ (Nat.clog 2 n) ^ B)
    (allow : 15 + 8 * B + Nat.clog 2 (Nat.card Stack.Device.Guide) ≤ E)
    (G : Diagram F x y) {u : ℕ} {L : Finset (Table F)}
    (hints : G.Admits u L) (size : G.cost ≤ m) (labels : L.card ≤ Shaving.dictionary n)
    (arity : (u : ℝ) ≤ (Nat.clog 2 n : ℝ) ^ b) :
    ∃ (P : Layer F (copies x v.batch) (copies y v.batch)) (i : P.State) (z : F),
      (fun f g => z * (P.graph i).eval f g) = power G.eval v.batch ∧
        v.Current s n m 0 E P ∧ P.template.count = 0 :=
  starting_layer_of_box ok fit hb hm hD hθ hF allow G hints size (labels.trans (dictionary_le_box fit)) arity

end OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
end

/-! # The initialization budget of the realized stack -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
open Assembly

variable {δ : ℝ} {p : Design δ} {M n m B C E q : ℕ} {v : Levels p M}
  {s : Plan} {F : Type} [Field F] {x y : Wire}
  {P : Layer F (copies x v.batch) (copies y v.batch)}

theorem Current.init_budget (cur : v.Current s n m 0 E P)
    (fit : v.Fits n B C) (empty : P.template.count = 0)
    (upper : m ≤ n ^ 2) (reserve : 1 ≤ M)
    (hmeta : E ≤ q * p.groupRate) (hE : 1 ≤ E)
    (const : s.d + s.p + 1 ≤ 2 ^ v.j) {J : ℝ} (hJ : 0 ≤ J)
    (hh : 1 ≤ (Nat.clog 2 n : ℝ)) (hl : 1 ≤ Real.log (Nat.clog 2 n))
    (height : (P.height : ℝ) + 1 ≤ J * (Real.log (Nat.clog 2 n)) ^ 2) :
    let h : ℝ := Nat.clog 2 n
    ((140 * (P.snapshot.port.width + v.batch * (wd x + wd y)) + 1 : ℕ) : ℝ) ≤
      (10000 + 280 * J + 140) * (Real.log h) ^ 2 * v.expense h m (wd x + wd y) q := by
  let h : ℝ := Nat.clog 2 n
  let W := (10000 + 280 * J + 140) * (Real.log h) ^ 2
  let addr := P.template.scheme.m
  let nb := P.template.scheme.h
  let e := wd x + wd y
  let long := 140 * (8 * (addr + 2) + 2) + 1
  let short := 140 * (P.template.scheme.ℓ + 2 * (P.height + 1))
  let ext := 140 * (2 * (P.height + 1) + 1)
  have hm₀ : 2 ^ (addr + nb) ≤ v.allocation m := by
    simpa only [pow_zero, one_mul] using cur.seats
  have hbase : 1 ≤ p.overhead := (by decide : 1 ≤ 2).trans p.overhead_large
  have hm₁ : 2 ^ addr ≤ p.overhead ^ (0 + 1) * v.allocation m :=
    (Nat.pow_le_pow_right (by decide) (Nat.le_add_right ..)).trans
      (hm₀.trans (Nat.le_mul_of_pos_left _ (by positivity)))
  have hm₂ : addr ≤ 4 * Nat.clog 2 n := fit.address upper (Nat.zero_le _) hm₁
  have hr : v.remaining ≤ nb := by
    dsimp only [nb]
    rw [cur.left (Nat.zero_le _)]
    exact Nat.le_add_right ..
  have seats : 2 ^ (addr + nb) ≤ p.overhead ^ v.j * v.allocation m :=
    hm₀.trans (Nat.le_mul_of_pos_left _ (by positivity))
  have hhi : P.volume = 2 ^ addr + v.batch * e := by
    simpa only [addr, e, wd_copies, Nat.mul_add, Nat.add_assoc] using cur.volume
  have actual := Stack.start_cost P (H:=2 ^ addr) (B:=nb) le_rfl rfl cur.degree empty hhi
  have pay : 140 * (P.snapshot.port.width + v.batch * e) + 1 ≤
      2 ^ addr * long + 2 ^ (addr + nb) * short + v.batch * e * ext := calc
    _ ≤ 140 * (2 ^ addr * (8 * (addr + 2) + 2) + 2 ^ addr * 2 ^ nb * (P.template.scheme.ℓ + 2 * (P.height + 1)) +
          (2 * (P.height + 1) + 1) * (v.batch * e)) + 1 := actual
    _ ≤ 140 * (2 ^ addr * (8 * (addr + 2) + 2) + 2 ^ addr * 2 ^ nb * (P.template.scheme.ℓ + 2 * (P.height + 1)) +
          (2 * (P.height + 1) + 1) * (v.batch * e)) + 2 ^ addr := by gcongr; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    _ = _ := by rw [pow_add]; unfold long short ext; ring
  have hlog : 0 ≤ Real.log h := zero_le_one.trans hl
  have hlog₂ : 1 ≤ (Real.log h) ^ 2 := one_le_pow₀ hl
  have wbig : 10000 ≤ W := by
    unfold W
    exact le_trans (show (10000 : ℝ) ≤ 10000 + 280 * J + 140 by linarith)
      (le_mul_of_one_le_right (by positivity) hlog₂)
  have hl₁ : (long : ℝ) ≤ W * h ^ M := calc
    _ ≤ 10000 * h := by
      have hraddr : (addr : ℝ) ≤ 4 * h := by unfold h; exact_mod_cast hm₂
      unfold long; push_cast
      linarith only [hraddr, hh]
    _ ≤ W * h ^ M := mul_le_mul wbig
      (by simpa only [pow_one] using (pow_le_pow_right₀ hh reserve)) (by positivity) (by positivity)
  have hspan : v.span ≤ 2 ^ v.j := (Nat.le_mul_of_pos_left _ (by omega : 0 < B + 4)).trans fit.span
  have hbox₁ : 2 ^ v.j ≤ v.box 1 := by
    unfold Levels.box
    rw [one_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hbox : 2 ^ v.j ≤ v.box E := hbox₁.trans (v.box_mono hE)
  have ht : P.height + 1 ≤ 2 * v.box E := by
    have h₁ := cur.height
    have h₂ := hspan.trans hbox
    have h₃ := const.trans hbox
    omega
  have hlen : P.template.scheme.ℓ ≤ v.box E := by
    simpa only [empty, add_zero, pow_zero, one_mul] using cur.labels
  have hs₁ : short ≤ 700 * 2 ^ (q * v.group) := calc
    _ ≤ 700 * v.box E := by
      unfold short
      omega
    _ ≤ _ := Nat.mul_le_mul_left _ (v.box_le_group_power hmeta)
  have hs₂ : (short : ℝ) ≤ W * (2 : ℝ) ^ (q * v.group) := calc
    _ ≤ 700 * (2 : ℝ) ^ (q * v.group) := by exact_mod_cast hs₁
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_trans (by norm_num) wbig) (by positivity)
  have he₁ : (ext : ℝ) ≤ W := by
    unfold ext W
    push_cast
    nlinarith only [height, hlog₂]
  exact v.phase_expense (by linarith) (by linarith : 0 ≤ W) hr seats pay hl₁ hs₂ he₁

end OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
end
