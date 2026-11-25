import OAI.LinearAlgebra.MatrixExponent.Assembly.Boundary
import OAI.LinearAlgebra.MatrixExponent.Coloring.VectorSort
import OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
import OAI.LinearAlgebra.MatrixExponent.Assembly.Serial
import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Presents
import OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Frame
import OAI.LinearAlgebra.MatrixExponent.Assembly.Hold
import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Sweep
import OAI.LinearAlgebra.MatrixExponent.Assembly.RetagStore
import OAI.LinearAlgebra.MatrixExponent.Assembly.Prepare.Parcel

/-! # Certifying a directed presentation by checking individual bits -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Seating
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {r : S.format.obj} {a b : Wire}
  {G : Diagram F a b} (p : S.Seating r G)

def Bond (x y : G.End) : Prop :=
  S.Joins r (p.ends x) (p.ends y) ∧ S.Joins r (p.ends y) (p.ends x) ∧
    S.direction r (p.ends x).1 = x.isRight ∧ S.direction r (p.ends y).1 = y.isRight

theorem Bond.swap {p} {x y : G.End} (h : Bond (S := S) (r := r) p x y) : p.Bond y x :=
  ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩

def Free (x : G.End) : Prop := S.peer r (p.ends x).1 = none ∧ S.direction r (p.ends x).1 = x.isRight

structure Connected : Prop where
  used : ∀ i, S.peer r i ≠ none → 0 < S.width r i
  bond : ∀ e, p.Bond (.inl (.inr e)) (.inr (.inr e))
  input : ∀ i, p.Free (.inl (.inl i))
  output : ∀ i, p.Free (.inr (.inl i))

namespace Connected
variable {p} (h : p.Connected)
include h

private theorem other {q : S.Pin r} {j : S.Span} (he : S.peer r q.1 = some j) :
    S.peer r j = some q.1 ∧ q.2.val < S.width r j ∧ S.direction r q.1 ≠ S.direction r j := by
  obtain ⟨x, rfl⟩ := p.ends.surjective q
  have aux {y : G.End} (b : p.Bond x y) (hn : x.isRight ≠ y.isRight) :
      S.peer r j = some (p.ends x).1 ∧ (p.ends x).2.val < S.width r j ∧
        S.direction r (p.ends x).1 ≠ S.direction r j := by
    rw [b.1.1, Option.some.injEq] at he
    subst j
    rw [b.1.2, b.2.2.1, b.2.2.2]
    exact ⟨b.2.1.1, (p.ends y).2.isLt, hn⟩
  rcases x with (i|e)|(i|e)
  · rw [(h.input i).1] at he
    cases he
  · exact aux (h.bond e) Bool.false_ne_true
  · rw [(h.output i).1] at he
    cases he
  · exact aux (h.bond e).swap Bool.false_ne_true.symm

private theorem size {i j : S.Span} (he : S.peer r i = some j) : S.width r i ≤ S.width r j := by
  by_contra! hn
  exact (lt_irrefl _) (h.other (q := ⟨i, ⟨_, hn⟩⟩) he).2.1

theorem proper : S.Proper r := by
  intro i j he
  have hi := h.used i (by rw [he]; simp)
  obtain ⟨hj, _, hd⟩ := h.other (q := ⟨i, ⟨0, hi⟩⟩) he
  exact ⟨hj, le_antisymm (h.size he) (h.size hj), hd⟩

def presentation : S.Presentation r G :=
  ⟨p, h.proper, fun i => (h.bond i).1, fun i => (h.input i).1, fun i => (h.output i).1⟩

theorem directed : h.presentation.Directed := by
  rintro ((i|e)|(i|e))
  · exact (h.input i).2
  · exact (h.bond e).2.2.1
  · exact (h.output i).2
  · exact (h.bond e).2.2.2

end Connected
end OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Seating
end

section
/-! # Comparing the two address lists at one host -/

namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Alias
open Coloring

abbrev Input (m d d' p : ℕ) : Format :=
  .pair (.vec p (.vec d (.addr m))) (.vec d' (.vec p (.addr m)))

abbrev Output (d d' p : ℕ) : Format :=
  .vec p (.vec d (.vec d' (.vec p .bit)))

def mask {m d d' p : ℕ} (x : (Input m d d' p).obj) : (Output d d' p).obj :=
  fun i j y t => decide (x.1 i j = x.2 y t)

theorem mask_circuit (F : Type) [Field F] (m d d' p : ℕ) :
    Circuit F (Input m d d' p) (Output d d' p) mask ((100 + m + 2 ^ d + 2 ^ d' + 2 ^ p) ^ 100) := by
  let A := Input m d d' p
  let D := Format.vec p (.vec d (.vec d' (.vec p (.pair (.addr m) (.addr m)))))
  let f : A.obj → D.obj := fun x i j y t => (x.1 i j, x.2 y t)
  have wire : Circuit F A D f (A.width + 2 * D.width) := by
    apply Circuit.project (A := A) (D := D) (fun (i, j, y, t, b) =>
      Sum.elim (fun z => Sum.inl (i, j, z)) (fun z => Sum.inr (y, t, z)) b)
    rintro x ⟨i, j, y, t, z|z⟩ <;> rfl
  have eqs := Circuit.map (h := p) _ (fun _ =>
    Circuit.map (h := d) _ (fun _ =>
      Circuit.map (h := d') _ (fun _ =>
        Circuit.map (h := p) _ (fun _ => numeric_eq F m))))
  refine (wire.comp eqs).mono ?_
  simp only [A, D, Input, Format.width_vec, Format.width_pair, Format.width_addr]
  let s := 100 + m + 2 ^ d + 2 ^ d' + 2 ^ p
  have h₁ : 0 ≤ 2 ^ d := Nat.zero_le _
  have h₂ : 0 ≤ 2 ^ d' := Nat.zero_le _
  have h₃ : 0 ≤ 2 ^ p := Nat.zero_le _
  have hs : 100 ≤ s := by dsimp [s]; omega
  have hm : m ≤ s := by dsimp [s]; omega
  have hd : 2 ^ d ≤ s := by dsimp [s]; omega
  have hd' : 2 ^ d' ≤ s := by dsimp [s]; omega
  have hp : 2 ^ p ≤ s := by dsimp [s]; omega
  calc
    _ ≤ s * (s * s) + s * (s * s) + 2 * (s * (s * (s * (s * (s + s))))) + s * (s * (s * (s * (2 * s + s)))) := by
      gcongr; omega
    _ = 2 * s ^ 3 + 7 * s ^ 5 := by ring
    _ ≤ 9 * s ^ 5 := by
      have := Nat.pow_le_pow_right (show 0 < s by omega) (show 3 ≤ 5 by decide)
      omega
    _ ≤ s ^ 6 := by rw [show s ^ 6 = s * s ^ 5 by ring]; gcongr; omega
    _ ≤ s ^ 100 := Nat.pow_le_pow_right (by omega) (by decide)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Alias
end

/-! # Ordered reads from the short records of neighboring hosts -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
open Coloring

private theorem read_budget (n u v l : ℕ) :
    (100 + (n + u + v + l + u * l)) ^ 50 ≤ (100 + n + u + v + l) ^ 100 := by
  rw [show 100 = 2 * 50 from rfl, pow_mul]
  gcongr
  ring_nf
  omega

/-- For each request column, gather the whole neighbor list at the requested block,
then select the requested neighbor. Padding repeats existing rows and is removed
by a fixed projection, so arbitrary repetitions and order are preserved. -/
theorem local_read (F : Type) [Field F] (n a d p l : ℕ) (ha : a ≤ n) :
    Circuit F (.pair (.vec d (.vec n (.addr l))) (.vec a (.vec p (.pair (.addr d) (.addr n)))))
      (.vec a (.vec p (.addr l))) (fun x i j => x.1 (x.2 i j).1 (x.2 i j).2)
      (2 ^ n * (100 + n + 2 ^ d + 2 ^ p + l) ^ 100) := by
  let A := Format.pair (.vec d (.vec n (.addr l))) (.vec a (.vec p (.pair (.addr d) (.addr n))))
  let U := Format.vec d (.addr l)
  let k := n + 2 ^ d + 2 ^ p + l + 2 ^ d * l
  have := Nat.lt_two_pow_self (n := d)
  have := Nat.lt_two_pow_self (n := p)
  have hn : n ≤ k := by unfold k; omega
  have hd : 2 ^ d ≤ k := by unfold k; omega
  have hp : 2 ^ p ≤ k := by unfold k; omega
  have hl : l ≤ k := by unfold k; omega
  have hdn : d + n ≤ k := by unfold k; omega
  have hu : U.width ≤ k := by rw [Format.width_vec, Format.width_addr]; unfold k; omega
  have hrows : 2 ^ a ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) ha
  let up := Fin.castLEEmb hrows
  let down := Function.invFun up
  have cancel (i : B a) : down (up i) = i := Function.leftInverse_invFun up.injective i
  have hA : A.width ≤ 2 ^ n * (100 + k) ^ 2 := by
    simp only [A, Format.width_pair, Format.width_vec, Format.width_addr]
    rw [mul_left_comm (2 ^ d)]
    calc
      _ ≤ 2 ^ n * k + 2 ^ n * (k * k) := by
        have h : 2 ^ d * l ≤ k := by unfold k; omega
        gcongr
      _ ≤ _ := by rw [← mul_add]; gcongr; ring_nf; omega
  have hv (V : Format) (hv : V.width ≤ k) : (Format.vec n V).width ≤ 2 ^ n * (100 + k) ^ 2 := by
    rw [Format.width_vec]
    exact Nat.mul_le_mul_left _ (by nlinarith only [hv])
  have table : Cheap F n k A (.vec n U) (fun x i t => x.1 t i) 3 :=
    Cheap.project F hA (hv U hu) (fun z => .inl (z.2.1, z.1, z.2.2)) (fun _ _ => rfl)
  have each (j : B p) : Cheap F n k A (.vec n (.addr l))
      (fun x i => x.1 (x.2 (down i) j).1 (x.2 (down i) j).2) 13 := by
    have block : Cheap F n k A (Perm n) (fun x i => (x.2 (down i) j).2) 3 :=
      Cheap.project F hA (hv (.addr n) (by simpa))
        (fun z => .inr (down z.1, j, .inr z.2)) (fun _ _ => rfl)
    have near : Cheap F n k A (.vec n (.addr d)) (fun x i => (x.2 (down i) j).1) 3 :=
      Cheap.project F hA (hv (.addr d) (by rw [Format.width_addr]; omega))
        (fun z => .inr (down z.1, j, .inl z.2)) (fun _ _ => rfl)
    have records := (table.pair block).comp (Cheap.lookup F n k U hn hu)
    exact (near.pair records).zip.comp
      (Cheap.map (fun _ => _) (fun _ => Match.read_one F (.addr l) (by omega) (by simpa) hd))
  let Z := Format.vec p (.vec n (.addr l))
  let W := Format.vec a (.vec p (.addr l))
  have hz : Z.width ≤ 2 ^ n * (100 + k) ^ 2 := by
    simp only [Z, Format.width_vec, Format.width_addr, pow_two]
    rw [mul_left_comm (2 ^ p)]
    gcongr <;> omega
  have hw : W.width ≤ 2 ^ n * (100 + k) ^ 2 := by
    simp only [W, Format.width_vec, Format.width_addr, pow_two]
    gcongr <;> omega
  have out : Cheap F n k Z W (fun x i j => x j (up i)) 3 :=
    Cheap.project F hz hw (fun z => (z.2.1, up z.1, z.2.2)) (fun _ _ => rfl)
  have ans := (Cheap.share _ each hp).comp out
  simp only [Function.comp_def, cancel] at ans
  obtain ⟨m, hm, hcost⟩ := ans.mono (d := 50) (by decide)
  refine hm.mono ((show m ≤ 2 ^ n * (100 + k) ^ 50 by omega).trans ?_)
  exact Nat.mul_le_mul_left _ (read_budget n (2 ^ d) (2 ^ p) l)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
end

/-! # Reattaching the frozen tables in their original port order -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Presentation
open Packing
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {S : Scheme F} {r : S.format.obj}
    {G : Diagram F x y} (p : S.Presentation r G) (Z : Freeze G)

local notation "J" => Z.border.attach Z.core

def original : (J).V ≃ G.V :=
  (Equiv.sumComm _ _).trans (Equiv.sumCompl Z.frozen)

def joinedPin (i : (J).V) : (J).Port i ≃ S.LocalPin r (p.vertex (original Z i)) :=
  match i with
  | .inl v => p.pin v.val
  | .inr v => p.pin v.val

def joinedSeat : S.Seating r J where
  vertex := (original Z).toEmbedding.trans p.vertex
  pin := p.joinedPin Z
  cover i := by
    obtain ⟨v, hv⟩ := p.cover i
    obtain ⟨u, rfl⟩ := (original Z).surjective v
    exact ⟨u, hv⟩
  sample v t := by rcases v with v|v <;> exact p.sample v.val t
  vacant v hv t := p.vacant v (by
    rintro ⟨i, rfl⟩
    obtain ⟨u, rfl⟩ := (original Z).surjective i
    exact hv ⟨u, rfl⟩) t

private def joinedEnd : (J).End ≃ G.End :=
  ((Equiv.refl _).sumCongr Z.edges).sumCongr ((Equiv.refl _).sumCongr Z.edges)

theorem joined_at (i : (J).End) :
    (p.joinedSeat Z).ends i = p.toSeating.ends (joinedEnd Z i) := by
  rcases i with (_|_|_|_)|(_|_|_|_) <;> rfl

def joined : S.Presentation r J where
  toSeating := p.joinedSeat Z
  proper := p.proper
  input i := by rw [joined_at]; exact p.input i
  output i := by rw [joined_at]; exact p.output i
  internal i := by rw [joined_at, joined_at]; exact p.internal (Z.edges i)

theorem joined_directed (hd : p.Directed) : (p.joined Z).Directed := by
  intro i
  change S.direction r ((p.joinedSeat Z).ends i).1 = _
  rw [joined_at, hd]
  cases i <;> rfl

theorem joined_boundary (i : slots x ⊕ slots y) :
    (p.joined Z).boundary i = p.boundary i := by
  apply Subtype.ext
  cases i <;> rfl

end OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Presentation
end

section
/-!
# Reading neighboring rows and comparing old host addresses

The comparison bits are computed once per host and reused in every row.
The width of an address therefore contributes independently of the row count.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Inspect
open Coloring

abbrev Packet (m d p a : ℕ) (A : Format) : Format :=
  .pair (.vec p (.addr m)) (.pair (.vec p (.vec d (.addr m))) (.vec a A))

abbrev Input (m d m' d' p a : ℕ) (A : Format) :=
  Fmt.bank m' d' (Packet m d p a A)

abbrev Row (d d' p : ℕ) (A : Format) : Format :=
  .pair (Alias.Output d d' p) (.pair A (.vec d' A))

abbrev Output (d m' d' p a : ℕ) (A : Format) : Format :=
  .vec m' (.vec a (Row d d' p A))

def cost (m d m' d' p a : ℕ) (A : Format) (v N : ℕ) :=
  gatherCost m' d' v N +
  56 * (Input m d m' d' p a A).width +
  32 * (Format.vec m' (.vec d' (Packet m d p a A))).width +
  8 * (Format.vec m' (Alias.Input m d d' p)).width +
  4 * (Format.vec m' (Alias.Output d d' p)).width +
  8 * (Output d m' d' p a A).width +
  4 * (2 ^ m' * (100 + m + 2 ^ d + 2 ^ d' + 2 ^ p) ^ 100)

variable {F : Type} [Field F] {u v N m d m' d' p a : ℕ}
  {A : Format} {L : Set (Table F)} {I : Type*}

def view (x : (Input m d m' d' p a A).obj) : (Output d m' d' p a A).obj :=
  fun i j =>
    (Alias.mask ((x i).2.2.1, fun t => (x ((x i).1 t)).2.1),
     (x i).2.2.2 j, fun t => (x ((x i).1 t)).2.2.2 j)

theorem run (hu : 3 ≤ u) (ht : Access F u L (m' + d') v N)
    (hc : (Packet m d p a A).width ≤ v) (X : I → (Input m d m' d' p a A).obj)
    (hx : ∀ i, Fmt.Reciprocal (Packet m d p a A) (X i)) :
    Computes F u L (Input m d m' d' p a A) (Output d m' d' p a A)
      X (fun i => view (X i)) (fun _ => 1) (cost m d m' d' p a A v N) := by
  let T := Input m d m' d' p a A
  let R := Format.vec m' (.vec d' (Packet m d p a A))
  let U := Format.vec m' (Alias.Input m d d' p)
  let V := Format.vec m' (Alias.Output d d' p)
  let W := Format.pair T R
  let Y := Format.pair V W
  let Z := Output d m' d' p a A
  let select : W.obj → U.obj := fun x i => ((x.1 i).2.2.1, fun t => (x.2 i t).1)
  have pre : Circuit F W U select (W.width + 2 * U.width) := by
    apply Circuit.project (A := W) (D := U) (fun (i, b) =>
      Sum.elim (fun y => .inl (i, .inr (.inr (.inl y))))
        (fun t => .inr (i, t.1, .inl t.2)) b)
    rintro x ⟨i, b|b⟩ <;> rfl
  have cmp := pre.comp (Circuit.map (h := m') _ (fun _ => Alias.mask_circuit F m d d' p))
  let arrange : Y.obj → Z.obj := fun x i j =>
    (x.1 i, (x.2.1 i).2.2.2 j, fun t => (x.2.2 i t).2.2 j)
  have post : Circuit F Y Z arrange (Y.width + 2 * Z.width) := by
    apply Circuit.project (A := Y) (D := Z) (fun (i, j, b) =>
      Sum.elim (fun y => .inl (i, y)) (Sum.elim
        (fun y => .inr (.inl (i, .inr (.inr (.inr (j, y))))))
        (fun t => .inr (.inr (i, t.1, .inr (.inr (j, t.2)))))) b)
    rintro x ⟨i, j, b|b|b⟩ <;> rfl
  have read := (cmp.pair (Circuit.id F W)).comp post
  have keep := Computes.of_map (L := L) (x := X) (Map.circuit hu (Circuit.id F T)) (fun _ => rfl)
  have both := keep.pair hu (gather_neighbors (Packet m d p a A) hu ht hc X hx)
  have h := both.comp (Computes.of_map (Map.circuit hu read)
    (y := fun i => view (X i)) (fun _ => rfl))
  simp only [one_mul] at h
  refine h.mono ?_
  unfold cost
  simp only [W, Y, Format.width_pair, T, R, U, V, Z]
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Inspect
end

/-!
# Keeping a full presentation beside a frozen core

The status mask sends mobile vertices to lane zero and frozen
vertices to lane one. The bit order within each span is unchanged.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring
open scoped Classical

variable {F : Type} [Field F]

namespace Pattern
variable {d k e : ℕ} (P : Pattern F d k e) (mobile : Bool) (peerMobile : B d → Bool)

def lane (mobile : Bool) : B 1 := if mobile then 0 else 1

def reseat : Pattern F d 1 e where
  width j s := if j = lane mobile then P.width 0 s else 0
  direction _ s := P.direction 0 s
  peer j s := if j = lane mobile
    then (P.peer 0 s).map (fun a => (a.1, lane (peerMobile a.1), a.2.2)) else none
  value j z := if h : j = lane mobile
    then P.value 0 (fun s i => z s (i.cast (ite_eq_left h).symm)) else 1

end Pattern

namespace Template
variable (D : Template F) (u : ℕ) (scale : ℝ)

abbrev borderCode := Format.pair (.addr D.scheme.cutCode.width) (.addr D.count)

abbrev border : Attachment (D.cut u scale) where
  k := 1
  e := D.scheme.e
  ℓ := D.borderCode.width
  decode i :=
    let k := D.scheme.cutCode.serial.symm (D.borderCode.serial.symm i).1
    (D.scheme.decode k.1).reseat k.2.1 k.2.2
  live i j :=
    let c := D.borderCode.serial.symm i
    decide (0 < D.load c.2 ∧ j = Pattern.lane (D.scheme.cutCode.serial.symm c.1).2.1)
  charge i _ := D.load (D.borderCode.serial.symm i).2
  coreSpan := Function.Embedding.refl _

def enclose (r : D.format.obj) : (D.border u scale).format.obj :=
  (D.remove u scale r, fun v i => D.borderCode.serial ((((D.remove u scale r).1 v).2 i), D.counter r v i))

theorem border_length : (D.border u scale).ℓ = D.scheme.ℓ + 1 + 2 ^ D.scheme.d + D.count := by
  change D.borderCode.width = _
  rw [borderCode, Format.width_pair, Format.width_addr, Format.width_addr]
  exact congrArg (·+D.count) D.scheme.cut_length

end Template
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-! # Widths, peers and table values under the two-lane placement -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.FreezeInput
open Coloring
open scoped Classical
variable {F : Type} [Field F] (D : Template F) (u : ℕ) (scale : ℝ) (r : D.format.obj)
local notation "S" => D.scheme
local notation "A" => D.border u scale
local notation "U" => Attachment.scheme (D.border u scale)
local notation "out" => Attachment.rows (D.border u scale) (D.enclose u scale r)

def dest (v : (S).Vtx) : (U).Vtx := (v.1, v.2.1, Pattern.lane (D.mobile r v.1))
abbrev newSpan (t : (S).Span) : (U).Span := (dest D u scale r t.1, t.2)
def src (v : (U).Vtx) : (S).Vtx := (v.1, v.2.1, 0)

theorem pattern (v : (U).Vtx) :
    (U).pattern out v = ((S).pattern r.1 (src D u scale v)).reseat (D.mobile r v.1) (D.mobile r ∘ D.nav r v.1) := by
  simp only [Scheme.pattern, Attachment.rows, Attachment.scheme, border, enclose, remove, Scheme.remove,
    Equiv.symm_apply_apply, src, nav]

theorem width (v : (U).Vtx) (i : B D.scheme.e) :
    (U).width out (v, i) = if v.2.2 = Pattern.lane (D.mobile r v.1) then (S).width r.1 (src D u scale v, i) else 0 := by
  rw [Scheme.width, pattern]
  rfl

theorem peer (v : (U).Vtx) (i : B D.scheme.e) :
    (U).peer out (v, i) = if v.2.2 = Pattern.lane (D.mobile r v.1)
      then ((S).peer r.1 (src D u scale v, i)).map (newSpan D u scale r) else none := by
  rw [Scheme.peer, pattern]
  unfold Pattern.reseat
  dsimp only
  split
  · simp only [Scheme.peer, Option.map_map]
    rfl
  · rfl

theorem untouched (v : (U).Vtx) (h : v.2.2 ≠ Pattern.lane (D.mobile r v.1))
    (t : (U).LocalPin out v → Bool) : (U).table out v t = 1 := by
  have aux (q : Pattern F D.scheme.d 1 D.scheme.e)
      (he : q = ((S).pattern r.1 (src D u scale v)).reseat (D.mobile r v.1) (D.mobile r ∘ D.nav r v.1))
      (x : ∀ j, Fin (q.width v.2.2 j) → Bool) : q.value v.2.2 x = 1 := by
    subst q; exact dite_eq_right h
  exact aux _ (pattern D u scale r v) _

variable (h : D.scheme.k = 0)

include h in
omit [Field F] in
theorem slot (v : (S).Vtx) : v.2.2 = 0 := by
  apply Fin.ext
  have hv := v.2.2.isLt
  simp only [h, pow_zero, Fin.val_zero] at *
  omega

include h in
theorem src_dest (v : (S).Vtx) : src D u scale (dest D u scale r v) = v :=
  Prod.ext rfl (Prod.ext rfl (slot D h v).symm)

theorem dest_src (v : (U).Vtx) (hv : v.2.2 = Pattern.lane (D.mobile r v.1)) :
    dest D u scale r (src D u scale v) = v := Prod.ext rfl (Prod.ext rfl hv.symm)

include h in
theorem width_at (t : (S).Span) : (U).width out (newSpan D u scale r t) = (S).width r.1 t := by
  rw [newSpan, width, src_dest _ _ _ _ h]
  simp only [dest, ite_true]

include h in
theorem peer_at (t : (S).Span) :
    (U).peer out (newSpan D u scale r t) = ((S).peer r.1 t).map (newSpan D u scale r) := by
  rw [newSpan, peer, src_dest _ _ _ _ h]
  simp only [dest, ite_true]

include h in
theorem direction_at (t : (S).Span) :
    (U).direction out (newSpan D u scale r t) = (S).direction r.1 t := by
  rw [Scheme.direction, pattern]
  change ((S).pattern r.1 t.1).direction 0 t.2 = _
  rw [Scheme.direction, slot D h t.1]

def pin (v : (S).Vtx) : (S).LocalPin r.1 v ≃ (U).LocalPin out (dest D u scale r v) :=
  Equiv.sigmaCongrRight fun j => finCongr (width_at D u scale r h (v, j)).symm

private theorem preserved {d k e : ℕ} (P : Pattern F d k e) (q : Pattern F d 1 e)
    (j : B k) (hj : j = 0) (b : Bool) (f : B d → Bool) (he : q = P.reseat b f)
    (hw : ∀ i, P.width j i = q.width (Pattern.lane b) i)
    (z : ∀ i, Fin (q.width (Pattern.lane b) i) → Bool) :
    q.value (Pattern.lane b) z = P.value j (fun i t => z i (t.cast (hw i))) := by
  subst q; subst j
  exact dite_eq_left rfl

theorem table_at (v : (S).Vtx) (t : (U).LocalPin out (dest D u scale r v) → Bool) :
    (U).table out (dest D u scale r v) t = (S).table r.1 v (t ∘ pin D u scale r h v) :=
  preserved _ _ _ (slot D h v) _ _ (pattern D u scale r (dest D u scale r v))
    (fun i => (width_at D u scale r h (v, i)).symm) (fun j k => t ⟨j, k⟩)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.FreezeInput
end

/-!
# Computing both records at the input to a frozen round

Ask for the cut on the first copy and carry the status bits and
original labels on the second. Serializing a short label only
reindexes its positions.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template
open Coloring
open scoped Classical
variable {F : Type} [Field F] (D : Template F)

private theorem serial_bits (A : Format) :
    ∃ e : (Format.addr A.width).pins → A.pins,
      ∀ x i, (Format.addr A.width).code (A.serial x) i = A.code x (e i) := by
  refine ⟨@Fintype.equivOfCardEq _ _ (slotsFintype _) A.finite
    ((card_slots _).trans (wd_word _)), fun x i => ?_⟩
  rw [Format.serial, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

private abbrev RequestCut := D.scheme.cutInput.pair D.format
private abbrev CutReply := D.scheme.cut.format.pair D.format

private def requestCut (s : D.format.obj) : D.RequestCut.obj := ((s.1, D.mobile s), s)

private theorem ask_cut :
    Circuit F D.format D.RequestCut D.requestCut (D.format.width + 34 * D.RequestCut.width) := by
  have h : Install.Depends (D.RequestCut.code ∘ D.requestCut ∘ D.format.code.symm) 1 := by
    have pin (i : D.RequestCut.pins) (j : D.format.pins) (f : Bool → Bool)
        (he : ∀ t, D.RequestCut.code (D.requestCut t) i = f (D.format.code t j)) :
        ∃ s : Finset D.format.pins, s.card ≤ 1 ∧ ∀ x y, (∀ l ∈ s, x l = y l) →
          (D.RequestCut.code ∘ D.requestCut ∘ D.format.code.symm) x i =
          (D.RequestCut.code ∘ D.requestCut ∘ D.format.code.symm) y i := by
      refine ⟨{j}, by simp, fun x y h => ?_⟩
      simp only [Function.comp_apply, he, Equiv.apply_symm_apply, h j (by simp)]
    rintro ((i|⟨v, b⟩)|i)
    · exact pin _ (.inl i) id (fun _ => rfl)
    · exact pin _ (.inr (v, .inl (.inr b))) Bool.not (fun _ => rfl)
    · exact pin _ i id (fun _ => rfl)
  exact h.bnet F

variable (u : ℕ) (scale : ℝ)

private def emitCut (s : D.CutReply.obj) : (D.border u scale).format.obj :=
  ((s.1, fun v => ((s.2.2 v).1, D.flags s.2 v, fun j =>
    D.cutCounter.serial (D.frozen s.2 v, D.counter s.2 v j))),
    fun v j => D.borderCode.serial ((s.1 v).2 j, D.counter s.2 v j))

private theorem emit_cut :
    Circuit F D.CutReply (D.border u scale).format (D.emitCut u scale)
      (D.CutReply.width + 2 * (D.border u scale).format.width) := by
  obtain ⟨k, hk⟩ := serial_bits D.cutCounter
  obtain ⟨l, hl⟩ := serial_bits D.borderCode
  let counter (v : B D.scheme.m) (j : B D.scheme.h) : D.cutCounter.pins → D.CutReply.pins
    | .inl b => .inr (.inr (v, .inl (.inr b)))
    | .inr b => .inr (.inr (v, .inr (.inr (j, b))))
  let border (v : B D.scheme.m) (j : B D.scheme.h) : D.borderCode.pins → D.CutReply.pins
    | .inl b => .inl (v, .inr (j, b))
    | .inr b => .inr (.inr (v, .inr (.inr (j, b))))
  let pin : (D.border u scale).format.pins → D.CutReply.pins
    | .inl (.inl i) => .inl i
    | .inl (.inr (v, .inl i)) => .inr (.inr (v, .inl i))
    | .inl (.inr (v, .inr (.inl i))) => .inr (.inr (v, .inr (.inl i)))
    | .inl (.inr (v, .inr (.inr (j, i)))) => counter v j (k i)
    | .inr (v, j, i) => border v j (l i)
  refine Circuit.project pin ?_
  rintro s ((i | ⟨v, i|i|⟨j, i⟩⟩) | ⟨v, j, i⟩)
  · rfl
  · rfl
  · rfl
  · refine (hk (D.frozen s.2 v, D.counter s.2 v j) i).trans ?_
    change _ = D.CutReply.code s (counter v j (k i))
    cases k i <;> rfl
  · refine (hl ((s.1 v).2 j, D.counter s.2 v j) i).trans ?_
    change _ = D.CutReply.code s (border v j (l i))
    cases l i <;> rfl

def encloseCost := D.scheme.cutCost + 200 * (D.format.width + D.scheme.cutInput.width +
  D.scheme.cut.format.width + (D.border u scale).format.width)

theorem enclose_net {w : ℕ} {L : Set (Table F)} (hw : 3 ≤ w) :
    Map F w L D.format (D.border u scale).format (D.enclose u scale) (D.encloseCost u scale) := by
  have cut := (D.scheme.map_remove (L := L) hw).par (Map.circuit hw (Circuit.id F D.format))
  have network := ((Map.circuit hw D.ask_cut).comp cut).comp (Map.circuit hw (D.emit_cut u scale))
  refine network.mono ?_
  unfold encloseCost RequestCut CutReply
  rw [Format.width_pair D.scheme.cutInput D.format, Format.width_pair D.scheme.cut.format D.format]
  omega

local notation "m" => D.scheme.m
local notation "p" => (2 ^ D.scheme.d)
local notation "ℓ" => D.scheme.ℓ
local notation "h" => D.scheme.h

private theorem enclose_price :
    D.encloseCost u scale =
      2 ^ m * (848 * (p * m) + 800 * p + 1040 + 12 * (100 + (m + p)) ^ 12) +
      2 ^ (m + h) * (1048 * ℓ + 600 * D.count + 608 * p + 808) := by
  have hc : (D.cut u scale).count = 1 + D.count := by
    change D.cutCounter.width = _
    rw [cutCounter, Format.width_pair, Format.width_bit, Format.width_addr]
  have hi : D.scheme.cutInput.width = 2 ^ m * (p * m + 2 ^ h * ℓ) + 2 ^ m := by
    rw [Scheme.cutInput, Format.width_pair, Scheme.format, Fmt.width_rows, Format.width_addr,
      Format.width_vec, Format.width_bit, mul_one]
  have hr : D.scheme.cut.format.width = 2 ^ m * (p * m + 2 ^ h * (ℓ + 1 + p)) := by
    rw [Scheme.format, Fmt.width_rows, Format.width_addr, Scheme.cut_length]
  have ho : (D.border u scale).format.width =
      2 ^ m * (p * (m + 2) + 2 + 2 ^ h * ((ℓ + 1 + p) + (1 + D.count))) + 2 ^ m * (2 ^ h * (ℓ + 1 + p + D.count)) := by
    rw [Attachment.width, border_length, Template.width, hc]
    change 2 ^ m * (p * (m + 2) + 2 + 2 ^ h * (D.scheme.cut.ℓ + (1 + D.count))) + _ = _
    rw [Scheme.cut_length]
  rw [encloseCost, Scheme.cutCost, hi, hr, ho, D.width, pow_add]
  generalize (100 + (m + p)) ^ 12 = w
  ring

/-- The charge repeated in every cell is independent of the host address. -/
theorem enclose_bound {s : ℕ} (hs : 10000 + p + ℓ + D.count ≤ s) :
    D.encloseCost u scale ≤ 2 ^ m * (s + m) ^ 13 + 2 ^ (m + h) * s ^ 2 := by
  rw [enclose_price]
  generalize p = n at *
  have hs' : 10000 ≤ s := by omega
  let t := s + m
  have hn : n ≤ t := by unfold t; omega
  have hm : m ≤ t := Nat.le_add_left ..
  have ht : 10000 ≤ t := hs'.trans (Nat.le_add_right ..)
  have hpow : (100 + (m + n)) ^ 12 ≤ t ^ 12 := Nat.pow_le_pow_left (by unfold t; omega) _
  have hprod : n * m ≤ t ^ 12 := by
    refine (Nat.mul_le_mul hn hm).trans ?_
    rw [← pow_two]
    exact Nat.pow_le_pow_right (by omega) (by decide)
  have ht' : t ≤ t ^ 12 := Nat.le_self_pow (by decide) t
  have h₁ : 848 * (n * m) + 800 * n + 1040 + 12 * (100 + (m + n)) ^ 12 ≤ t ^ 13 := calc
    _ ≤ t ^ 12 * 3000 := by omega
    _ ≤ t ^ 12 * t := Nat.mul_le_mul_left _ (by omega)
    _ = _ := (pow_succ ..).symm
  have h₂ : 1048 * ℓ + 600 * D.count + 608 * n + 808 ≤ s ^ 2 := calc
    _ ≤ s * 4000 := by omega
    _ ≤ s * s := Nat.mul_le_mul_left _ (by omega)
    _ = _ := (pow_two _).symm
  exact Nat.add_le_add (Nat.mul_le_mul_left _ h₁) (Nat.mul_le_mul_left _ h₂)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template
end

/-! # Presenting the attached diagram on two station lanes -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.FreezeInput
open Coloring
open scoped Classical
variable {F : Type} [Field F] (D : Template F) (u : ℕ) (scale : ℝ) (r : D.format.obj)
local notation "S" => D.scheme
local notation "A" => D.border u scale
local notation "U" => Attachment.scheme (D.border u scale)
local notation "out" => Attachment.rows (D.border u scale) (D.enclose u scale r)
variable (h : D.scheme.k = 0) {x y : Wire} {G : Diagram F x y}
    (p : D.scheme.Presentation r.1 G)

local notation "toLane" => dest D u scale r
local notation "toSpan" => newSpan D u scale r

def position : (S).Vtx ↪ (U).Vtx :=
  ⟨toLane, (show Function.LeftInverse (src D u scale) toLane from src_dest D u scale r h).injective⟩

def seat : (U).Seating out G where
  vertex := p.vertex.trans (position D u scale r h)
  pin i := (p.pin i).trans (pin D u scale r h (p.vertex i))
  sample v t := (table_at D u scale r h _ t).trans (p.sample _ _)
  cover := by
    rintro ⟨⟨v, j⟩, k⟩
    have hw := k.pos
    rw [width] at hw
    split at hw
    · rename_i hv
      obtain ⟨a, ha⟩ := p.cover ⟨(src D u scale v, j), ⟨0, hw⟩⟩
      exact ⟨a, (congrArg toLane ha).trans (dest_src D u scale r v hv)⟩
    · exact (lt_irrefl _ hw).elim
  vacant v hv t := by
    by_cases e : v.2.2 = Pattern.lane (D.mobile r v.1)
    · obtain ⟨w, rfl⟩ : v ∈ Set.range toLane := ⟨_, dest_src _ _ _ _ v e⟩
      apply (table_at D u scale r h w t).trans
      exact p.vacant w (fun ⟨i, he⟩ => hv ⟨i, congrArg toLane he⟩) _
    · exact untouched D u scale r v e t

local notation "q" => seat D u scale r h p

def put (j : (S).Pin r.1) : (U).Pin out := ⟨toSpan j.1, j.2.cast (width_at D u scale r h j.1).symm⟩

theorem ends (i : G.End) : (q).ends i = put D u scale r h (p.toSeating.ends i) := by
  obtain ⟨⟨v, j⟩, rfl⟩ := G.portEquiv.surjective i
  rw [Scheme.Seating.ends_at, Scheme.Seating.ends_at]
  rfl

include h p in
theorem proper : (U).Proper out := by
  rintro ⟨v, i⟩ t ht
  rw [peer] at ht
  split at ht
  swap
  · contradiction
  rename_i he
  obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp ht
  have hv : (v, i) = toSpan (src D u scale v, i) := Prod.ext (dest_src D u scale r v he).symm rfl
  obtain ⟨hb, hw, hd⟩ := p.proper _ _ hk
  rw [hv, peer_at _ _ _ _ h, hb, Option.map_some, width_at _ _ _ _ h, width_at _ _ _ _ h,
    direction_at _ _ _ _ h, direction_at _ _ _ _ h]
  exact ⟨rfl, hw, hd⟩

def present : (U).Presentation out G where
  toSeating := q
  proper := proper D u scale r h p
  internal i := by
    rw [ends, ends]
    refine ⟨?_, (p.internal i).2⟩
    rw [put, peer_at _ _ _ _ h, (p.internal i).1]
    rfl
  input i := by rw [ends, put, peer_at _ _ _ _ h, p.input]; rfl
  output i := by rw [ends, put, peer_at _ _ _ _ h, p.output]; rfl

theorem directed (hd : p.Directed) : (present D u scale r h p).Directed := by
  intro i
  change (U).direction out ((q).ends i).1 = _
  rw [ends, put, direction_at _ _ _ _ h, hd]

theorem boundary (i : slots x ⊕ slots y) :
    ((present D u scale r h p).boundary i).val = put D u scale r h (p.boundary i).val := by
  cases i
  · exact ends D u scale r h p _
  · exact ends D u scale r h p _

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.FreezeInput
end

/-!
# The two presentations of a concentrated term

The mobile part retains the order of each unit packet. The full
presentation restores the frozen tables and their tethers.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Shows
open Coloring Packing Rounds
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {u : ℕ}
    {D : Template F} {r : D.format.obj} {Q : LocalTerm F x y D.scheme.h u}
    (s : D.Shows r Q) (h : D.scheme.k = 0) (hu : 0 < u) (L : Fringe Q.freeze.x Q.freeze.y Q.freeze.Fixed)
    (hL : L.tensor = Q.freeze.border.tensor) (hc : L.charge = fun i => Q.charge i.val)
local notation "G" => Q.frame.hostOf hu L hL s.packets
local notation "A" => D.border u L.scale
local notation "rows" => D.enclose u L.scale r
local notation "old" => Scheme.Presentation.original Q.freeze

abbrev attached := FreezeInput.present D u L.scale r h (s.pres.joined Q.freeze)

theorem vertex_at (v : Q.freeze.Core ⊕ Q.freeze.Fixed) :
    (s.attached h L).vertex v = FreezeInput.dest D u L.scale r (s.pres.vertex (old v)) := rfl

theorem mobile_lane (v : Q.freeze.Core) : Pattern.lane (D.mobile r (s.pres.vertex v.val).1) = 0 :=
  ite_eq_left ((s.kept _).mpr v.property)

theorem frozen_lane (v : Q.freeze.Fixed) : Pattern.lane (D.mobile r (s.pres.vertex v.val).1) = 1 :=
  ite_eq_right (fun h => (s.kept _).mp h v.property)

private theorem active (v : (A).scheme.Vtx) :
    (A).live ((rows).2 v.1 v.2.1) v.2.2 = true ↔
      0 < D.load (D.counter r v.1 v.2.1) ∧ v.2.2 = Pattern.lane (D.mobile r v.1) := by
  simp only [border, enclose, remove, Scheme.remove, Equiv.symm_apply_apply, decide_eq_true_eq]

include hu in
private theorem occupied_lane (v : (A).scheme.Vtx) :
    (A).live ((rows).2 v.1 v.2.1) v.2.2 = true ↔ v ∈ Set.range (s.attached h L).vertex := by
  rw [active, s.occupied hu]
  constructor
  · rintro ⟨⟨j, hj⟩, he⟩
    obtain ⟨i, rfl⟩ := (old).surjective j
    refine ⟨i, ?_⟩
    rw [s.vertex_at, hj]
    exact Prod.ext rfl (Prod.ext rfl he.symm)
  · rintro ⟨i, rfl⟩
    rw [s.vertex_at]
    refine ⟨⟨old i, ?_⟩, rfl⟩
    rw [s.vertex]
    rfl

def encloses : (A).Encloses rows G Q.freeze.border where
  full := rfl
  tether := hL
  core := s.encode hu L hL hc
  pres := s.attached h L
  directed := FreezeInput.directed D u L.scale r h (s.pres.joined Q.freeze)
    (s.pres.joined_directed Q.freeze s.directed)
  occupied := s.occupied_lane h hu L
  slot _ := 1
  positive _ := by exact (by decide : (1 : B 1) ≠ 0)
  internal v := by
    change FreezeInput.dest D u L.scale r (s.pres.vertex v.val) = _
    unfold FreezeInput.dest
    rw [s.mobile_lane v, s.vertex]
    rfl
  frozen v := by
    change FreezeInput.dest D u L.scale r (s.pres.vertex v.val) = _
    unfold FreezeInput.dest
    rw [s.frozen_lane v, s.vertex]
    rfl
  charge v := by
    have hm := s.weight_at v.val
    simp only [border, enclose, Equiv.symm_apply_apply]
    exact hm.trans (congrFun hc v).symm
  ordered v j := ⟨rfl, rfl⟩

theorem attached_boundary (i : slots x ⊕ slots y) :
    ((s.attached h L).boundary i).val =
      FreezeInput.put D u L.scale r h (s.pres.boundary i).val := by
  rw [attached, FreezeInput.boundary, s.pres.joined_boundary]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Shows
end

/-! # The retained exterior payload needs no further permutation -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Shows
open Coloring Packing Rounds

variable {F : Type} [Field F] {x y : Wire} {u : ℕ}
    {D : Template F} {r : D.format.obj} {Q : LocalTerm F x y D.scheme.h u}
    (s : D.Shows r Q) (h : D.scheme.k = 0) (L : Fringe Q.freeze.x Q.freeze.y Q.freeze.Fixed)

theorem outer_lane (i : slots x ⊕ slots y) : ((s.attached h L).boundary i).val.1.1.2.2 = (1 : B 1) := by
  have he : (s.pres.boundary i).val.1.1 = s.pres.vertex (portEnd Q.diagram i) := by
    cases i <;> exact s.pres.end_station _
  rw [s.attached_boundary]
  change Pattern.lane (D.mobile r (s.pres.boundary i).val.1.1.1) = _
  rw [he]
  exact s.frozen_lane ⟨_, Q.freeze.exterior i⟩

theorem retag : s.pres.Retag (s.attached h L) where
  m := rfl
  owner i := by unfold Scheme.owner; rw [attached_boundary]; rfl
  block i := by rw [attached_boundary]; rfl
  span i := by rw [attached_boundary]; rfl
  offset i := by rw [attached_boundary]; rfl
  left i j := (FreezeInput.slot D h _).trans (FreezeInput.slot D h _).symm
  right i j := (s.outer_lane h L i).trans (s.outer_lane h L j).symm

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Shows
end
