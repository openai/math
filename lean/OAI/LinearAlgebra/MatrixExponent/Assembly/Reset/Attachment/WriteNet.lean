import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Move
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Length
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Ports.Correspondence
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Checks
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Child.Follow
import OAI.LinearAlgebra.MatrixExponent.Assembly.Volumes
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Child.Headers
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.BoardPush
import OAI.LinearAlgebra.MatrixExponent.Processor.Labels
import OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Apply
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Child.Described
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Ports.Eval

/-! # Passing the budget for old labels through a reset -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset

open Coloring Packing Finset
open scoped Classical

variable {T F : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {h u a : ℕ}
  {G : HostNet F L h u} {S : Scheme F} {r : S.format.obj} (p : S.Posting r G)
  {B' W : ℝ} {Hcap D : ℕ}
  (q : ResetResult F a G.N G.src G.dst G.ix G.load u B' W Hcap D)
  (v : Cell a × q.vertex)

local notation "Q" => G.afterReset q

theorem footprint_reset :
    push q.owner (fun t => (G.footprint t : ℝ)) v ≤ (Q).footprint v.swap := by
  let f := Prod.swap ∘ q.owner
  have he : push q.owner (fun t => (G.footprint t : ℝ)) v =
      push f (fun t => (G.footprint t : ℝ)) v.swap := by
    apply sum_congr rfl
    intro i _
    simp [f]
  have ext : push f (fun t => (G.tetherLoad t : ℝ)) v.swap = (Q).tetherLoad v.swap := by
    unfold HostNet.tetherLoad
    erw [← exterior_comp, port_load]
  have past : push f (fun t => (G.past t + degree G.pair t * u : ℕ)) v.swap =
      (Q).past v.swap := by
    change _ = (G.carried f v.swap : ℝ)
    simp only [HostNet.carried, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, push]
  have add : push f (fun t => (G.footprint t : ℝ)) v.swap =
      push f (fun t => (G.past t + degree G.pair t * u : ℕ)) v.swap +
        push f (fun t => (G.tetherLoad t : ℝ)) v.swap := by
    unfold push
    rw [← sum_add_distrib]
    refine sum_congr rfl fun t _ => ?_
    split_ifs
    · simp only [HostNet.footprint, Nat.cast_add]; exact add_right_comm _ _ _
    · exact (add_zero _).symm
  rw [he, add, ext, past]
  simp only [HostNet.footprint, Nat.cast_add]
  exact le_add_of_nonneg_right (Nat.cast_nonneg (α := ℝ) _)

def Charged (o : B S.ℓ ≃ B S.ℓ) (unit cost : ℕ) :=
  ∀ t : G.V × Cell h, 0 < G.tetherLoad t + degree G.pair t * u →
    Dense.used (o ((r (p.host t.1)).2 (p.block t.2))).val * unit ≤ cost * G.footprint t

variable {o : B S.ℓ ≃ B S.ℓ} {unit cost : ℕ}

theorem inherited_charge (tag : Charged p o unit cost) (hu : 0 < unit) :
    inherited p q v o * unit ≤ cost * (Q).footprint v.swap := by
  let c : ℝ := (cost : ℝ) / unit
  have hc : 0 ≤ c := by unfold c; positivity
  have hu' : (0 : ℝ) < unit := Nat.cast_pos.mpr hu
  let mass (t : G.V × Cell h) := c * (G.footprint t : ℝ)
  have hh := inherited_le p q v o mass (fun t => mul_nonneg hc (Nat.cast_nonneg _)) (by
    intro w hw
    let t := G.units.place w
    have ht := tag t (G.arity_active w hw)
    rw [oldLabel, p.vertex_eq]
    change (Dense.used (o ((r (p.host t.1)).2 (p.block t.2))).val : ℝ) ≤
      (cost : ℝ) / unit * G.footprint t
    rw [div_mul_eq_mul_div, le_div_iff₀ hu']
    exact_mod_cast ht)
  have hm : push q.owner mass v ≤ c * (Q).footprint v.swap := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (footprint_reset q v) hc)
    have ee := push_div q.owner (fun t => (G.footprint t : ℝ)) c⁻¹ v
    simp only [div_inv_eq_mul, mul_comm _ c] at ee
    exact ee.le
  have hh := hh.trans hm
  rw [show c = (cost : ℝ) / unit from rfl, div_mul_eq_mul_div, le_div_iff₀ hu'] at hh
  exact_mod_cast hh

theorem inherited_bound (tag : Charged p o unit cost) (hu : 0 < unit) (b : ℕ)
    (hm : (Q).mass ≤ L.cap) (hl : 89 * B' ≤ (b : ℝ) * unit) :
    inherited p q v o ≤ cost * (2 ^ L.discount * b) := by
  have hp : (Q).footprint v.swap ≤ 2 ^ L.discount * b * unit := by
    have hload := (G.reset_load q v.2 v.1).trans hl
    have he := ((Q).footprint_le hm v.swap).trans (mul_le_mul_of_nonneg_left hload (by positivity))
    rw [← mul_assoc] at he
    exact_mod_cast he
  apply Nat.le_of_mul_le_mul_right _ hu
  rw [mul_assoc]
  exact (inherited_charge p q v tag hu).trans (Nat.mul_le_mul_left _ hp)

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
end

/-! # Charging an emitted reset label to the next occurrence -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Book.Ready
open Packing Coloring
open scoped Classical

variable {T F : Type} [Field F] [Fintype F] [Fintype T] {x y : Wire} {L : Fringe x y T} {h u a : ℕ}
  {G : HostNet F L h u} {S : Scheme F} {r : S.format.obj} {p : S.Posting r G}
  {B' W' : ℝ} {Hcap D : ℕ}
  {q : ResetResult F a G.N G.src G.dst G.ix G.load u B' W' Hcap D}
  {m d h' e cap : ℕ} {b : Book S u e cap}
  {A : Allocation p q (b.scheme m d h')} {nav : B m → B d → B m} (H : b.Ready A nav)
  {unit cost : ℕ}

theorem charged (tag : Charged p b.ord unit cost) (hu : 0 < unit) (hle : unit ≤ u)
    (hw : ∀ j, u ≤ p.toPresentation.borderWidth j) :
    Charged H.posting (Post.order d e b.d cap) unit (cost + (Post.headerFmt d e b.d).width + overhead S e) := by
  intro w active
  let Q := G.afterReset q
  let W := (Post.headerFmt d e b.d).width + overhead S e
  have hf := Q.active_floor (H.posting.toPresentation.contacts (H.floor hw)) w active
  have hl := H.stored w.swap
  have hi := inherited_charge p q w.swap tag hu
  have hh : W * unit ≤ W * Q.footprint w := Nat.mul_le_mul_left W (hle.trans hf)
  calc
    _ ≤ (W + inherited p q w.swap b.ord) * unit := Nat.mul_le_mul_right _ hl
    _ ≤ W * Q.footprint w + cost * Q.footprint w := by rw [Nat.add_mul]; exact Nat.add_le_add hh hi
    _ = _ := by rw [← Nat.add_mul, Nat.add_comm W, Nat.add_assoc]

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Book.Ready
end

/-! # Sufficient load and label budgets for a host reset -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset

open Packing Coloring
open scoped Classical
variable {T F : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {h u a : ℕ}
  {G : HostNet F L h u} {S : Scheme F} {r : S.format.obj} (p : S.Posting r G)
  {B' W : ℝ} {Hcap D : ℕ}
  (q : ResetResult F a G.N G.src G.dst G.ix G.load u B' W Hcap D)
  {unit cost b : ℕ}

theorem seats_fit (v : Cell a × q.vertex) (hu : 0 < unit) (hle : unit ≤ u)
    (hw : ∀ j, u ≤ p.toPresentation.borderWidth j) (hb : 89 * B' ≤ (b : ℝ) * unit) :
    Fintype.card (Hidden q v) ≤ b ∧ Fintype.card (Live q v) ≤ b ∧ Fintype.card (Visible p q v) ≤ b := by
  have fit (n : ℕ) (hn : (n : ℝ) * u ≤ 89 * B') : n ≤ b := by
    apply Nat.le_of_mul_le_mul_right _ hu
    have hh : (n : ℝ) * unit ≤ (b : ℝ) * unit :=
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hle) (Nat.cast_nonneg _)).trans (hn.trans hb)
    exact_mod_cast hh
  exact ⟨fit _ (hidden_bound q v), fit _ (live_bound p q v hw), fit _ (visible_bound p q v hw)⟩

variable {p q} [Fintype F] {m d h' e cap : ℕ} (t : Book S u e cap)
    (A : Allocation p q (t.scheme m d h')) (nav : B m → B d → B m)

local notation "Host" => Allocation.endHost (q := q)

theorem Book.ready
    (sizes : ∀ j, t.len (t.put (p.toPresentation.borderWidth j)) = p.toPresentation.borderWidth j)
    (hop : ∀ (i : q.Survivors) z,
      nav (A.host (Host i z)) (A.index (Host i z) (Host i (!z))) = A.host (Host i (!z)))
    (hs : q.rule.Simple)
    (hn : ∀ w, G.diagram.arity w = 0 → ∀ z, Transcript.sample (G.diagram.table w) z = 1)
    (tag : Charged p t.ord unit cost) (hu : 0 < unit) (hle : unit ≤ u)
    (hw : ∀ j, u ≤ p.toPresentation.borderWidth j) (hm : (G.afterReset q).mass ≤ L.cap)
    (hb : 89 * B' ≤ (b : ℝ) * unit) (he : b ≤ 2 ^ e)
    (hc : overhead S e + cost * (2 ^ L.discount * b) ≤ cap) : t.Ready A nav where
  sizes := sizes
  hop := hop
  describe v := by
    obtain ⟨hi, hl, _⟩ := seats_fit p q v hu hle hw hb
    exact describe p q v (A.seat v) t.ord hs hn (hi.trans he) (hl.trans he)
  budget v := (Nat.add_le_add_left (inherited_bound p q v tag hu b hm hb) _).trans hc

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
end

/-! # Comparing the long addresses once at every host -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Tile
open Coloring Neighborhood
variable {F : Type} [Field F] (A : Template F) (n : ℕ)
local notation "m" => A.scheme.m
local notation "d" => A.scheme.d

def maskCost := A.format.width + 2 ^ m * (100 + (m + 2 ^ ((d + 1) * n))) ^ 50

theorem mask_net (hn : 0 < n) : Circuit F A.format (.vec m (coincides d n)) (mask A n) (maskCost A n) := by
  have nav : Circuit F A.format (Neighborhood.Rows m d) A.nav (A.format.width + 2 * (Neighborhood.Rows m d).width) :=
    Circuit.project (A := A.format) (D := Neighborhood.Rows m d) (fun z => .inl (z.1, .inl z.2)) (fun _ _ => rfl)
  let t := m + 2 ^ ((d + 1) * n)
  obtain ⟨s, net, hs⟩ := (cheap_walks F m d n hn).comp (cheap_equal F (Nat.le_add_right ..) (Nat.le_add_left ..))
  refine (nav.comp net).mono ?_
  have hq := Nat.two_pow_pos ((d + 1) * n)
  have hc : 2 * (2 ^ m * (100 + t) ^ 26) ≤ 2 ^ m * (100 + t) ^ 50 := calc
    _ = 2 ^ m * (2 * (100 + t) ^ 26) := mul_left_comm ..
    _ ≤ 2 ^ m * (100 + t) ^ 27 := by rw [pow_succ' (100 + t) 26]; gcongr; omega
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by decide))
  change (Neighborhood.Rows m d).width + _ + s ≤ 2 ^ m * (100 + t) ^ 26 at hs
  change _ ≤ A.format.width + 2 ^ m * (100 + t) ^ 50
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Tile
end

/-! # Sending a short window to every child and group -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Tile
open Coloring
variable {F : Type} (A D : Template F) (k n t : ℕ)
    (ha : D.scheme.h ≤ A.scheme.h) (hm : D.scheme.m = A.scheme.m + t)

local notation "a" => D.scheme.h
local notation "m" => A.scheme.m
local notation "d" => A.scheme.d
local notation "W" => Window.Walks n A.scheme.d (row A D.scheme.h k)
local notation "src" => pair A k

abbrev gathered := (src).pair ((Format.vec m (coincides d n)).pair (Fmt.groups m d a W))
abbrev queries := Format.vec D.scheme.m (.vec a (sample A a k n t))
def volume := 2 ^ a * (W).width

def collect (r : (src).obj) : (gathered A D k n).obj :=
  (r, mask A n r.1, Window.reads n (packet A a k ha r))

def distribute (r : (gathered A D k n).obj) : (queries A D k n t).obj :=
  fun v i =>
    let p := Match.rowIndex m t (Fin.cast (congrArg (2^·) hm) v)
    ((A.live r.1.1 p.1, p.2), (r.1.2.1, i), r.2.1 p.1, (r.2.2 p.1).2 i)

def lookupKey (r : (src).obj) : (queries A D k n t).obj :=
  fun v i => look A a k ha n t r (Fin.cast (congrArg (2^·) hm) v) i

def windowCost (N : ℕ) :=
  100 * ((src).width + packetCost A a k + maskCost A n + (gathered A D k n).width) +
    136 * (queries A D k n t).width + (n + 1) * Window.readCost m d (volume A D k n) N

variable [Field F]

private theorem distribute_net :
    Circuit F (gathered A D k n) (queries A D k n t) (distribute A D k n t hm)
      ((gathered A D k n).width + 34 * (queries A D k n t).width) := by
  apply Window.Tile.project_const
  rintro ⟨v, i, j⟩
  let p := Match.rowIndex m t (Fin.cast (congrArg (2^·) hm) v)
  rcases j with (j|j)|(j|j)|j|j
  · exact .inl ⟨.inl (.inl (.inr (p.1, .inl (.inl j)))), fun _ => rfl⟩
  · exact .inr ⟨(Format.addr t).code p.2 j, fun _ => rfl⟩
  · exact .inl ⟨.inl (.inr (.inl j)), fun _ => rfl⟩
  · exact .inr ⟨(Format.addr a).code i j, fun _ => rfl⟩
  · exact .inl ⟨.inr (.inl (p.1, j)), fun _ => rfl⟩
  · exact .inl ⟨.inr (.inr (p.1, .inr (i, j))), fun _ => rfl⟩

theorem window_net {I : Type*} {u N : ℕ} {L : Set (Table F)} (hu : 3 ≤ u)
    (hn : 0 < n) (access : Access F u L (m + d) (volume A D k n) N)
    (x : I → (src).obj)
    (hr : ∀ i, Fmt.Reciprocal (.vec A.scheme.h (.addr A.scheme.ℓ)) (x i).1.1) :
    Computes F u L src (queries A D k n t) x (lookupKey A D k n t ha hm ∘ x)
      (fun _ => 1) (windowCost A D k n t N) := by
  have send := Computes.of_map (L := L) (x := x) (Map.circuit hu (packet_net A a k ha)) (fun _ => rfl)
  have read := Window.reads_net (r := n) hu access (fun i => packet A a k ha (x i)) hr le_rfl
  have first : Circuit F src A.format Prod.fst ((src).width + 2 * A.format.width) :=
    Circuit.project Sum.inl (fun _ _ => rfl)
  have eqs := Computes.of_map (L := L) (x := x) (Map.circuit hu (first.comp (mask_net A n hn))) (fun _ => rfl)
  have copy := Computes.of_map (L := L) (x := x) (Map.circuit hu (Circuit.id F src)) (fun _ => rfl)
  have all := Computes.pair hu copy (Computes.pair hu eqs (send.comp read))
  have output := Computes.of_map (x := collect A D k n ha ∘ x) (L := L)
    (Map.circuit hu (distribute_net A D k n t hm)) (fun _ => rfl)
  have net := all.comp output
  simp only [one_mul] at net
  refine net.mono ?_
  have hv : A.format.width ≤ (src).width := by rw [Format.width_pair A.format]; omega
  unfold windowCost
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Tile
end

/-!
# Selecting a relative header from a short observation

Only one group is needed for each child. The frozen flag is
available separately at the parent. Global addresses never
enter the dictionary gate.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Tile
open Coloring
open scoped Classical

variable {F : Type} (A D : Template F) (k n t : ℕ)
    (ha : D.scheme.h ≤ A.scheme.h) (hm : D.scheme.m = A.scheme.m + t)
local notation "m" => A.scheme.m
local notation "d" => A.scheme.d
local notation "l" => D.scheme.d
local notation "src" => pair A k
local notation "Q" => queries A D k n t

abbrev vertexFormat := Format.pair .bit (sample A D.scheme.h k n t)

def vertexKey (x : (src).obj) (v : B (m + t)) : (vertexFormat A D k n t).obj :=
  (A.frozen x.1 (Match.rowIndex m t v).1, look A D.scheme.h k ha n t x v 0)

abbrev headers := Format.vec (m + t) (Child.Suffix d t l)

def HeaderLocal {I : Type*} (x : I → (src).obj) (z : I → (headers A D t).obj) : Prop :=
  ∀ q q' v v', vertexKey A D k n t ha (x q) v = vertexKey A D k n t ha (x q') v' → z q v = z q' v'

abbrev request := Format.pair (Neighborhood.Rows m d) (.vec (m + t) (vertexFormat A D k n t))

private def take (r : (Format.pair src Q).obj) : (request A D k n t).obj :=
  (A.nav r.1.1, fun v =>
    (A.frozen r.1.1 (Match.rowIndex m t v).1, r.2 (Fin.cast (congrArg (2^·) hm.symm) v) 0))

def headerWidth := (vertexFormat A D k n t).width + (Child.Suffix d t l).width

def headerCost (N : ℕ) := 100 * ((src).width + (Q).width + (request A D k n t).width) +
  windowCost A D k n t N + 2 ^ (m + t) * (1 + headerWidth A D k n t)

variable [Field F]

private theorem take_net :
    Circuit F (.pair src Q) (request A D k n t) (take A D k n t hm)
      ((Format.pair src Q).width + 2 * (request A D k n t).width) := by
  let idx : (request A D k n t).pins → (Format.pair src Q).pins
    | .inl (v, j) => .inl (.inl (.inl (v, .inl j)))
    | .inr (v, .inl j) => .inl (.inl (.inr ((Match.rowIndex m t v).1, .inl (.inr j))))
    | .inr (v, .inr j) => .inr (Fin.cast (congrArg (2^·) hm.symm) v, 0, j)
  exact Circuit.project idx (by rintro x (⟨v, j⟩|⟨v, j|j⟩) <;> rfl)

include hm in
theorem header_net {I : Type*} (x : I → (pair A k).obj) (z : I → (headers A D t).obj)
    (h : HeaderLocal A D k n t ha x z)
    (hr : ∀ i, Fmt.Reciprocal (.vec A.scheme.h (.addr A.scheme.ℓ)) (x i).1.1) (hn : 0 < n) :
    ∃ gate : Table F, Processor.arity gate = headerWidth A D k n t ∧
      ∀ {u N : ℕ} {L : Set (Table F)}, 3 ≤ u → headerWidth A D k n t ≤ u → gate ∈ L →
      Access F u L (m + d) (volume A D k n) N →
      Computes F u L src (Child.Input m d t l) x (fun i => (A.nav (x i).1, z i))
        (fun _ => 1) (headerCost A D k n t N) := by
  let U := vertexFormat A D k n t
  let V := Child.Suffix d t l
  let gateKey (p : I × B (m + t)) := vertexKey A D k n t ha (x p.1) p.2
  let val (p : I × B (m + t)) := z p.1 p.2
  have hf : Function.FactorsThrough val gateKey := fun _ _ => h _ _ _ _
  let default' : U.obj → V.obj := fun _ => V.code.symm (fun _ => false)
  let f := Function.extend gateKey val default'
  refine ⟨lookup F U V (fun x y => @ite F (f x = y) (Classical.propDecidable _) 1 0), ?_, ?_⟩
  · simp only [Processor.arity, lookup, wd_word, headerWidth, U, V]
  intro u N L hu hw hg access
  have one : Map F u L U V f (1 + headerWidth A D k n t) := by
    rw [headerWidth, ← add_assoc]
    exact Kernel.lookup hw hg
  have first := window_net A D k n t ha hm hu hn access x hr
  have cp := Computes.of_map (x := x) (L := L) (Map.circuit hu (Circuit.id F src)) (fun _ => rfl)
  let y (i : I) : (request A D k n t).obj := (A.nav (x i).1, vertexKey A D k n t ha (x i))
  have prep := (Computes.pair hu cp first).comp (Computes.of_map (y := y)
    (Map.circuit hu (take_net A D k n t hm)) (fun _ => rfl))
  have gate := (Map.circuit hu (Circuit.id F (Neighborhood.Rows m d))).par
    (Map.vec _ (fun _ : B (m + t) => one))
  have fields (i : I) : Prod.map id (fun x v => f (x v)) (y i) = (A.nav (x i).1, z i) :=
    Prod.ext rfl (funext fun v => hf.extend_apply default' (i, v))
  have end' := Computes.of_map (x := y) gate fields
  have net := prep.comp end'
  simp only [one_mul] at net
  refine net.mono ?_
  have hv : (Neighborhood.Rows m d).width ≤ (request A D k n t).width := by
    rw [Format.width_pair]; exact Nat.le_add_right ..
  rw [Format.width_pair src Q, headerCost]
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Tile
end

/-! # One dictionary gate shared by all reset decisions -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Tile
open Coloring
open scoped Classical
variable {F : Type} (A D : Template F) (k n t : ℕ)
    (ha : D.scheme.h ≤ A.scheme.h) (hm : D.scheme.m = A.scheme.m + t)
local notation "a" => D.scheme.h
local notation "m" => D.scheme.m
local notation "U" => sample A D.scheme.h k n t
local notation "V" => output A D
local notation "src" => pair A k
variable {I : Type*} (x : I → (pair A k).obj) (y : I → (whole A D).obj)

def Local : Prop :=
  ∀ q q' v v' i i',
    lookupKey A D k n t ha hm (x q) v i = lookupKey A D k n t ha hm (x q') v' i' →
    part A D (y q) v i = part A D (y q') v' i'

def printWidth := (U).width + (V).width
def printCost (N H : ℕ) := 20 * (src).width + H + windowCost A D k n t N +
  2 ^ m * (2 ^ a * (1 + printWidth A D k n t)) + 4 * assembleCost A D

private theorem depends (h : Local A D k n t ha hm x y) :
    ∃ f : (U).obj → (V).obj, ∀ q v i, f (lookupKey A D k n t ha hm (x q) v i) = part A D (y q) v i := by
  have hx (z : (U).obj) : ∃ o : (V).obj,
      ∀ q v i, lookupKey A D k n t ha hm (x q) v i = z → o = part A D (y q) v i := by
    by_cases hs : ∃ q v i, lookupKey A D k n t ha hm (x q) v i = z
    · obtain ⟨q, v, i, hq⟩ := hs
      exact ⟨part A D (y q) v i, fun q' v' i' ht => h _ _ _ _ _ _ (hq.trans ht.symm)⟩
    · exact ⟨(V).code.symm (fun _ => false), fun q v i he => (hs ⟨q, v, i, he⟩).elim⟩
  choose f hf using hx
  exact ⟨f, fun q v i => hf _ _ _ _ rfl⟩

theorem print_net [Field F] (h : Local A D k n t ha hm x y)
    (hr : ∀ i, Fmt.Reciprocal (.vec A.scheme.h (.addr A.scheme.ℓ)) (x i).1.1) (hn : 0 < n) :
    ∃ gate : Table F, Processor.arity gate = printWidth A D k n t ∧
      ∀ {u N H : ℕ} {L : Set (Table F)}, 3 ≤ u → printWidth A D k n t ≤ u → gate ∈ L →
      Access F u L (A.scheme.m + A.scheme.d) (volume A D k n) N →
      Computes F u L src (graph D) x (fun i => header D (y i).1) (fun _ => 1) H →
      Computes F u L src (whole A D) x y (fun _ => 1) (printCost A D k n t N H) := by
  obtain ⟨f, hf⟩ := depends A D k n t ha hm x y h
  refine ⟨lookup F U V (fun x y => @ite F (f x = y) (Classical.propDecidable _) 1 0), ?_, ?_⟩
  · simp only [Processor.arity, lookup, wd_word, printWidth]
  intro u N H L hu hw hg access heads
  have one : Map F u L U V f (1 + printWidth A D k n t) :=
    by rw [printWidth, ← add_assoc]; exact Kernel.lookup hw hg
  have rows := Map.vec _ (fun _ : B m => Map.vec _ (fun _ : B a => one))
  have fields : Computes F u L (queries A D k n t) (body A D) (lookupKey A D k n t ha hm ∘ x)
      (fun i => part A D (y i)) (fun _ => 1) (2 ^ m * (2 ^ a * (1 + printWidth A D k n t))) := by
    refine Computes.of_map rows ?_
    intro q; funext v i; exact hf q v i
  have area := window_net A D k n t ha hm hu hn access x hr
  have all := Computes.pair hu heads (area.comp fields)
  have net := all.comp (Computes.of_map (y := y) (Map.circuit hu (assemble_net A D))
    (fun i => assemble_part A D (y i)))
  simp only [one_mul] at net
  exact net.mono (by unfold printCost; omega)

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Tile
end

/-! # Issuing attachment requests from the reset windows -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Tile

open Coloring
open scoped Classical
variable {F : Type} (A D : Template F) (T : Attachment A) (k n t slots : ℕ)
    (ha : D.scheme.h ≤ A.scheme.h) (hm : D.scheme.m = A.scheme.m + t)
local notation "U" => sample A D.scheme.h k n t
local notation "V" => Format.pair Format.bit (T.orders D slots 0)
local notation "src" => pair A k
variable {I : Type*} (x : I → (pair A k).obj) (qs : I → Attachment.Query T D slots 0)

def QueryLocal : Prop :=
  ∀ q q' v v' i i',
    lookupKey A D k n t ha hm (x q) v i = lookupKey A D k n t ha hm (x q') v' i' →
    ((qs q).ticketAt v i).2 = ((qs q').ticketAt v' i').2

def queryWidth := (U).width + (V).width
def queryCost (N H : ℕ) :=
  4 * T.format.width + 20 * (src).width + H + windowCost A D k n t N +
    2 ^ D.scheme.m * (2 ^ D.scheme.h * (1 + queryWidth A D T k n t slots))

private theorem ticket (h : QueryLocal A D T k n t slots ha hm x qs) :
    ∃ f : (U).obj → (V).obj,
      ∀ q v i, f (lookupKey A D k n t ha hm (x q) v i) = ((qs q).ticketAt v i).2 := by
  have hx (z : (U).obj) : ∃ o : (V).obj,
      ∀ q v i, lookupKey A D k n t ha hm (x q) v i = z → o = ((qs q).ticketAt v i).2 := by
    by_cases hs : ∃ q v i, lookupKey A D k n t ha hm (x q) v i = z
    · obtain ⟨q, v, i, hq⟩ := hs
      exact ⟨_, fun q' v' i' ht => h q q' v v' i i' (hq.trans ht.symm)⟩
    · exact ⟨(V).code.symm (fun _ => false), fun q v i he => (hs ⟨q, v, i, he⟩).elim⟩
  choose f hf using hx
  exact ⟨f, fun q v i => hf _ _ _ _ rfl⟩

/-- The separate dictionary gate emits all local controls. Its input
window and the fresh core use the same reset data. -/
theorem query_net [Field F] (h : QueryLocal A D T k n t slots ha hm x qs)
    (hr : ∀ i, Fmt.Reciprocal (.vec A.scheme.h (.addr A.scheme.ℓ)) (x i).1.1) (hn : 0 < n) :
    ∃ gate : Table F, Processor.arity gate = queryWidth A D T k n t slots ∧
      ∀ {u N H : ℕ} {L : Set (Table F)}, 3 ≤ u → queryWidth A D T k n t slots ≤ u → gate ∈ L →
      Access F u L (A.scheme.m + A.scheme.d) (volume A D k n) N →
      Computes F u L src D.format x (fun i => (qs i).fresh) (fun _ => 1) H →
      Computes F u L (T.format.pair src) (T.Requests D slots 0)
        (fun i => ((qs i).old, x i)) (fun i => (qs i).requests) (fun _ => 1)
        (queryCost A D T k n t slots N H) := by
  obtain ⟨f, hf⟩ := ticket A D T k n t slots ha hm x qs h
  refine ⟨lookup F U V (fun x y => @ite F (f x = y) (Classical.propDecidable _) 1 0), ?_, ?_⟩
  · simp only [Processor.arity, lookup, wd_word, queryWidth]
  intro u N H L hu hw hg access fresh
  have one : Map F u L U V f (1 + queryWidth A D T k n t slots) :=
    by rw [queryWidth, ← add_assoc]; exact Kernel.lookup hw hg
  have rows := Map.vec _ (fun _ : B D.scheme.m => Map.vec _ (fun _ : B D.scheme.h => one))
  have data : Computes F u L (queries A D k n t) (.vec D.scheme.m (.vec D.scheme.h V))
      (lookupKey A D k n t ha hm ∘ x) (fun i v j => ((qs i).ticketAt v j).2) (fun _ => 1)
      (2 ^ D.scheme.m * (2 ^ D.scheme.h * (1 + queryWidth A D T k n t slots))) := by
    refine Computes.of_map rows ?_
    intro i; funext v j; exact hf i v j
  have area := window_net A D k n t ha hm hu hn access x hr
  have keep := Computes.of_map (x := fun i => (qs i).old) (L := L) (Map.circuit hu (Circuit.id F T.format))
    (fun _ => rfl)
  have all := keep.par (Computes.pair hu fresh (area.comp data))
  simp only [one_mul] at all
  exact all.mono (by unfold queryCost; omega)

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Tile
end

/-! # One short lookup table computes all reset records -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Board
open Packing Coloring Setup
open scoped Classical
variable {F : Type} [Field F] [Fintype F] {A : Template F} {u a Δ D Y w k n : ℕ} {W cost : ℝ}
  [NeZero Y] [NeZero w] {U V : Setup A.scheme A.scheme.h u a Δ D Y w W}
  {b : Board A U k} {c : Board A V k}
  {R : Rotor F Y w} {fit : U.Fits R cost} {fit' : V.Fits R cost}
  {e cap t d : ℕ} {B' : Book A.scheme u e cap}
  {L : U.Layout R fit B' (A.scheme.m + t) d} {L' : V.Layout R fit' B' (A.scheme.m + t) d}
  {g g' : (Child.Graph (A.scheme.m + t) d).obj}
  {locate : Coord R A.scheme.h a Δ ↪ B t}
  (M : Template.Meter)
local notation "E" => A.resetTarget B' M (A.scheme.m + t) d a

theorem part_eq (hn : A.scheme.h - a + 8 ≤ n) (hD : 0 < D)
    (delayed : A.full = false → A.scheme.h - a ≤ 32 * Nat.clog 2 (2 * D))
    (hp : Placed A L locate) (hq : Placed A L' locate) (ha : Ranked L) (hb : Ranked L')
    (hi : ∀ v z σ, Sample b c v z σ n → IndexAgrees L L' (path v z) σ v z)
    (hu : ∀ t, U.G.diagram.arity t = 0 → ∀ x, Transcript.sample (U.G.diagram.table t) x = 1)
    (hv : ∀ t, V.G.diagram.arity t = 0 → ∀ x, Transcript.sample (V.G.diagram.table t) x = 1)
    (hs : B'.Ready L g.1) (ht : B'.Ready L' g'.1)
    {i j : B (A.scheme.m + t)} {x y : B a}
    (he : Tile.look A a k U.groups n t b.tape i x = Tile.look A a k V.groups n t c.tape j y) :
    Tile.part A E (emitted M L g (parent A t)) i x =
      Tile.part A E (emitted M L' g' (parent A t)) j y := by
  rcases matched hp hq he with ⟨hl, hr⟩|⟨σ, v, z, loc, rfl, rfl, rfl, rfl, h⟩
  · exact (emitted_vacant M L g (parent A t) hl x).trans (emitted_vacant M L' g' (parent A t) hr y).symm
  · exact h.cell hn hD delayed ha hb (hi v z σ h) hu hv loc M hs ht hp.block hq.block (parent A t)

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Board
end

/-! # Locality of the graph header from a single group's sample -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Board
open Packing Coloring Setup
open scoped Classical
variable {F : Type} [Field F] [Fintype F] {A : Template F} {u a Δ D Y w k n : ℕ} {W cost : ℝ}
  [NeZero Y] [NeZero w] {U V : Setup A.scheme A.scheme.h u a Δ D Y w W}
  {b : Board A U k} {c : Board A V k}
  {R : Rotor F Y w} {fit : U.Fits R cost} {fit' : V.Fits R cost}
  {e cap t d : ℕ} {B' : Book A.scheme u e cap}
  {L : U.Layout R fit B' (A.scheme.m + t) d} {L' : V.Layout R fit' B' (A.scheme.m + t) d}
  {locate : Coord R A.scheme.h a Δ ↪ B t}
  (M : Template.Meter)
local notation "E" => A.resetTarget B' M (A.scheme.m + t) d a

theorem vertex_eq (hp : Placed A L locate) (hq : Placed A L' locate)
    (f g : B (A.scheme.m + t) → (Child.Suffix A.scheme.d t d).obj)
    (idle : ∀ i j, i ∉ Set.range L.host → j ∉ Set.range L'.host →
      (Match.rowIndex _ t i).2 = (Match.rowIndex _ t j).2 → f i = g j)
    (active : ∀ v z σ loc, Preview b.read c.read (path v z) n → (U.G.frozen v ↔ V.G.frozen z) →
      f (L.host (U.station R fit σ v loc).2) = g (L'.host (V.station R fit' σ z loc).2))
    {i j : B (A.scheme.m + t)}
    (he : Tile.vertexKey A E k n t U.groups b.tape i = Tile.vertexKey A E k n t V.groups c.tape j) :
    f i = g j := by
  obtain ⟨hf, hl⟩ := Prod.mk.inj he
  change Tile.look A a k U.groups n t b.tape i 0 = Tile.look A a k V.groups n t c.tape j 0 at hl
  rcases matched hp hq hl with ⟨hs, ht⟩ | ⟨σ, v, z, loc, _, _, rfl, rfl, h⟩
  · exact idle _ _ hs ht (congrArg (fun x => x.1.2) hl)
  apply active v z σ loc h.look.preview
  rw [← b.frozen, ← c.frozen]
  simp only [hp.host, hq.host, Equiv.apply_symm_apply] at hf
  rw [hf]

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Board
end

/-! # Choosing a layout and common header for each input branch -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
open Packing Coloring
open scoped Classical
variable {F : Type} [Field F] [Fintype F] {A : Template F} {u a Δ D Y w k : ℕ} {W cost : ℝ}
  [NeZero Y] [NeZero w] {I : Type*} (U : I → Setup A.scheme A.scheme.h u a Δ D Y w W)
  (R : Rotor F Y w) (fit : ∀ i, (U i).Fits R cost) (boards : ∀ i, Board A (U i) k)
  {e cap : ℕ} (b : Book A.scheme u e cap) (M : Template.Meter) (ha : a ≤ A.scheme.h)
local notation "E" => (A.reset R Δ D a b M)
local notation "t" => (Child.extra R Δ (A.scheme.h - a))
local notation "mx" => (A.scheme.m + t)
local notation "dx" => (Child.width D Y A.full)
local notation "n" => (A.scheme.h - a + 8)

structure Selection where
  layout : ∀ i, (U i).Layout R (fit i) b mx dx
  graph : I → (Child.Graph mx dx).obj
  address : Coord R A.scheme.h a Δ ↪ B t
  placed : ∀ i, Placed A (layout i) address
  ranked : ∀ i, Ranked (layout i)
  agree : ∀ i j v z σ, Board.Sample (boards i) (boards j) v z σ n →
    IndexAgrees (layout i) (layout j) (Board.path v z) σ v z
  describes : ∀ i, Child.Describes (m := mx) (d := dx) A.full
    ((U i).graph R (fit i)) (layout i).host (layout i).index (graph i)
  headers : I → (Tile.headers A E t).obj
  control : Tile.HeaderLocal A E k n t ha (fun i => (boards i).tape) headers
  build : ∀ i, Child.build A.scheme.m A.scheme.d t dx (A.nav (boards i).tape.1, headers i) = graph i

namespace Selection
variable {U R fit boards b M ha} (s : Selection U R fit boards b M ha)

abbrev output (i : I) : (Tile.whole A E).obj :=
  emitted M (s.layout i) (s.graph i) (parent A t)

theorem fields (hD : 0 < D) (delayed : A.full = false → A.scheme.h - a ≤ 32 * Nat.clog 2 (2 * D))
    (neutral : ∀ i v, (U i).G.diagram.arity v = 0 → ∀ x, Transcript.sample ((U i).G.diagram.table v) x = 1)
    (ready : ∀ i, b.Ready (s.layout i) (s.graph i).1) :
    Tile.Local A E k n t ha rfl (fun i => (boards i).tape) s.output := by
  intro i j _ _ _ _ eq
  exact Board.part_eq M le_rfl hD delayed (s.placed i) (s.placed j) (s.ranked i) (s.ranked j)
    (s.agree i j) (neutral i) (neutral j) (ready i) (ready j) eq

end Selection
end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-! # A single controlled layout across all branches of a reset -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
open Packing Coloring
open scoped Classical
variable {F : Type} [Field F] [Fintype F] {A : Template F} {u a Δ D Y w k : ℕ} {W cost : ℝ}
  [NeZero Y] [NeZero w] {I : Type*} (U : I → Setup A.scheme A.scheme.h u a Δ D Y w W)
  (R : Rotor F Y w) (fit : ∀ i, (U i).Fits R cost) (boards : ∀ i, Board A (U i) k)
  {e cap : ℕ} (b : Book A.scheme u e cap) (M : Template.Meter) (ha : a ≤ A.scheme.h)
local notation "E" => (A.reset R Δ D a b M)
local notation "ex" => (Child.extra R Δ (A.scheme.h - a))
local notation "mx" => (A.scheme.m + ex)
local notation "dx" => (Child.width D Y A.full)
local notation "n" => (A.scheme.h - a + 8)

def select (room : ∀ i, (U i).Room R (fit i) (E).scheme) :
    Selection U R fit boards b M ha := by
  let idx i := (U i).index R (fit i) A.full
  let hd i := (U i).desc R (fit i) A.full
  let L i := (U i).arrange R (fit i) b (idx i) (room i)
  have place i := (U i).arrange_placed R (fit i) b (idx i) (room i)
  refine ⟨L, fun i => Child.build _ _ _ _ (A.nav (boards i).tape.1, hd i),
    Child.code R Δ (A.scheme.h - a), place, fun i => (U i).arrange_ranked R (fit i) b (idx i) (room i),
    ?_, fun i => (U i).describes R (fit i) (boards i), hd, ?_, fun _ => rfl⟩
  · intro i j v z σ h v' z' hr loc loc'
    apply h.look.preview.idx_match R (fit i) (fit j) (k := 0) (by omega)
    · rw [station_parts, station_parts]
      exact Board.start v z
    · rw [station_parts, station_parts]
    · rw [station_parts, station_parts]
      exact h.look.widen (by omega) hr
    · rw [station_parts, station_parts]
  · intro i j x y h
    apply Board.vertex_eq M (place i) (place j) (hd i) (hd j) _ _ h
    · intro v z hv hz he
      unfold hd
      rw [desc_vacant _ _ _ _ _ hv, desc_vacant _ _ _ _ _ hz, he]
    · intro v z σ loc p frozen
      change hd i ((U i).host R (fit i) _) = hd j ((U j).host R (fit j) _)
      unfold hd
      refine ((U i).desc_live R (fit i) A.full _).trans (Eq.trans ?_ ((U j).desc_live R (fit j) A.full _).symm)
      apply p.suffix_eq R (fit i) (fit j) (k := 0) (by omega)
      · rw [station_parts, station_parts]
        exact Board.start v z
      · rw [station_parts, station_parts]
      · change (U i).G.frozen (((U i).result R (fit i)).origin _) ↔
          (U j).G.frozen (((U j).result R (fit j)).origin _)
        rw [station_owner, station_owner]
        exact frozen

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-! # The two local gates that write a reset from summarized inputs -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Tile
open Coloring
open scoped Classical

variable {F : Type} [Field F]

private theorem build_net {m d t l j u : ℕ} {L : Set (Table F)} (hm : j = m + t) (hu : 3 ≤ u) :
    Map F u L (Child.Input m d t l) (Child.Graph j l)
      (fun x => cast (congrArg (fun i => (Child.Graph i l).obj) hm.symm) (Child.build m d t l x))
      (4 * Child.buildCost m d t l) := by
  subst j
  exact Map.circuit hu (Child.build_net F m d t l)

variable (A D : Template F) (k n t : ℕ) (ha : D.scheme.h ≤ A.scheme.h) (hm : D.scheme.m = A.scheme.m + t)
local notation "m" => A.scheme.m
local notation "d" => A.scheme.d
local notation "l" => D.scheme.d

theorem writer_net {I : Type*} (x : I → (pair A k).obj) (y : I → (whole A D).obj)
    (z : I → (headers A D t).obj) (fields : Local A D k n t ha hm x y)
    (control : HeaderLocal A D k n t ha x z)
    (build : ∀ i, cast (congrArg (fun v => (Child.Graph v l).obj) hm.symm)
      (Child.build m d t l (A.nav (x i).1, z i)) = header D (y i).1)
    (hr : ∀ i, Fmt.Reciprocal (.vec A.scheme.h (.addr A.scheme.ℓ)) (x i).1.1) (hn : 0 < n) :
    ∃ f g : Table F, Processor.arity f = printWidth A D k n t ∧ Processor.arity g = headerWidth A D k n t ∧
      ∀ {u N : ℕ} {L : Set (Table F)}, 3 ≤ u → printWidth A D k n t ≤ u → headerWidth A D k n t ≤ u →
      f ∈ L → g ∈ L → Access F u L (m + d) (volume A D k n) N →
      Computes F u L (pair A k) (whole A D) x y (fun _ => 1)
        (printCost A D k n t N (headerCost A D k n t N + 4 * Child.buildCost m d t l)) := by
  obtain ⟨f, hf, body⟩ := print_net A D k n t ha hm x y fields hr hn
  obtain ⟨g, hg, head⟩ := header_net A D k n t ha hm x z control hr hn
  refine ⟨f, g, hf, hg, ?_⟩
  intro u N L hu hp hq h₁ h₂ access
  have next := (head hu hq h₂ access).comp (Computes.of_map
    (y := fun i => header D (y i).1) (build_net (L:=L) hm hu) build)
  simp only [one_mul] at next
  exact body hu hp h₁ access next

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Tile
end

/-! # Writing the reset network and its frozen-station controls -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Tile
open Coloring
open scoped Classical

variable {F : Type} (A D : Template F) (T : Attachment A) (k n t slots : ℕ)
  (ha : D.scheme.h ≤ A.scheme.h) (hm : D.scheme.m = A.scheme.m + t)

def attachedWidth :=
  max (max (printWidth A D k n t) (headerWidth A D k n t)) (queryWidth A D T k n t slots)

def attachedCost (N : ℕ) :=
  queryCost A D T k n t slots N
    (printCost A D k n t N (headerCost A D k n t N +
      4 * Child.buildCost A.scheme.m A.scheme.d t D.scheme.d) +
      4 * ((whole A D).width + 2 * D.format.width))

/-- The dictionary contains at most three local tables, independent
of the state, host, group and old attachment labels. -/
theorem attached_net [Field F] {I : Type*} (x : I → (pair A k).obj)
    (qs : I → Attachment.Query T D slots 0) (z : I → (headers A D t).obj)
    (hloc : Local A D k n t ha hm x (fun i => ((qs i).fresh, (qs i).M.commands)))
    (hheader : HeaderLocal A D k n t ha x z)
    (hbuild : ∀ i, cast (congrArg (fun v => (Child.Graph v D.scheme.d).obj) hm.symm)
      (Child.build A.scheme.m A.scheme.d t D.scheme.d (A.nav (x i).1, z i)) = header D (qs i).fresh)
    (hquery : QueryLocal A D T k n t slots ha hm x qs)
    (hr : ∀ i, Fmt.Reciprocal (.vec A.scheme.h (.addr A.scheme.ℓ)) (x i).1.1) (hn : 0 < n) :
    ∃ gates : Finset (Table F), gates.card ≤ 3 ∧
      (∀ f ∈ gates, Processor.arity f ≤ attachedWidth A D T k n t slots) ∧
      ∀ {u N : ℕ} {L : Set (Table F)}, 3 ≤ u → attachedWidth A D T k n t slots ≤ u →
      (∀ f ∈ gates, f ∈ L) → Access F u L (A.scheme.m + A.scheme.d) (volume A D k n) N →
      Computes F u L (T.format.pair (pair A k)) (T.Requests D slots 0)
        (fun i => ((qs i).old, x i)) (fun i => (qs i).requests) (fun _ => 1)
        (attachedCost A D T k n t slots N) := by
  let y (i : I) : (whole A D).obj := ((qs i).fresh, (qs i).M.commands)
  obtain ⟨f, g, hf, hg, write⟩ := writer_net A D k n t ha hm x y z hloc hheader hbuild hr hn
  obtain ⟨e, he, run⟩ := query_net A D T k n t slots ha hm x qs hquery hr hn
  refine ⟨{f, g, e}, Finset.card_le_three, ?_, ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro _ (rfl|rfl|rfl) <;> unfold attachedWidth <;> omega
  intro u N L hu hw hl access
  unfold attachedWidth at hw
  have h := write hu (by omega) (by omega) (hl f (by simp)) (hl g (by simp)) access
  have proj : Circuit F (whole A D) D.format Prod.fst ((whole A D).width + 2 * D.format.width) :=
    Circuit.project Sum.inl (fun _ _ => rfl)
  have fresh := h.comp (Computes.of_map (y := fun i => (qs i).fresh) (Map.circuit hu proj)
    (fun _ => rfl))
  simp only [one_mul] at fresh
  exact run hu (by omega) (hl e (by simp)) access fresh

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Tile
end
