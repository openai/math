import OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Wiring
import OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Presentation
import OAI.LinearAlgebra.MatrixExponent.Sphere.Waves.Price
import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Presents
import OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Children.Correct
import OAI.LinearAlgebra.MatrixExponent.Sphere.Panel.Wave
import OAI.LinearAlgebra.MatrixExponent.Sphere.Panel.Terminal
import OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Children.Traces

/-! # A uniform dictionary for terminal station and relay tables -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print
open Coloring Assembly Surface.Local
open scoped Classical

structure Printer (F K N : Type) (m d h ℓ M r t q D k n u j z : ℕ) where
  menu : B ℓ → Option (Face F (M * r) (M * t) q K N)
  dyadic : D = 2 ^ n
  large : 4 ≤ D
  chunks : M ≤ D ^ k
  degree : 2 ^ ((d + 1) * 1) ≤ D ^ k + 1
  cap : ℕ
  pos : 0 < u

def indexBits (A : Type) := Nat.clog 2 (Nat.card A)

def indexCode (A : Type) [Finite A] : A ↪ B (indexBits A) := by
  letI := Fintype.ofFinite A
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  simp only [B, indexBits, Fintype.card_fin, Nat.card_eq_fintype_card]
  exact Nat.le_pow_clog (by decide) _

namespace Printer
variable {F K N : Type} {m d h ℓ M r t q D k n u j z : ℕ}
  (P : Printer F K N m d h ℓ M r t q D k n u j z)

abbrev digits (_ : Printer F K N m d h ℓ M r t q D k n u j z) := z * M * (q + 2 * (2 * D ^ k))
abbrev part (_ : Printer F K N m d h ℓ M r t q D k n u j z) := Children.Part M D k n
abbrev lane (_ : Printer F K N m d h ℓ M r t q D k n u j z) := Compass.FinalLane (Fin q) K M D k n
abbrev childBits := indexBits P.part
abbrev spanBits := indexBits (Band P.lane P.cap)
abbrev window := Fmt.wave d 1 1 (.addr ℓ) (.addr P.digits)
abbrev labelBits := P.window.width + P.childBits
abbrev selectors := Format.vec m (.vec h (.addr P.digits))
abbrev rows (_ : Printer F K N m d h ℓ M r t q D k n u j z) := Fmt.rows m d h (.addr ℓ)

theorem window_width : P.window.width = 2 ^ ((d + 1) * 1) * (2 ^ ((d + 1) * 1) * (ℓ + P.digits)) := by
  simp only [window, Fmt.wave, Fmt.view, Format.width_vec, Format.width_pair, Format.width_addr]

include P in
theorem positive : 0 < D ^ k := pow_pos (lt_of_lt_of_le (by decide) P.large) k

def ballot : Ballot M q D k z ≃ B P.digits :=
  Fintype.equivOfCardEq (by simp [B, Ballot, Axis, Number, Digits, digits, pow_mul])

abbrev slot := indexCode P.part
abbrev ix [Finite K] := indexCode (Band P.lane P.cap)

def view (v : P.window.obj) : Lens F K N M r t q D k z d :=
  fun a b => (P.menu (v a b).1, P.ballot.symm (v a b).2)

def tariff [Field F] (v : P.window.obj) : F := (P.view v).score P.positive

def request (v : Lens F K N M r t q D k z d) (c : P.part)
    (p : Page F (Fin q) (Number D k) K M r t) :
    Request F (Fin q) (Number D k) K M r t (Layout.Sharing.radius k * n) (Children.degree d P.childBits) :=
  ⟨p.1, p.2, wiring P.dyadic P.large P.chunks P.degree P.slot v.tone, lift (Prod.mk p.1.mark) c⟩

def send [Field F] (v : Lens F K N M r t q D k z d) (c : P.part) :=
  (v.page P.positive).bind fun s => (P.request v c s).emit j u

def read [Field F] (v : B P.labelBits) : Option (Star F P.lane (Children.degree d P.childBits)) :=
  let p := Match.rowIndex _ _ v
  Function.extend P.slot (P.send (P.view ((Design.number P.window).symm p.1))) (fun _ => none) p.2

variable [Field F] [Finite K]

def engine : Engine F P.lane where
  m := m + P.childBits
  d := Children.degree d P.childBits
  h := h
  e := P.spanBits
  ℓ := P.labelBits
  cap := P.cap
  ix := P.ix
  decode x := ((P.read x).map fun a => a.pattern P.ix u).getD Star.vacant

abbrev template : Assembly.Template F where
  scheme := P.engine.scheme
  count := P.labelBits
  load x := if (P.read x).isSome then (∑ i, (P.engine.decode x).width 0 i : ℕ) + (u : ℝ) else 0
  park _ := 0
  past _ := 0
  order := Equiv.refl _

abbrev split : B P.template.scheme.m ≃ B m × B P.childBits := Match.rowIndex _ _

def outer : Bool ↪ B P.template.scheme.e :=
  ⟨fun b => P.ix (b, none), fun _ _ h => congrArg Prod.fst (P.ix.injective h)⟩

end Printer
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print
end

/-! # The counter records exactly the charge of an occupied site -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Assembly Coloring Rounds
open scoped Classical

variable {F K N : Type} [Field F] [Finite K] {m d h ℓ M r t q D k n u j z : ℕ}
    (U : Printer F K N m d h ℓ M r t q D k n u j z)

variable {x y : Wire} {G : Diagram F x y} {r' : U.template.format.obj}
    (p : U.template.scheme.Presentation r'.1 G)

private theorem load_arity (v : G.V) (hv : (U.read ((r'.1 (p.vertex v).1).2 (p.vertex v).2.1)).isSome) :
    U.template.load ((r'.1 (p.vertex v).1).2 (p.vertex v).2.1) = G.arity v + (u : ℝ) := by
  have hh := Fintype.card_congr (p.pin v)
  simp only [Diagram.Port, Scheme.LocalPin, Fintype.card_sigma, Fintype.card_sum, card_slots,
    Fintype.card_fin] at hh
  change G.arity v = ∑ s, U.template.scheme.width r'.1 (p.vertex v, s) at hh
  have hz : (p.vertex v).2.2 = 0 := Fin.eq_zero _
  rw [hh]
  change (if (U.read _).isSome then _ else 0) = _
  rw [ite_eq_left hv]
  simp only [Scheme.width, hz]
  rfl

theorem amount (charge : G.V → ℝ) (hc : ∀ v, charge v = G.arity v + (u : ℝ))
    (copy : ∀ i j, U.template.counter r' i j = (r'.1 i).2 j)
    (live : ∀ v, (U.read ((r'.1 (p.vertex v).1).2 (p.vertex v).2.1)).isSome)
    (idle : ∀ v ∉ Set.range p.vertex, U.read ((r'.1 v.1).2 v.2.1) = none)
    (i : B U.template.scheme.m) (j : B U.template.scheme.h) :
    U.template.load (U.template.counter r' i j) =
      ∑ v, if (p.vertex v).1 = i ∧ (p.vertex v).2.1 = j then charge v else 0 := by
  rw [copy]
  let q : U.template.scheme.Vtx := (i, j, 0)
  have he (v : G.V) : (p.vertex v).1 = i ∧ (p.vertex v).2.1 = j ↔ p.vertex v = q :=
    ⟨fun hx => Prod.ext hx.1 (Prod.ext hx.2 (Fin.eq_zero _)), fun h => by rw [h]; exact ⟨rfl, rfl⟩⟩
  simp only [he]
  by_cases hq : q ∈ Set.range p.vertex
  · obtain ⟨v, hv⟩ := hq
    have h := U.load_arity p v (live v)
    rw [hv] at h
    simp only [← hv, p.vertex.injective.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hc]
    exact h
  · have hv : U.read ((r'.1 i).2 j) = none := idle q hq
    change (if (U.read _).isSome then _ else 0) = _
    rw [hv]
    symm
    exact Finset.sum_eq_zero (fun v _ => ite_eq_right (fun he => hq ⟨v, he⟩))

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! # The record and scalar computed by a printer -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Coloring Assembly Surface.Local
open scoped Classical

variable {F K N : Type} {m d h ℓ M r t q D k n u j z : ℕ}
  (U : Printer F K N m d h ℓ M r t q D k n u j z)
  (data : U.rows.obj) (status : (Children.Header m d).obj) (choice : U.selectors.obj)

def around :=
  Fmt.around 1 1 (show (Fmt.waveIn m d h (.addr ℓ) (.addr U.digits)).obj from (data, choice))

def update : (Children.input m d h U.window.width).obj :=
  (Fmt.update (D := .addr U.window.width) (Design.number U.window) (U.around data choice), status)

def score [Field F] : F := Fmt.weight U.tariff (U.around data choice)

def advance [Field F] [Finite K] : U.template.format.obj :=
  Children.write U.slot U.dyadic U.large U.chunks U.degree (U.update data status choice)

def gate [Field F] := weightTable (D := .addr U.window.width) (Design.number U.window) U.tariff

def pack : ((B m × B h) × Axis (Fin q) (Number D k) → Digits M z) ≃ U.selectors.obj where
  toFun v i l := U.ballot (fun x => v ((i, l), x))
  invFun v i := U.ballot.symm (v i.1.1 i.1.2) i.2
  left_inv v := funext fun i => congrFun (U.ballot.symm_apply_apply (fun x => v (i.1, x))) i.2
  right_inv v := funext fun i => funext fun l => U.ballot.apply_symm_apply (v i l)

def ballots (i : B m × B h) := U.ballot.symm (choice i.1 i.2)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! # From the indexed input tape to colored local views -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Assembly Coloring Surface.Local
open scoped Classical

variable {F K N V E : Type} {m d h ℓ M r t q D k n u j z : ℕ}
  (U : Printer F K N m d h ℓ M r t q D k n u j z)
  (data : U.rows.obj) (a : Atlas V E m d h) (f : V → Face F (M * r) (M * t) q K N)

structure Receives : Prop where
  graph : ∀ i, (data i).1 = a.graph i
  labels : ∀ i, U.menu ((data i.1).2 i.2) = a.fill f i

namespace Receives
variable {U data a f} (H : U.Receives data a f)
  (status : (Children.Header m d).obj) (c : U.selectors.obj)
include H

theorem tape : Children.tape (U.update data status c) = (a.graph, status) := by
  refine Prod.ext ?_ rfl
  exact funext H.graph

theorem view (v : B m × B h) :
    U.view (((U.around data c) v.1).2 v.2) = lens a f (U.ballots c) v := by
  funext i l
  let w := a.around 1 (a.around 1 v i) l
  have eq : ((U.around data c) v.1).2 v.2 i l = ((data w.1).2 w.2, c w.1 w.2) := by
    unfold Printer.around Fmt.around Fmt.expand Fmt.zip w Atlas.around
    simp only [H.graph]
  unfold Printer.view
  rw [eq, H.labels w]
  rfl

theorem score [Field F] :
    U.score data c = ∏ i, (lens a f (U.ballots c) i).score U.positive := by
  rw [Fintype.prod_prod_type]
  unfold Printer.score Fmt.weight tariff
  exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun l _ =>
    congrArg (fun v => v.score U.positive) (H.view c (i, l))

variable [Field F] [Finite K]
local notation "O" => U.advance data status c

theorem read_at (i : B (m + U.childBits)) (l : B h) :
    U.read (((O).1 i).2 l) = Function.extend U.slot
      (U.send (lens a f (U.ballots c) ((U.split i).1, l))) (fun _ => none) (U.split i).2 := by
  change U.read (Children.label _ (U.update data status c) i l) = _
  unfold Printer.read
  rw [Children.label_at (U.update data status c) i l]
  simp only [Printer.update, Fmt.update, Equiv.symm_apply_apply]
  exact congrArg (fun v => Function.extend U.slot (U.send v) (fun _ => none) (U.split i).2)
    (H.view c ((U.split i).1, l))

end Receives
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-!
# The intrinsic data needed to print one terminal state

Species counts are kept abstract here so that the caller can work
with the original unchunked records and station orders.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print
open Coloring Assembly Rounds Surface Surface.Local
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Alphabet Key Place)
open scoped Classical

variable {F K N X Z J I : Type} [Field F] {x y : Wire} {m d h ℓ M r t q D k n u j z : ℕ}
  {T R g r₀ t₀ w : ℕ} {W : ℝ} {P : Input F x y h D T R g W}
  {Y : Alphabet P.Occupied} {s : Stage F r₀ t₀ Z P.Occupied P.grid.Seam X}
  (Q : Key.Source Y x y s) (left : Order.Exterior Q.left) (right : Order.Exterior Q.right)

def Keeps {S : Scheme F} {s₀ : S.format.obj} (p : S.Presentation s₀ P.diagram)
    (loc : P.Occupied ↪ B S.m × B S.h) : Prop :=
  ∀ e : slots x ⊕ slots y, let v := Packing.portEnd P.diagram e
    ∃ i : Place s.scene.cell, loc i.1 = ((p.vertex v).1, (p.vertex v).2.1) ∧
      left.ports i = P.diagram.extLeft v ∧ right.ports i = P.diagram.extRight v

namespace Printer
variable (U : Printer F K N m d h ℓ M r t q D k n u j z)
  (a : Atlas P.Occupied P.grid.Seam m d h) (π : Palette a w q)
  (β : P.Occupied ⊕ ℕ → K) (R₀ : Reference J I N P.Occupied P.grid.Seam Z X)
  (G : Record F r₀ t₀ P.Occupied P.grid.Seam K N)
  (hm : Matches R₀.world β s G) (index : ∀ v, Y.state v ↪ ℕ) (size : P.Occupied → ℕ)
  (ext : P.Occupied → Option N → Bool → ℕ) (old : P.V ↪ B m)
  (data : U.rows.obj) (status : (Children.Header m d).obj)

def faces (v : P.Occupied) : Face F r₀ t₀ q K N :=
  ⟨ext v, π.mark v, G.tile π.edge (catalog size β s) v⟩

structure Signal : Prop where
  radius : 2 ≤ w
  source : Q.src = a.src
  target : Q.dst = a.dst
  layout : ∃ c, s.Layout a.src a.dst c
  distinct : Distinct (a.near 1) s β
  location : ∀ v, a.coord v = (old v.val.1, cellIndex h v.val.2)
  parents : Children.Shows P.adj old (a.graph, status)
  graph : ∀ i, (data i).1 = a.graph i
  read : ∀ i, HEq (U.menu ((data i.1).2 i.2)) (a.fill (faces (s := s) a π β G size ext) i)
  exterior : ∀ i b, cond b (right.ports i).length (left.ports i).length = ext i.1 (hm.row i).name b
  hi : ∀ v x y z, R₀.key v (Q.init x y z) = index v (z v)
  he : ∀ i b c z, R₀.ext (Layout.item s.scene.cell i).label.name (Q.init b c z) =
    ((left.ports i).map (bits x b), (right.ports i).map (bits y c))
  sel : ∀ v, (Y.width v, Order.decode _ _ (Y.code v) (Sum.inl ∘ index v)) =
    Key.info t₀ (.inl (size v))

end Printer
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print
end

/-! # Physical locations of live stations and relay nodes -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer

open Coloring Assembly Rounds Surface Surface.Local
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Alphabet Key Node Sharing)
open scoped Classical

variable {F K N X Z : Type} [Field F] [Finite K] {x y : Wire} {m d h ℓ M r t q D k n u j z : ℕ}
  {T R g w : ℕ} {W : ℝ} {P : Input F x y h D T R g W}
  {Y : Alphabet P.Occupied} {s : Stage F (M * r) (M * t) Z P.Occupied P.grid.Seam X}
  {Q : Key.Source Y x y s} (U : Printer F K N m d h ℓ M r t q D k n u j z)
  (G : (Key.share s Q).Geo P k) {a : Atlas P.Occupied P.grid.Seam m d h} (π : Palette a w q)
  (old : P.V ↪ B m) (data : U.rows.obj) (status : (Children.Header m d).obj)

structure Physical where
  labels : Marking (Key.share s Q) (Fin q) (Number D k) K
  rules : Order.Rules (Key.share s Q)
  face : P.Occupied → Face F (M * r) (M * t) q K N
  aligned : Aligned π U.positive labels rules face
  wire : CircuitMap π G labels old U.degree
  location : ∀ i, a.coord i = (old (G.site i).1, cellIndex h (G.site i).2)
  parents : Children.Shows P.adj old (a.graph, status)
  steer : G.steer = parents.steer U.degree
  received : U.Receives data a face
  range : ∀ i, cost s.scene.cell s.scene.level i < 2 ^ z

namespace Physical
variable {U G π old data status} (B : U.Physical G π old data status)
  (p : Layout.Profile s.scene.cell s.scene.level)

local notation "S" => Key.share s Q
local notation "H" => G.layout U.dyadic U.large p j
local notation "V" => Node (Sharing.Position S) (Sharing.radius k * n)

abbrev term := (H).ordered (G.external U.dyadic U.large p j) U.pos (B.rules.script p j)
def select := (B.labels.select a.coord _ B.range).relabel U.pack
abbrev record := U.advance data status (B.select.write p)
abbrev host (_ : U.Physical G π old data status) := Children.host old U.slot
abbrev idx (_ : U.Physical G π old data status) := Children.idx old U.slot a.graph
abbrev vertex := Compass.vertex (U := U.engine) (G := G) U.dyadic U.large p j B.host (cellIndex h).toEmbedding
abbrev child (_ : U.Physical G π old data status) (v : V) := lift Prod.snd ((H).place v).1
abbrev lensAt (i : Coloring.B m × Coloring.B h) := lens a B.face (B.aligned.ballots B.range p) i

omit [Finite K] in
theorem score (c : U.selectors.obj) : U.score data c = (B.select.read c).elim 0 Layout.Profile.sign :=
  (B.received.score c).trans (B.aligned.score B.range (U.ballots c))

omit [Field F] [Finite K] in
theorem ballots : U.ballots (B.select.write p) = B.aligned.ballots B.range p :=
  funext fun _ => U.ballot.symm_apply_apply _

theorem address (v : V) :
    U.split (B.vertex p v).1 = ((a.coord ((S).home (root v))).1, U.slot (B.child p v)) ∧
      (B.vertex p v).2.1 = (a.coord ((S).home (root v))).2 := by
  have e := Compass.home_eq (G := G) U.dyadic U.large p j v
  rw [B.location, ← e]
  exact ⟨Children.host_split old U.slot _, rfl⟩

omit [Finite K] in
theorem color (v : V) : lift (Prod.mk (π.mark ((S).home (root v)))) (B.child p v) =
    lift B.labels.spot v := by
  cases v with
  | inl v => exact congrArg Sum.inl (B.wire.slot v).symm
  | inr v => exact congrArg (fun w => Sum.inr (w, v.2)) (B.wire.slot v.1).symm

omit [Finite K] in
theorem active (v : V) :
    U.send (B.lensAt p (a.coord ((S).home (root v)))) (B.child p v) =
      some ((B.labels.names p j u H B.idx).star ((H).routed (B.rules.script p j) u) v) := by
  let x := (S).home (root v)
  rw [send, B.aligned.page, Option.bind_some]
  refine B.wire.emit U.dyadic U.large U.slot p j u B.rules v _ rfl ?_ ?_ ?_
  · exact B.aligned.observes (B.aligned.ballots B.range p) x
  · change lift (Prod.mk (B.labels.mark x)) _ = _
    rw [B.aligned.mark]
    exact B.color p v
  · exact congrArg (wiring U.dyadic U.large U.chunks U.degree U.slot)
      (tones π B.face _ B.aligned.color x)

omit [Finite K] in
theorem active_only (i : Coloring.B m × Coloring.B h) (c : U.part) (h : (U.send (B.lensAt p i) c).isSome) :
    ∃ v : V, a.coord ((S).home (root v)) = i ∧ B.child p v = c := by
  by_cases hi : i ∈ Set.range a.coord
  swap
  · simp [send, lensAt, Lens.page, center, a.fill_away _ hi] at h
  obtain ⟨v, rfl⟩ := hi
  rw [send, B.aligned.page, Option.bind_some] at h
  obtain ⟨w, hw, hc⟩ := B.labels.emit_live B.rules p j u v _ rfl h
  refine ⟨w, congrArg a.coord hw, ?_⟩
  rw [← B.color p w] at hc
  have ee (i : Fin q) (x : U.part) : lift Prod.snd (lift (Prod.mk i) x) = x := by cases x <;> rfl
  exact (ee _ _).symm.trans ((congrArg (lift Prod.snd) hc).trans (ee _ _))

end Physical
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! # Constructing the physical labels from terminal records -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer.Signal
open Coloring Assembly Rounds Surface Surface.Local
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Alphabet Key Place Sharing item)
open scoped Classical

variable {F K N X Z J I : Type} [Field F] {x y : Wire} {m d h ℓ M r t q D k n u j z : ℕ}
  {T R g w : ℕ} {W : ℝ} {P : Input F x y h D T R g W}
  {Y : Alphabet P.Occupied} {s : Stage F (M * r) (M * t) Z P.Occupied P.grid.Seam X}
  {Q : Key.Source Y x y s} {left : Order.Exterior Q.left} {right : Order.Exterior Q.right}
  {U : Printer F K N m d h ℓ M r t q D k n u j z}
  {a : Atlas P.Occupied P.grid.Seam m d h} {π : Palette a w q}
  {β : P.Occupied ⊕ ℕ → K} {R₀ : Reference J I N P.Occupied P.grid.Seam Z X}
  {G : Record F (M * r) (M * t) P.Occupied P.grid.Seam K N}
  {hm : Matches R₀.world β s G} {index : ∀ v, Y.state v ↪ ℕ} {size : P.Occupied → ℕ}
  {ext : P.Occupied → Option N → Bool → ℕ} {old : P.V ↪ B m}
  {data : U.rows.obj} {status : (Children.Header m d).obj}
  (H : U.Signal Q left right a π β R₀ G hm index size ext old data status)

omit [Field F] in
theorem physical (G₀ : (Key.share s Q).Geo P k) (hs : ∀ i, G₀.site i = i.val)
    (hf : G₀.frozen = (fun i => (item s.scene.cell i).label.role = .collector)) (hg : G₀.steer = H.parents.steer U.degree)
    (hz : ∀ i, cost s.scene.cell s.scene.level i < 2 ^ z) :
    ∃ B : U.Physical G₀ π old data status, B.rules.left = left ∧ B.rules.right = right := by
  obtain ⟨c, hc⟩ := H.layout
  obtain ⟨L, hl, hr, ht, he⟩ := Key.intrinsic index hm left right H.hi H.he
  let W := marking s Q a π β G₀.count H.source H.target H.radius hc H.distinct
  let f := faces (s := s) a π β G size ext
  have ep : W.edge = π.edge := by
    funext i
    change (π.mark (Q.src i), π.mark (Q.dst i)) = _
    rw [H.source, H.target]; rfl
  have hn (i : Place s.scene.cell) : W.number i = number U.positive i.2.val (hm.row i).role := by
    have e := (hm.represents i).role
    change (decide ((item s.scene.cell i).label.role = .collector), _) = _
    unfold number
    refine Prod.ext ?_ (Fin.ext (Nat.mod_eq_of_lt (i.2.isLt.trans_le (G₀.count i.1))).symm)
    rw [e]
  have near (i) : a.near 1 (Q.src i) (Q.dst i) := by rw [H.source, H.target]; exact a.near_edge i
  have ha : Aligned π U.positive W L f := by
    refine ⟨H.radius, rfl, fun _ => rfl, near, ?_, ?_, ?_⟩
    · intro i
      change ofBody (G.body π.edge i) (W.mark i) _ = _
      rw [← ep]
      exact ofBody_eq hm W _ hn i
    · intro i; exact (footprint hm W rfl i).symm
    · intro p i
      change ofTile ⟨G.body π.edge i, catalog size β s i⟩ (W.mark i) _ _ _ = _
      rw [← ep]
      apply ofTile_eq hm W rfl L size _ ext p hn
      · rw [hl, hr]; exact H.exterior
      · exact he
      · unfold Order.Rules.signal
        rw [ht]
        exact Key.symbol_info index size H.sel _
  have loc (i) : a.coord i = (old (G₀.site i).1, cellIndex h (G₀.site i).2) := by rw [hs, H.location]
  have ac : CircuitMap π G₀ W old U.degree := by
    refine ⟨fun i => congrArg Prod.fst (loc i), ?_, ?_, near, H.radius⟩
    · rintro ((i|v|v)|(v|v))
      · change (_, Sum.inl _) = (_, Sum.inl (decide (G₀.frozen i), _))
        rw [hf]
        dsimp only [W, marking, coordinate, Sharing.home]
        congr!
      all_goals rfl
    · intro v l; rw [hg]; rfl
  exact ⟨⟨W, L, f, ha, ac, loc, H.parents, hg, ⟨H.graph, fun i => eq_of_heq (H.read i)⟩, hz⟩, hl, hr⟩

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer.Signal
end

/-! # Exact support of the printed station dictionary -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer

open Coloring Assembly Rounds Surface Surface.Local
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Alphabet Key Node Sharing)
open scoped Classical

variable {F K N X Z : Type} [Field F] [Finite K] {x y : Wire} {m d h ℓ M r t q D k n u j z : ℕ}
  {T R g w : ℕ} {W : ℝ} {P : Input F x y h D T R g W}
  {Y : Alphabet P.Occupied} {s : Stage F (M * r) (M * t) Z P.Occupied P.grid.Seam X}
  {Q : Key.Source Y x y s} (U : Printer F K N m d h ℓ M r t q D k n u j z)
  (G : (Key.share s Q).Geo P k) {a : Atlas P.Occupied P.grid.Seam m d h} (π : Palette a w q)
  (old : P.V ↪ B m) (data : U.rows.obj) (status : (Children.Header m d).obj)

namespace Physical
variable {U G π old data status} (B : U.Physical G π old data status)
  (p : Layout.Profile s.scene.cell s.scene.level)

local notation "S" => Key.share s Q
local notation "H" => G.layout U.dyadic U.large p j
local notation "V" => Node (Sharing.Position S) (Sharing.radius k * n)

theorem read_eq (i : U.engine.scheme.Vtx) :
    U.read (((B.record p).1 i.1).2 i.2.1) = Function.extend U.slot
      (U.send (B.lensAt p ((U.split i.1).1, i.2.1))) (fun _ => none) (U.split i.1).2 := by
  have he := B.received.read_at status (B.select.write p) i.1 i.2.1
  rw [B.ballots] at he
  exact he

theorem read_active (v : V) : U.read (((B.record p).1 (B.vertex p v).1).2 (B.vertex p v).2.1) =
    some ((B.labels.names p j u H B.idx).star ((H).routed (B.rules.script p j) u) v) := by
  rw [B.read_eq, (B.address p v).1, (B.address p v).2, U.slot.injective.extend_apply]
  exact B.active p v

theorem read_inactive (i : U.engine.scheme.Vtx) (hi : i ∉ Set.range (B.vertex p)) :
    U.read (((B.record p).1 i.1).2 i.2.1) = none := by
  rw [B.read_eq]
  by_cases he : (U.split i.1).2 ∈ Set.range U.slot
  swap
  · exact Function.extend_apply' _ _ _ he
  obtain ⟨c, hc⟩ := he
  rw [← hc, U.slot.injective.extend_apply]
  by_contra hne
  obtain ⟨v, hv, ht⟩ := B.active_only p _ _ (Option.isSome_iff_ne_none.mpr hne)
  obtain ⟨h₁, h₂⟩ := B.address p v
  rw [hv, ht, hc] at h₁
  rw [hv] at h₂
  refine hi ⟨v, Prod.ext (U.split.injective h₁) (Prod.ext h₂ ?_)⟩
  exact Fin.eq_zero i.2.2 |>.symm

end Physical
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! # A presentation of the diagram selected by a physical printer -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer

open Coloring Assembly Rounds Surface Surface.Local
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Alphabet Key Node Sharing)
open scoped Classical

variable {F K N X Z : Type} [Field F] [Finite K] {x y : Wire} {m d h ℓ M r t q D k n u j z : ℕ}
  {T R g w : ℕ} {W : ℝ} {P : Input F x y h D T R g W}
  {Y : Alphabet P.Occupied} {s : Stage F (M * r) (M * t) Z P.Occupied P.grid.Seam X}
  {Q : Key.Source Y x y s} (U : Printer F K N m d h ℓ M r t q D k n u j z)
  (G : (Key.share s Q).Geo P k) {a : Atlas P.Occupied P.grid.Seam m d h} (π : Palette a w q)
  (old : P.V ↪ B m) (data : U.rows.obj) (status : (Children.Header m d).obj)

namespace Physical
variable {U G π old data status} (B : U.Physical G π old data status)
  (p : Layout.Profile s.scene.cell s.scene.level)

local notation "S" => Key.share s Q
local notation "H" => G.layout U.dyadic U.large p j
local notation "V" => Node (Sharing.Position S) (Sharing.radius k * n)
local notation "A" => U.template
local notation "rows" => B.record p
local notation "node" => (B.term p)
local notation "tree" => (G.tree U.dyadic U.large)
local notation "graph" => Children.graph U.slot U.dyadic U.large U.chunks U.degree (a.graph, status)

theorem record_header :
    ((A).nav rows, fun i => (((A).live rows i, (A).frozen rows i), (A).flags rows i)) = graph := by
  change Children.graph U.slot U.dyadic U.large U.chunks U.degree
    (Children.tape (U.update data status (B.select.write p))) = _
  rw [B.received.tape]

theorem nav_at (x y : Host P.V M D k n) (hy : y ∈ (tree).adj x) :
    (A).nav rows (B.host x) (B.idx x y) = B.host y := by
  have he := congrArg Prod.fst (B.record_header p)
  change (A).nav rows = (graph).1 at he
  rw [he]
  exact (Children.used_column U.slot U.dyadic U.large U.chunks U.degree G B.parents B.steer x y hy).1

omit [Finite K] in
theorem charge (v : V) : (node).charge v = (node).diagram.arity v + (u : ℝ) := by
  have h := ((H).routed (B.rules.script p j) u).drawing.arity v
  exact congrArg (fun i : ℕ => (i : ℝ) + u) h.symm

variable (hw : ∀ i, Diagram.padWidth u (((Key.share s Q).backdrop.emitted p j).width i) / u ≤ U.cap)

def frame : Frame U.engine (rows).1 (B.labels.names p j u H B.idx) ((H).routed (B.rules.script p j) u) u where
  vertex := B.vertex p
  pos := U.pos
  width i := Diagram.dvd_padWidth U.pos _
  bound i := hw i.1
  active v := by
    change ((U.read _).map _).getD _ = _
    rw [B.read_active]
    rfl
  inactive v hv := by
    change ((U.read _).map _).getD _ = _
    rw [B.read_inactive p v hv]
    rfl
  address t i := by
    let x := (H).place (side ((H).pad u).route.net t i)
    let y := (H).place (side ((H).pad u).route.net (!t) i)
    have he : x.2 = y.2 ∧ y.1 ∈ (tree).adj x.1 := by
      have hi := ((H).pad u).edges i
      have hp (v : V) : ((H).pad u).place v = (H).place v := by cases v <;> rfl
      simp only [Layout.Fanout.linked, hp] at hi
      unfold x y
      cases t
      · exact hi
      · exact ⟨hi.1.symm, (tree).adj_symm hi.2⟩
    change ((A).nav rows (B.host x.1) (B.idx x.1 y.1), cellIndex h x.2, (0 : Coloring.B 0)) =
      (B.host y.1, cellIndex h y.2, 0)
    rw [B.nav_at p _ _ he.2, he.1]
    rfl

end Physical
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! # The family of terms carried by one controlled emission -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Assembly Coloring Rounds
open scoped Classical

variable {F K N : Type} [Field F] [Finite K] {x y : Wire} {S : Scheme F}
  {d ℓ M r t q D k n u j z T R g : ℕ} {W : ℝ} {P : Input F x y S.h D T R g W}
  {tape : S.format.obj} (U : Printer F K N S.m d S.h ℓ M r t q D k n u j z)
  (pres : S.Presentation tape P.diagram) (data : U.rows.obj) (status : (Children.Header S.m d).obj)
  (f : Val x → Val y → F) (σ : ℕ)

structure Release where
  I : Type
  [finite : Fintype I]
  select : Transcript.Selector I U.selectors.obj
  coeff : I → F
  term : I → LocalTerm F x y S.h u
  value : ∀ x y, ∑ i, coeff i * (term i).diagram.eval x y = f x y
  bound : ∀ i, Concentrated P (term i) (Input.terminalExponent g σ) n σ
  populated : ∀ i, Nonempty (term i).V
  valid : ∀ c, U.score data c = (select.read c).elim 0 coeff
  shows : ∀ i, U.template.Shows (U.advance data status (select.write i)) (term i)
  retains : ∀ i, Payload.Retains pres (shows i).pres U.split U.outer
  reciprocal : Fmt.Reciprocal (.vec S.h (.addr ℓ)) data

attribute [instance] Release.finite

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! # Reading a named collector's exterior wires after printing -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Frame
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout Assembly
open scoped Classical
variable {F α A : Type} [Field F] {a b : Wire} {u : ℕ} {G : Bundled F a b}
  {U : Engine F A} {r : U.scheme.format.obj} {N : Names G A U.d} {p : Order.Script G α}
  (H : Frame U r N p u)

private theorem exterior_left (v : G.V) (l : List (slots a))
    (hl : p.left.ports v = l) (i : Fin l.length) :
    let e := (H.presentation.boundary (.inl (l.get i))).val
    e.1 = H.exterior v false ∧ e.2.val = i.val := by
  subst l
  change let e := H.presentation.toSeating.ends (.inl (.inl (p.left.enum.get v i)))
         e.1 = H.exterior v false ∧ e.2.val = i.val
  rw [H.ends_eq, H.left]
  exact ⟨rfl, rfl⟩

private theorem exterior_right (v : G.V) (l : List (slots b))
    (hl : p.right.ports v = l) (i : Fin l.length) :
    let e := (H.presentation.boundary (.inr (l.get i))).val
    e.1 = H.exterior v true ∧ e.2.val = i.val := by
  subst l
  change let e := H.presentation.toSeating.ends (.inr (.inl (p.right.enum.get v i)))
         e.1 = H.exterior v true ∧ e.2.val = i.val
  rw [H.ends_eq, H.right]
  exact ⟨rfl, rfl⟩

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Frame

namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer

open Coloring Assembly Rounds Surface Surface.Local
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Alphabet Key Node Sharing)
open scoped Classical

variable {F K N X Z : Type} [Field F] [Finite K] {x y : Wire} {S : Scheme F} {d ℓ M r t q D k n u j z : ℕ}
  {T R g w : ℕ} {W : ℝ} {P : Input F x y S.h D T R g W}
  {Y : Alphabet P.Occupied} {s : Stage F (M * r) (M * t) Z P.Occupied P.grid.Seam X}
  {Q : Key.Source Y x y s} (U : Printer F K N S.m d S.h ℓ M r t q D k n u j z)
  (G : (Key.share s Q).Geo P k) {a : Atlas P.Occupied P.grid.Seam S.m d S.h} (π : Palette a w q)
  (old : P.V ↪ B S.m) (data : U.rows.obj) (status : (Children.Header S.m d).obj)

namespace Physical
variable {U G π old data status} (B : U.Physical G π old data status)
  (p : Layout.Profile s.scene.cell s.scene.level)

local notation "Lyt" => G.layout U.dyadic U.large p j

theorem retains
    {record : U.engine.scheme.format.obj}
    {names : Names _ U.lane U.engine.d}
    (H : Frame U.engine record names ((Lyt).routed (B.rules.script p j) u) u)
    (hv : H.vertex = B.vertex p)
    {r₀ : S.format.obj} (portal : S.Presentation r₀ P.diagram)
    (keeps : Keeps Q B.rules.left B.rules.right portal a.coord) :
    Payload.Retains portal H.presentation U.split U.outer := by
  intro e
  obtain ⟨i, hloc, hleft, hright⟩ := keeps e
  let v : Node (Key.share s Q).Position (Sharing.radius k * n) := .inl (.inl (.inl i))
  have addr := B.address p v
  change U.split (B.vertex p v).1 = ((a.coord i.1).1, _) ∧ (B.vertex p v).2.1 = (a.coord i.1).2 at addr
  rw [hloc] at addr
  refine ⟨v, ?_, ?_, ?_, ?_, ?_⟩
  · rw [H.vertex_eq, hv, addr.1]
  · rw [H.vertex_eq, hv, addr.2]
  · exact Fin.eq_zero _
  · exact H.exterior_left v _ hleft
  · exact H.exterior_right v _ hright

end Physical
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! # A printed record displays its weighted local term -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer

open Coloring Assembly Rounds Surface Surface.Local
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Alphabet Key Node Sharing)
open scoped Classical

variable {F K N X Z : Type} [Field F] [Finite K] {x y : Wire} {m d h ℓ M r t q D k n u j z : ℕ}
  {T R g w : ℕ} {W : ℝ} {P : Input F x y h D T R g W}
  {Y : Alphabet P.Occupied} {s : Stage F (M * r) (M * t) Z P.Occupied P.grid.Seam X}
  {Q : Key.Source Y x y s} (U : Printer F K N m d h ℓ M r t q D k n u j z)
  (G : (Key.share s Q).Geo P k) {a : Atlas P.Occupied P.grid.Seam m d h} (π : Palette a w q)
  (old : P.V ↪ B m) (data : U.rows.obj) (status : (Children.Header m d).obj)

namespace Physical
variable {U G π old data status} (B : U.Physical G π old data status)
  (p : Layout.Profile s.scene.cell s.scene.level)

local notation "S" => Key.share s Q
local notation "H" => G.layout U.dyadic U.large p j
local notation "V" => Node (Sharing.Position S) (Sharing.radius k * n)
local notation "A" => U.template
local notation "rows" => B.record p
local notation "node" => (B.term p)
local notation "tree" => (G.tree U.dyadic U.large)
local notation "graph" => Children.graph U.slot U.dyadic U.large U.chunks U.degree (a.graph, status)

variable (hw : ∀ i, Diagram.padWidth u (((Key.share s Q).backdrop.emitted p j).width i) / u ≤ U.cap)

def shows : (A).Shows rows node where
  pres := (B.frame p hw).presentation
  host := B.host
  vertex v := by cases v <;> rfl
  directed := (B.frame p hw).directed
  uniform := by
    intro i
    apply (B.frame p hw).uniform
    rw [(B.frame p hw).presentation.wirePin_peer]
    rfl
  index := B.idx
  neighbor v z i l he := by
    refine ((B.frame p hw).neighbor v z i l he).trans ?_
    have hp (i : V) : (node).frame.place i = (H).place i := by cases i <;> rfl
    rw [hp, hp]
    rfl
  live i := by
    have ht := Children.live U.slot U.dyadic U.large U.chunks U.degree B.parents i
    rw [← B.record_header p] at ht
    exact ht
  frozen v := by
    have ht := Children.fixed_slot U.slot U.dyadic U.large U.chunks U.degree
      (old:=old) (u:=(a.graph, status)) v
    rw [← B.record_header p] at ht
    exact ht.trans (Children.fixed_iff U.dyadic U.large G v)
  closed v j := by
    have ht := Children.closed U.slot U.dyadic U.large U.chunks U.degree G B.parents B.steer v j
    rw [← B.record_header p] at ht
    exact ht
  reciprocal := by
    have ht := Children.reciprocal U.slot U.dyadic U.large U.chunks U.degree G B.parents B.steer
    rw [← B.record_header p] at ht
    exact ht
  edge v z := by
    have ht := Children.edge U.slot U.dyadic U.large U.chunks U.degree G B.parents B.steer v z
    rw [← B.record_header p] at ht
    exact ht
  core v z := by
    have ht := Children.core U.slot U.dyadic U.large U.chunks U.degree G B.parents B.steer v z
    rw [← B.record_header p] at ht
    exact ht
  charge := B.charge p
  amount := by
    refine U.amount (r':=rows) (B.frame p hw).presentation _ (B.charge p) (fun _ _ => rfl)
      ?_ (B.read_inactive p)
    intro v
    exact Option.isSome_iff_exists.mpr ⟨_, B.read_active p v⟩

end Physical
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! # Values and charges of the selected diagrams -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer

open Coloring Assembly Rounds Surface Surface.Local
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Alphabet Key Node Sharing)
open scoped Classical

variable {F K N X Z : Type} [Field F] [Finite K] {x y : Wire} {m d h ℓ M r t q D k n u j z : ℕ}
  {T R g w : ℕ} {W : ℝ} {P : Input F x y h D T R g W}
  {Y : Alphabet P.Occupied} {s : Stage F (M * r) (M * t) Z P.Occupied P.grid.Seam X}
  {Q : Key.Source Y x y s} (U : Printer F K N m d h ℓ M r t q D k n u j z)
  (G : (Key.share s Q).Geo P k) {a : Atlas P.Occupied P.grid.Seam m d h} (π : Palette a w q)
  (old : P.V ↪ B m) (data : U.rows.obj) (status : (Children.Header m d).obj)

namespace Physical
variable {U G π old data status} (B : U.Physical G π old data status)
  (p : Layout.Profile s.scene.cell s.scene.level)

local notation "S" => Key.share s Q
local notation "H" => G.layout U.dyadic U.large p j
local notation "V" => Node (Sharing.Position S) (Sharing.radius k * n)

open Finset

omit [Finite K] in
theorem populated (hn : Nonempty P.V) : Nonempty (B.term p).V := by
  obtain ⟨v⟩ := hn
  exact ⟨.inl (v, .inr (.inl false))⟩

omit [Finite K] in
theorem value (a : Val x) (b : Val y) :
    ∑ p ∈ @Finset.univ _ (Input.FinalBounds.profileType s.scene.cell s.scene.level), p.sign * (B.term p).diagram.eval a b = ∑ i, s.value j (Q.init a b i) := by
  have he := G.sum_output U.dyadic U.large (e := s.scene.level) j U.pos a b
  refine Eq.trans ?_ (he.trans ?_)
  · apply sum_congr rfl
    intro p _
    have h₀ := (G.layout U.dyadic U.large p j).eval_ordered (G.external U.dyadic U.large p j) U.pos (B.rules.script p j)
    have h₁ := (G.layout U.dyadic U.large p j).eval_finish (G.external U.dyadic U.large p j) U.pos
    exact congrArg (fun f => p.sign * f a b) (h₀.trans h₁.symm)
  · have ht := Key.sum_stack Y (M * t) s.hidden (Q.init a b) (s.scene.value j)
    refine Eq.trans ?_ (ht.trans ?_)
    · exact sum_congr (by ext; simp) (fun _ _ => rfl)
    · exact sum_congr (by ext; simp) (fun _ _ => rfl)

omit [Finite K] in
theorem concentrated {σ A : ℕ} (hc : Concentrated P (G.output U.dyadic U.large p j U.pos) A n σ) :
    Concentrated P (B.term p) A n σ :=
  ((H).pad u).drawn_concentrated (G.external U.dyadic U.large p j) _ _ P hc

end Physical
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end
