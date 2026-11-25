import OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Shows
import OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry.Boundary
import OAI.LinearAlgebra.MatrixExponent.Sphere.Panel.Terminal
import OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Children.Correct
import OAI.LinearAlgebra.MatrixExponent.Assembly.Boundary

/-! # Locating an exterior collector by its original station name -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print
open Coloring Assembly Rounds Surface Surface.Local
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Alphabet Key Place)
open scoped Classical

variable {F K N X Z J I : Type} [Field F] {x y : Wire} {S : Scheme F}
    {m d h ℓ M r t q D k n u j z T R g r₀ t₀ : ℕ} {W : ℝ}
    {P : Input F x y S.h D T R g W} {Y : Alphabet P.Occupied}
    {s : Stage F r₀ t₀ Z P.Occupied P.grid.Seam X}
    {β : P.Occupied ⊕ ℕ → K} {R₀ : Reference J I (B S.k) P.Occupied P.grid.Seam Z X}
    {G : Record F r₀ t₀ P.Occupied P.grid.Seam K (B S.k)} {tape : S.format.obj}

def NamedKeeps (Q : Key.Source Y x y s) (left : Order.Exterior Q.left) (right : Order.Exterior Q.right)
    (hm : Matches R₀.world β s G) (p : S.Presentation tape P.diagram)
    (loc : P.Occupied ↪ B S.m × B S.h) : Prop :=
  ∀ e : slots x ⊕ slots y, let v := Packing.portEnd P.diagram e
    ∃ i : Place s.scene.cell, loc i.1 = ((p.vertex v).1, (p.vertex v).2.1) ∧
      left.ports i = P.diagram.extLeft v ∧ right.ports i = P.diagram.extRight v ∧
      (hm.row i).name = some (p.vertex v).2.2 ∧
      ∀ l, l.1 = i.1 → (hm.row l).name = (hm.row i).name → l = i

theorem NamedKeeps.keeps {Q : Key.Source Y x y s} {left : Order.Exterior Q.left} {right : Order.Exterior Q.right}
    {hm : Matches R₀.world β s G} {p : S.Presentation tape P.diagram}
    {loc : P.Occupied ↪ B S.m × B S.h} (hp : NamedKeeps Q left right hm p loc) :
    Keeps Q left right p loc := by
  intro e
  obtain ⟨i, hl, h₁, h₂, _⟩ := hp e
  exact ⟨i, hl, h₁, h₂⟩

namespace Printer
variable (U : Printer F K N m d h ℓ M r t q D k n u j z)

def namesAt (x : B ℓ) :=
  (U.menu x).elim [] (fun c => c.tile.rows.map Entry.name)

def namedIndex (names : List (Option N)) (name : N) : ℕ :=
  if h : ∃ i : Fin names.length, names.get i = some name then h.choose.val else 0

def childFor (x : B ℓ) (name : N) : B U.childBits :=
  U.slot (.inl (.inl (true, ⟨namedIndex (U.namesAt x) name % D ^ k, Nat.mod_lt _ U.positive⟩)))

variable [Finite K] (V : Printer F K (B S.k) S.m d S.h ℓ M r t q D k n u j z)
  (pres : S.Presentation tape P.diagram) (data : V.rows.obj) (status : (Children.Header S.m d).obj)
  (f : Val x → Val y → F) (σ : ℕ)

structure NamedRelease extends V.Release pres data status f σ where
  nonzero : ∀ i, coeff i ≠ 0
  named : ∀ i e, let v := (pres.boundary e).val.1.1
    (V.split (((shows i).pres.boundary e).val.1.1.1)).2 = V.childFor ((data v.1).2 v.2.1) v.2.2

end Printer
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print
end

/-!
# Decoding proposed geometry and terminal coefficients

Each address carries the original label, the printer window and one
bounded outline. Port widths and peer addresses read only the original
exterior lengths and the outline.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry
open Coloring Assembly
open scoped Classical

variable {F : Type} [One F] {d e k : ℕ} (a : Outline d e k) (u : ℕ)
    (outer : Bool ↪ B e) (size : Option (B k) → Bool → ℕ) (x : Pattern F d 0 e)

def Outline.revise : Pattern F d 0 e where
  width _ := a.width u outer size
  peer _ := a.peer
  direction _ := a.direction
  value _ v := if h : a.live = true ∧ a.width u outer size = x.width 0 then
    x.value 0 (fun j i => v j (Fin.cast (congrFun h.2.symm j) i)) else 1

theorem Outline.revise_eq (h : a.Matches u outer size x) (hu : a.live = false → ∀ t, x.value 0 t = 1) :
    a.revise u outer size x = x := by
  obtain ⟨w, o, p, v⟩ := x
  have he (f : B 0 → B e → ℕ) : f = fun _ => f 0 :=
    funext fun i => congrArg f (Fin.eq_zero i)
  have ew : w = fun _ => a.width u outer size := (he w).trans (congrArg (fun g _ => g) h.width.symm)
  have ed : o = fun _ => a.direction := funext fun i => by rw [Fin.eq_zero i]; exact h.direction.symm
  have ep : p = fun _ => a.peer := funext fun i => by rw [Fin.eq_zero i]; exact h.peer.symm
  subst w o p
  unfold revise
  congr 1
  funext i t
  rw [Fin.eq_zero i]
  by_cases hl : a.live = true
  · simp [hl]
  · simpa [hl] using (hu (Bool.eq_false_iff.mpr hl) t).symm

end OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Coloring Assembly Geometry
open scoped Classical

variable {F K : Type} [Field F] [Finite K] (S : Scheme F)
    {d ℓ M r t q D k n u j z : ℕ} (U : Printer F K (B S.k) S.m d S.h ℓ M r t q D k n u j z)

abbrev Outline := Geometry.Outline (Children.degree d U.childBits) U.spanBits S.k
abbrev Blueprint := B U.childBits → U.Outline S
abbrev planBits := indexBits (U.Outline S)
abbrev addressBits := S.ℓ + (U.labelBits + U.planBits S)
abbrev Ticket := B S.ℓ × B U.labelBits × U.Outline S

def ticket : U.Ticket S ↪ B (U.addressBits S) :=
  ((Function.Embedding.refl _).prodMap
    (((Function.Embedding.refl _).prodMap (indexCode (U.Outline S))).trans
      (Match.rowIndex _ _).symm.toEmbedding)).trans (Match.rowIndex _ _).symm.toEmbedding

def decodeTicket (i : U.Ticket S) :=
  i.2.2.revise u U.outer (S.extWidth i.1) (U.engine.decode i.2.1)

def chargeTicket (i : U.Ticket S) : ℝ :=
  if i.2.2.live then (∑ s, i.2.2.width u U.outer (S.extWidth i.1) s : ℕ) + (u : ℝ) else 0

abbrev revised : Assembly.Template F where
  scheme := {U.engine.scheme with
    ℓ := U.addressBits S
    decode := Function.extend (U.ticket S) (U.decodeTicket S) (fun _ => Star.vacant)}
  count := U.addressBits S
  load := Function.extend (U.ticket S) (U.chargeTicket S) (fun _ => 0)
  park _ := 0
  past _ := 0
  order := Equiv.refl _

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! # The child carrying each individual exterior wire -/

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
variable (hw : ∀ i, Diagram.padWidth u (((Key.share s Q).backdrop.emitted p j).width i) / u ≤ U.cap)

theorem boundary_child (e : slots x ⊕ slots y) (i : Layout.Place s.scene.cell)
    (he : Sum.elim Q.left Q.right e = i) :
    (U.split ((B.shows p hw).pres.boundary e).val.1.1.1).2 =
      U.slot (.inl (.inl (true, Fin.castLE (G.count i.1) i.2))) := by
  let v : V := .inl (.inl (.inl i))
  have hf : G.frozen i := by
    rw [← he]; cases e with
    | inl e => exact G.left e
    | inr e => exact G.right e
  have hp : Packing.portEnd (B.term p).diagram e = v := by
    refine (((H).routed (B.rules.script p j) u).drawing.exterior e).trans ?_
    rw [show v = .inl (.inl (.inl (Sum.elim Q.left Q.right e))) by rw [he]]
    cases e <;> rfl
  rw [Payload.owner, hp]
  change (U.split (B.vertex p v).1).2 = _
  rw [(B.address p v).1]
  change U.slot (.inl (.inl (decide (G.frozen i), _))) = _
  rw [decide_eq_true hf]

end Physical
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! # The host certificate is shared by all geometry choices -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Coloring Assembly
open scoped Classical
variable {F K : Type} [Field F] [Finite K] (S : Scheme F)
    {d ℓ M r t q D k n u j z : ℕ} (U : Printer F K (B S.k) S.m d S.h ℓ M r t q D k n u j z)
    (y : U.template.format.obj)

local notation "L" => U.template

structure Graph (V : Type) where
  host : V ↪ B (L).scheme.m
  adj : V → Finset V
  frozen : V → Prop
  index : V → V → B (L).scheme.d
  sym : ∀ v w, w ∈ adj v → v ∈ adj w
  separate : ∀ v w, w ∈ adj v → ¬(frozen v ∧ frozen w)
  live : ∀ i, (L).live y i = true ↔ i ∈ Set.range host
  fixed : ∀ v, (L).frozen y (host v) = true ↔ frozen v
  closed : ∀ v j, (L).nav y (host v) j ∈ Set.range host
  reciprocal : Fmt.Reciprocal (.vec (L).scheme.h (.addr (L).scheme.ℓ)) y.1
  edge : ∀ v w, w ∈ adj v ↔ ∃ j, (L).nav y (host v) j = host w ∧ ((L).flags y (host v) j).1 = true
  core : ∀ v w, (w ∈ adj v ∧ ¬frozen v ∧ ¬frozen w) ↔
    ∃ j, (L).nav y (host v) j = host w ∧ ((L).flags y (host v) j).2 = true
  indexed : ∀ v w j, (L).nav y (host v) j = host w → ((L).flags y (host v) j).1 = true → j = index v w

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-!
# A profile-independent trie host

The trie uses only the parent contacts, the steering columns and
the common slot shapes. An empty seam list with one placeholder
at each parent suffices to apply the geometric routing lemmas.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Assembly Coloring Rounds
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Alphabet Sharing Trie)
open scoped Classical
variable {F K : Type} [Field F] [Finite K] {S : Scheme F}
  {d ℓ M r t q D k n u j z T R g : ℕ} {x y : Wire} {W : ℝ} {P : Input F x y S.h D T R g W}
  (U : Printer F K (B S.k) S.m d S.h ℓ M r t q D k n u j z)
  {old : P.V ↪ B S.m} {data : U.rows.obj} {status : (Children.Header S.m d).obj}
  {nav : B S.m → B d → B S.m} (A : Children.Shows P.adj old (nav, status))
  (hdata : ∀ i, (data i).1 = nav i) (hg : g ≤ D ^ k) (c : U.selectors.obj)

private def blank : Alphabet Empty where
  state _ := Unit
  width _ := 0
  code i := i.elim

private def places (M : ℕ) (P : Input F x y S.h D T R g W) :
    P.V → Surface.Cell F (M * 0) (M * 0) Unit Empty Unit :=
  fun _ => ⟨[], [⟨0, 0, 0, (), fun _ _ _ => 1⟩]⟩

private def site (M : ℕ) (P : Input F x y S.h D T R g W) : Sharing (places M P) x y blank where
  src i := i.elim
  dst i := i.elim
  meets _ i := i.1.elim
  seen _ := ∅
  reads _ := ∅
  within _ := Finset.Subset.rfl
  present i := i.elim
  connected i := i.elim
  left i := ⟨(P.place (Packing.portEnd P.diagram (.inl i))).1, ⟨0, by simp [places]⟩⟩
  right i := ⟨(P.place (Packing.portEnd P.diagram (.inr i))).1, ⟨0, by simp [places]⟩⟩
  param _ _ _ := ()
  locality _ _ _ _ _ _ _ _ _ _ := rfl

private def layout : (site M P).Geo P k where
  site := ⟨fun i => (i, 0), fun _ _ e => congrArg Prod.fst e⟩
  near i := i.elim
  count _ := U.positive
  chunks := U.chunks
  degree := hg
  frozen _ := True
  left _ := trivial
  right _ := trivial
  steer := A.steer U.degree

abbrev graphTree : Trie (Bench P.V M D k) (Sharing.radius k * n) :=
  (layout U A hg).tree U.dyadic U.large

local notation "net" => Children.graph U.slot U.dyadic U.large U.chunks U.degree (nav, status)
local notation "tree" => graphTree U A hg
local notation "N" => U.template
local notation "rows" => U.advance data status c
local notation "H" => Host P.V M D k n

include hdata in
private theorem header :
    ((N).nav rows, fun i => (((N).live rows i, (N).frozen rows i), (N).flags rows i)) = net := by
  change Children.graph _ _ _ _ _ (Children.tape (U.update data status c)) = _
  have eq : Children.tape (U.update data status c) = (nav, status) := Prod.ext (funext hdata) rfl
  rw [eq]

local notation "L" => (layout U A hg)
local notation "addr" => Children.host old U.slot
local notation "idx" => Children.idx old U.slot nav

include A hg in
omit [Finite K] in
private theorem indexed (v w : H) (i : B (Children.degree d U.childBits))
    (he : (net).1 (addr v) i = addr w) (hf : (((net).2 (addr v)).2 i).1 = true) :
    i = idx v w := by
  have h : Children.used U.slot U.dyadic U.large U.chunks U.degree (u:=(nav, status)) (addr v) i := by
    by_contra hn
    rw [(Children.spare U.slot U.dyadic U.large U.chunks U.degree _ _ hn).2] at hf
    cases hf
  obtain ⟨z, hz, rfl⟩ := (Children.columns U.slot U.dyadic U.large U.chunks U.degree L A rfl v i).mp h
  have h' := (Children.used_column U.slot U.dyadic U.large U.chunks U.degree L A rfl v z hz).1
  exact congrArg (idx v) ((addr).injective (h'.symm.trans he))

def graph : Graph S U rows H where
  host := addr
  adj := (tree).adj
  frozen := (tree).fixed
  index := idx
  sym _ _ := (tree).adj_symm
  separate _ _ := (tree).separate
  live i := by
    have he := Children.live U.slot U.dyadic U.large U.chunks U.degree A i
    rw [← header U hdata c] at he
    exact he
  fixed v := by
    have he := Children.fixed_slot U.slot U.dyadic U.large U.chunks U.degree
      (old:=old) (u:=(nav, status)) v
    rw [← header U hdata c] at he
    exact he.trans (Children.fixed_iff U.dyadic U.large L v)
  closed v j := by
    have he := Children.closed U.slot U.dyadic U.large U.chunks U.degree L A rfl v j
    rw [← header U hdata c] at he
    exact he
  reciprocal := by
    have he := Children.reciprocal U.slot U.dyadic U.large U.chunks U.degree L A rfl
    rw [← header U hdata c] at he
    exact he
  edge v w := by
    have he := Children.edge U.slot U.dyadic U.large U.chunks U.degree L A rfl v w
    rw [← header U hdata c] at he
    exact he
  core v w := by
    have he := Children.core U.slot U.dyadic U.large U.chunks U.degree L A rfl v w
    rw [← header U hdata c] at he
    exact Finset.mem_filter.symm.trans he
  indexed v w i := by
    have he := indexed U A hg v w i
    rw [← header U hdata c] at he
    exact he

variable {σ : ℕ} (hk : k = Sharing.allocation g σ)

include U A hg hk in
omit [Finite K] in
theorem graph_cells : Fintype.card H ≤ D ^ (Input.terminalExponent g σ) * Fintype.card P.V := by
  have hi := (L).host_count U.large
  have hb := (Layout.Fanout.host_bound (c:=Sharing.radius k) (ℓ:=σ)
    (C:=Input.terminalExponent g σ) U.dyadic U.large (by rw [hk]; rfl)).1
  unfold Host
  rw [Layout.node_count]
  exact (Nat.mul_le_mul_left _ hi).trans (by rw [← mul_assoc]; exact Nat.mul_le_mul_right _ hb)

local notation "Q" => (graph U A hdata hg c)

include hk in
theorem graph_fullDegree (v : H) : ((Q).adj v).card ≤ D ^ (Input.terminalExponent g σ) :=
  ((tree).degree v).trans (Layout.Fanout.host_bound (ℓ:=σ) U.dyadic U.large (by rw [hk]; rfl)).2.2

theorem graph_coreDegree (v : H) :
    (((Q).adj v).filter (fun w => ¬(Q).frozen v ∧ ¬(Q).frozen w)).card ≤ 3 :=
  (tree).core_degree v

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! # Reading the index of a unique name in a local record -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Surface Surface.Local Coloring
open scoped Classical

variable {F K N X Z J I V E : Type} {r t : ℕ} {β : V ⊕ ℕ → K}
    {R₀ : Reference J I N V E Z X} {G : Record F r t V E K N}
    {s : Stage F r t Z V E X} (hm : Matches R₀.world β s G)

theorem named_index (i : Layout.Place s.scene.cell) (n : N) (hn : (hm.row i).name = some n)
    (hu : ∀ l, l.1 = i.1 → (hm.row l).name = (hm.row i).name → l = i) :
    namedIndex ((G.rows i.1).map Entry.name) n = i.2.val := by
  let names := (G.rows i.1).map Entry.name
  have len : names.length = (s.scene.cell i.1).stations.length :=
    (List.length_map ..).trans (hm.rows i.1).length_eq.symm
  have he (j : Fin names.length) : names.get j = (hm.row ⟨i.1, Fin.cast len j⟩).name := by
    simp only [names, List.get_eq_getElem, List.getElem_map, Matches.row, Fin.val_cast]
  have hex : ∃ j : Fin names.length, names.get j = some n := by
    exact ⟨Fin.cast len.symm i.2, (he _).trans hn⟩
  change namedIndex names n = _
  rw [namedIndex, dite_eq_left hex]
  exact congrArg (fun l : Layout.Place s.scene.cell => l.2.val)
    (hu ⟨i.1, Fin.cast len hex.choose⟩ rfl ((he _).symm.trans (hex.choose_spec.trans hn.symm)))

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! # Recording a short blueprint alongside each printed label -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Coloring Assembly
open scoped Classical
variable {F K : Type} [Field F] [Finite K] (S : Scheme F)
    {d ℓ M r t q D k n u j z : ℕ} (U : Printer F K (B S.k) S.m d S.h ℓ M r t q D k n u j z)

abbrev Matrix := B S.m → B S.h → U.Blueprint S
abbrev Actors := U.template.scheme.Vtx

def localAt (A : U.Matrix S) (v : U.Actors S) := A (U.split v.1).1 v.2.1 (U.split v.1).2
def originalAt (x : S.format.obj) (v : U.Actors S) := (x (U.split v.1).1).2 v.2.1
def printedAt (y : U.template.format.obj) (v : U.Actors S) := (y.1 v.1).2 v.2.1

def held (x : B S.ℓ) (i : B S.k) : Bool :=
  decide (∃ b, S.extWidth x (some i) b ≠ 0)

def nameOf (x : B S.ℓ) (data : B ℓ) (child : B U.childBits) : Option (B S.k) :=
  if h : ∃ i, held S x i = true ∧ U.childFor data i = child then some h.choose else none

def centerLabel (v : B U.labelBits) :=
  ((Surface.Local.Design.number U.window).symm ((Match.rowIndex U.window.width U.childBits) v).1 0 0).1

def original (x : B S.ℓ) (y : B U.labelBits) : U.Outline S :=
  Geometry.Outline.read (U.read y).isSome
    (U.nameOf S x (U.centerLabel S y) ((Match.rowIndex _ _) y).2) (U.engine.decode y)

def centerAt (i : B S.m) (t : B S.h) (c : B U.childBits) : U.Actors S :=
  (U.split.symm (i, c), t, 0)

variable (x : S.format.obj) (y : U.template.format.obj)

def canonical : U.Matrix S :=
  fun i t c => U.original S ((x i).2 t) (U.printedAt S y (U.centerAt S i t c))

def atTicket (A : U.Matrix S) (v : U.Actors S) : U.Ticket S :=
  (U.originalAt S x v, U.printedAt S y v, U.localAt S A v)

def overlay (A : U.Matrix S) : (U.revised S).format.obj :=
  let label i j := U.ticket S (U.atTicket S x y A (i, j, 0))
  (fun i => ((y.1 i).1, label i), fun i => ((y.2 i).1, (y.2 i).2.1, label i))

variable (A : U.Matrix S) (v : U.Actors S)

theorem pattern_overlay :
    (U.revised S).scheme.pattern (U.overlay S x y A).1 v = U.decodeTicket S (U.atTicket S x y A v) :=
  (U.ticket S).injective.extend_apply (U.decodeTicket S) (fun _ => Star.vacant) (U.atTicket S x y A v)

theorem load_overlay :
    (U.revised S).load ((U.revised S).counter (U.overlay S x y A) v.1 v.2.1) =
      U.chargeTicket S (U.atTicket S x y A v) :=
  (U.ticket S).injective.extend_apply (U.chargeTicket S) (fun _ => 0) (U.atTicket S x y A v)

theorem local_center (i t c) : U.localAt S A (U.centerAt S i t c) = A i t c := by
  simp only [localAt, centerAt, Equiv.apply_symm_apply]

theorem original_center (i t c) : U.originalAt S x (U.centerAt S i t c) = (x i).2 t := by
  simp only [originalAt, centerAt, Equiv.apply_symm_apply]

theorem local_canonical :
    U.localAt S (U.canonical S x y) v = U.original S (U.originalAt S x v) (U.printedAt S y v) := by
  simp only [localAt, canonical, originalAt, printedAt, centerAt, Prod.mk.eta, Equiv.symm_apply_apply]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! # Changing the label alphabet preserves equal patterns and their ordered contraction -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry
open Coloring Assembly
open scoped Classical

variable {F : Type} [Field F] {m h k d e : ℕ}

private abbrev Vertex (m h k : ℕ) := B m × B h × B k
private abbrev PinFromBoardEval (P : Vertex m h k → Pattern F d k e) :=
  Σ t : Vertex m h k × B e, Fin ((P t.1).width t.1.2.2 t.2)

/-- Spell the contraction in terms of the decoded patterns, ignoring the label alphabet. -/
private def contraction {I : Type} (P : Vertex m h k → Pattern F d k e)
    (nav : B m → B d → B m) (bd : I → PinFromBoardEval P) (input : I → Bool) : F :=
  let peer (t : Vertex m h k × B e) := ((P t.1).peer t.1.2.2 t.2).map
    fun z => ((nav t.1.1 z.1, t.1.2.1, z.2.1), z.2.2)
  ∑ a : PinFromBoardEval P → Bool, if (∀ i, a (bd i) = input i) ∧
      (∀ t s : PinFromBoardEval P, peer t.1 = some s.1 ∧ t.2.val = s.2.val → a t = a s)
    then ∏ v, (P v).value v.2.2 (fun i j => a ⟨(v, i), j⟩) else 0

private theorem presented {x y : Wire} {S : Scheme F} {r : S.format.obj}
    {G : Diagram F x y} (p : S.Presentation r G) (a : Val x) (b : Val y) :
    G.eval a b = contraction (S.pattern r) (fun i => (r i).1)
      (fun i => (p.boundary i).val) (Sum.elim (bits x a) (bits y b)) := by
  rw [← p.eval]
  have hc (z : S.Pin r → Bool) :
      (∀ t : S.exposed r, z t.val = p.exterior a b t) ↔
      ∀ i, z (p.boundary i).val = Sum.elim (bits x a) (bits y b) i := by
    constructor
    · intro h i
      exact (h _).trans (p.exterior_boundary a b i)
    · intro h q
      obtain ⟨i, rfl⟩ := p.boundary.surjective q
      exact (h i).trans (p.exterior_boundary a b i).symm
  simp only [Scheme.eval, Scheme.Agrees, hc, contraction, Scheme.Joins, Scheme.peer,
    Scheme.table, Scheme.port, Function.comp_apply]
  apply Finset.sum_congr rfl
  intro z _
  congr

private theorem invariant {I : Type} {P Q : Vertex m h k → Pattern F d k e}
    (nav : B m → B d → B m) (f : I → PinFromBoardEval P) (g : I → PinFromBoardEval Q) (input : I → Bool)
    (hp : P = Q) (hs : ∀ i, (f i).1 = (g i).1) (hi : ∀ i, (f i).2.val = (g i).2.val) :
    contraction P nav f input = contraction Q nav g input := by
  subst Q
  have he : f = g := by
    funext i
    refine Sigma.ext (hs i) ((Fin.heq_ext_iff ?_).mpr (hi i))
    rw [hs i]
  rw [he]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry

namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Coloring Assembly
variable {F K : Type} [Field F] [Finite K] (S : Scheme F)
    {d ℓ M r t q D k n u j z : ℕ} (U : Printer F K (B S.k) S.m d S.h ℓ M r t q D k n u j z)
    (x : S.format.obj) (y : U.template.format.obj) (A : U.Matrix S)
    {a b : Wire} {G G' : Diagram F a b}

theorem eval_overlay (p : U.template.scheme.Presentation y.1 G)
    (p' : (U.revised S).scheme.Presentation (U.overlay S x y A).1 G')
    (hp : ∀ v, U.template.scheme.pattern y.1 v =
      (U.revised S).scheme.pattern (U.overlay S x y A).1 v)
    (hs : ∀ i, (p.boundary i).val.1 = (p'.boundary i).val.1)
    (hi : ∀ i, (p.boundary i).val.2.val = (p'.boundary i).val.2.val) :
    G.eval = G'.eval := by
  funext c d
  rw [Geometry.presented p, Geometry.presented p']
  exact Geometry.invariant _ _ _ _ (funext hp) hs hi

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! # Matching outlines recover the original tables without changing a coefficient -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Coloring Assembly
open scoped Classical

variable {F K : Type} [Field F] [Finite K] (S : Scheme F)
    {d ℓ M r t q D k n u j z : ℕ} (U : Printer F K (B S.k) S.m d S.h ℓ M r t q D k n u j z)
    (x : S.format.obj) (y : U.template.format.obj)

theorem pattern_canonical (v : U.Actors S)
    (h : (U.localAt S (U.canonical S x y) v).Matches u U.outer (S.extWidth (U.originalAt S x v))
      (U.engine.decode (U.printedAt S y v))) :
    U.template.scheme.pattern y.1 v =
      (U.revised S).scheme.pattern (U.overlay S x y (U.canonical S x y)).1 v := by
  rw [U.pattern_overlay]
  symm
  apply Geometry.Outline.revise_eq _ _ _ _ _ h
  intro hh
  rw [U.local_canonical] at hh
  have he : U.read (U.printedAt S y v) = none := by
    cases hp : U.read (U.printedAt S y v) <;> simp [original, Geometry.Outline.read, hp] at hh ⊢
  have hd : U.engine.decode (U.printedAt S y v) = Star.vacant := by simp [engine, he]
  rw [hd]
  exact fun _ => rfl

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! # Distinct exterior holders have distinct child addresses -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer.Signal
open Coloring Assembly Rounds Surface Surface.Local
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Alphabet Key Place Sharing item)
open scoped Classical

variable {F K X Z J I : Type} [Field F] [Finite K] {x y : Wire} {S : Scheme F} {d ℓ M r t q D k n u j z : ℕ}
  {T b c g w σ r₀ t₀ : ℕ} {W : ℝ} {P : Input F x y S.h D T (c * b) g W}
  {Y : Alphabet P.Occupied} {s : Stage F (M * r) (M * t) Z P.Occupied P.grid.Seam X}
  {Q : Key.Source Y x y s} {left : Order.Exterior Q.left} {right : Order.Exterior Q.right}
  {U : Printer F K (B S.k) S.m d S.h ℓ M r t q D k n u j z}
  {a : Atlas P.Occupied P.grid.Seam S.m d S.h} {π : Palette a w q}
  {β : P.Occupied ⊕ ℕ → K} {R₀ : Reference J I (B S.k) P.Occupied P.grid.Seam Z X}
  {G : Record F (M * r) (M * t) P.Occupied P.grid.Seam K (B S.k)}
  {hm : Matches R₀.world β s G} {index : ∀ v, Y.state v ↪ ℕ} {size : P.Occupied → ℕ}
  {ext : P.Occupied → Option (B S.k) → Bool → ℕ} {old : P.V ↪ B S.m}
  {data : U.rows.obj} {status : (Children.Header S.m d).obj}
  (H : U.Signal Q left right a π β R₀ G hm index size ext old data status)

open SphereScale (Scales depth)

variable {tape : S.format.obj} {pres : S.Presentation tape P.diagram}

omit [Finite K] in
include H in
theorem injection (keeps : NamedKeeps Q left right hm pres a.coord) (hd : pres.Directed)
    (count : ∀ i, (s.scene.cell i).stations.length ≤ D ^ k) (v : B S.m) (w : B S.h) :
    Set.InjOn (U.childFor ((data v).2 w)) {i | held S ((tape v).2 w) i = true} := by
  have witness (i) (hi : held S ((tape v).2 w) i = true) :
      ∃ l : Place s.scene.cell, a.coord l.1 = (v, w) ∧ (hm.row l).name = some i ∧
        U.childFor ((data v).2 w) i = U.slot (.inl (.inl (true, Fin.castLE (count l.1) l.2))) := by
    obtain ⟨b, hb⟩ := of_decide_eq_true hi
    obtain ⟨e, he, _⟩ := (pres.extWidth_ne_zero hd (v, w, i) b).mp hb
    obtain ⟨l, hc, _, _, hn, hu⟩ := keeps e
    rw [Payload.owner] at he
    rw [he] at hc hn
    refine ⟨l, hc, hn, ?_⟩
    have hs := eq_of_heq (H.read (a.coord l.1))
    rw [Atlas.fill_at, hc] at hs
    have hx : namedIndex (U.namesAt ((data v).2 w)) i = l.2.val := by
      rw [namesAt, hs, Option.elim_some]
      exact named_index hm l i hn hu
    unfold childFor
    exact congrArg (fun j => U.slot (.inl (.inl (true, j))))
      (Fin.ext (by simp only [Fin.val_castLE, hx, Nat.mod_eq_of_lt (l.2.isLt.trans_le (count l.1))]))
  intro i hi j hj he
  obtain ⟨⟨p, x⟩, hp, hx, h⟩ := witness i hi
  obtain ⟨⟨l, y⟩, hl, hy, h'⟩ := witness j hj
  have eq : p = l := a.coord.injective (hp.trans hl.symm)
  subst l
  have eq := U.slot.injective (h.symm.trans (he.trans h'))
  have hu : x = y := Fin.castLE_injective (count p) (Prod.mk.inj (Sum.inl.inj (Sum.inl.inj eq))).2
  subst y
  exact Option.some.inj (hx.symm.trans hy)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer.Signal
end

/-!
# Checks using bounded local data

A register names each old exterior holder exactly once. Reciprocal
contacts use only short neighbor indices and one bit per reverse index.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry
open Coloring Assembly
open scoped Classical

variable {d e k w : ℕ}
structure Blueprint.Register (a : Blueprint w d e k) (outer : Bool ↪ B e)
    (eligible : B k → Bool) (live fixed : B w → Bool) : Prop where
  live : ∀ i, (a i).live = true → live i = true
  vacant : ∀ i, (a i).live = false → a i = Outline.empty
  cover : ∀ j, eligible j = true → ∃! i, (a i).name = some j
  named : ∀ i j, (a i).name = some j → eligible j = true ∧ fixed i = true ∧ (a i).live = true
  outer : ∀ i, (a i).name.isSome → ∀ b, (a i).peer (outer b) = none ∧ (a i).direction (outer b) = b

def Outline.Contact (a b : Outline d e k) (j : B d) (flag : Bool) (reverse : B d → Bool) : Prop :=
  ∀ i l, a.peer i = some (j, 0, l) → flag = true ∧ a.live = true ∧ b.live = true ∧
    a.direction i ≠ b.direction l ∧ ∃ t, reverse t = true ∧ b.peer l = some (t, 0, i)

def Blueprint.find (a : Blueprint w d e k) (name : B k) : B w :=
  if h : ∃ i, (a i).name = some name then h.choose else 0

theorem Blueprint.Register.find {a : Blueprint w d e k} {outer elig live fixed}
    (h : a.Register outer elig live fixed) {j i} (hi : (a i).name = some j) : a.find j = i := by
  obtain ⟨w, _, hu⟩ := h.cover j (h.named i j hi).1
  have he : ∃ i, (a i).name = some j := ⟨i, hi⟩
  rw [Blueprint.find, dite_eq_left he]
  exact (hu _ he.choose_spec).trans (hu _ hi).symm

end OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Coloring Assembly
open scoped Classical
variable {F K : Type} [Field F] [Finite K] (S : Scheme F)
    {d ℓ M r t q D k n u j z : ℕ} (U : Printer F K (B S.k) S.m d S.h ℓ M r t q D k n u j z)
    (x : S.format.obj) (y : U.template.format.obj) (A : U.Matrix S)

def childLive (i : B S.m) (c : B U.childBits) := U.template.live y (U.split.symm (i, c))
def childFixed (i : B S.m) (c : B U.childBits) := U.template.frozen y (U.split.symm (i, c))

def registered := ∀ i t, Geometry.Blueprint.Register (A i t) U.outer (held S ((x i).2 t))
  (U.childLive S y i) (U.childFixed S y i)

def linked := ∀ v b i,
  let w := U.template.nav y v i
  Geometry.Outline.Contact (U.localAt S A (v, b, 0)) (U.localAt S A (w, b, 0)) i
    (U.template.flags y v i).1 (fun j => decide (U.template.nav y w j = v))

def Valid := U.registered S x y A ∧ U.linked S y A

def destination (v : S.Vtx) : U.Actors S :=
  U.centerAt S v.1 v.2.1 (Geometry.Blueprint.find (A v.1 v.2.1) v.2.2)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! # Reciprocal local contacts give a proper global scheme -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Coloring Assembly
open scoped Classical

variable {F K : Type} [Field F] [Finite K] (S : Scheme F)
    {d ℓ M r t q D k n u j z : ℕ} (U : Printer F K (B S.k) S.m d S.h ℓ M r t q D k n u j z)
    (x : S.format.obj) (y : U.template.format.obj) (A : U.Matrix S)

local notation "T" => Template.scheme (U.revised S)
local notation "R" => Prod.fst (U.overlay S x y A)

theorem width_overlay (v : U.Actors S) (i : B U.spanBits) :
    (T).width R (v, i) = (U.localAt S A v).width u U.outer (S.extWidth (U.originalAt S x v)) i := by
  unfold Scheme.width
  rw [U.pattern_overlay]
  rfl

theorem direction_overlay (v : U.Actors S) (i : B U.spanBits) :
    (T).direction R (v, i) = (U.localAt S A v).direction i := by
  unfold Scheme.direction
  rw [U.pattern_overlay]
  rfl

theorem peer_overlay (v : U.Actors S) (i : B U.spanBits) :
    (T).peer R (v, i) = ((U.localAt S A v).peer i).map
      (fun a => ((U.template.nav y v.1 a.1, v.2.1, a.2.1), a.2.2)) := by
  unfold Scheme.peer
  rw [U.pattern_overlay]
  rfl

theorem overlay_link (hl : U.linked S y A) (v w : U.Actors S) (i l : B U.spanBits)
    (he : (T).peer R (v, i) = some (w, l)) :
    ∃ a, (U.localAt S A v).peer i = some (a, 0, l) ∧
      U.template.nav y v.1 a = w.1 ∧ (U.template.flags y v.1 a).1 = true ∧
      (T).peer R (w, l) = some (v, i) ∧ (T).width R (v, i) = u ∧ (T).width R (w, l) = u ∧
      (T).direction R (v, i) ≠ (T).direction R (w, l) := by
  rcases v with ⟨v, b, s⟩
  have hs : s = 0 := Fin.eq_zero s
  subst s
  rw [U.peer_overlay] at he
  obtain ⟨⟨a, c, j'⟩, hp, hw⟩ := Option.map_eq_some_iff.mp he
  have hc : c = 0 := Fin.eq_zero c
  subst c
  obtain ⟨hww, hh⟩ := Prod.mk.inj hw
  change j' = l at hh
  subst l
  change (U.template.nav y v a, b, 0) = w at hww
  subst w
  obtain ⟨hf, _, _, hd, e, he, hb⟩ := hl v b a i j' hp
  refine ⟨a, hp, rfl, hf, ?_, ?_, ?_, ?_⟩
  · rw [U.peer_overlay, hb, Option.map_some]
    exact congrArg (fun z => some ((z, b, 0), i)) (of_decide_eq_true he)
  · exact (U.width_overlay S x y A _ i).trans (ite_eq_left (Option.isSome_iff_exists.mpr ⟨_, hp⟩))
  · exact (U.width_overlay S x y A _ j').trans (ite_eq_left (Option.isSome_iff_exists.mpr ⟨_, hb⟩))
  · rw [U.direction_overlay, U.direction_overlay]
    exact hd

theorem overlay_proper (hl : U.linked S y A) : (T).Proper R := by
  rintro ⟨v, i⟩ ⟨w, l⟩ he
  obtain ⟨_, _, _, _, hr, hv, hw, hd⟩ := U.overlay_link S x y A hl v w i l he
  exact ⟨hr, hv.trans hw.symm, hd⟩

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! # A valid geometry overlay displays its realized local term -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Coloring Assembly
open scoped Classical

variable {F K : Type} [Field F] [Finite K] (S : Scheme F)
    {d ℓ M r t q D k n u j z : ℕ} (U : Printer F K (B S.k) S.m d S.h ℓ M r t q D k n u j z)
    (x : S.format.obj) (y : U.template.format.obj) (A : U.Matrix S) (hv : U.Valid S x y A)

local notation "T" => Template.scheme (U.revised S)
local notation "rows" => Prod.fst (U.overlay S x y A)

include hv in
private theorem registered_live (v : U.Actors S) (h : (U.localAt S A v).live = true) :
    U.template.live y v.1 = true := by
  have hh := (hv.1 (U.split v.1).1 v.2.1).live (U.split v.1).2 h
  simpa only [childLive, Prod.mk.eta, Equiv.symm_apply_apply] using hh

include hv in
private theorem registered_exterior (p : (T).exposed rows) :
    U.template.frozen y p.val.1.1.1 = true := by
  rcases p with ⟨⟨⟨v, i⟩, z⟩, hp⟩
  have hm : (U.localAt S A v).peer i = none := by
    exact Option.map_eq_none_iff.mp ((U.peer_overlay S x y A v i).symm.trans hp)
  have hn : (U.localAt S A v).name ≠ none := by
    intro he
    have ht : 0 < (T).width rows (v, i) := Nat.zero_lt_of_lt z.isLt
    have hh := (U.width_overlay S x y A v i) ▸ ht
    unfold Geometry.Outline.width at hh
    simp [hm, he, Scheme.extWidth] at hh
  obtain ⟨l, hl⟩ := Option.ne_none_iff_exists'.mp hn
  have hh := ((hv.1 (U.split v.1).1 v.2.1).named (U.split v.1).2 l hl).2.1
  simpa only [childFixed, Prod.mk.eta, Equiv.symm_apply_apply] using hh

variable {V : Type} [Fintype V] (H : U.Graph S y V) {a b : Wire}
  (R : (U.revised S).scheme.Realization (U.overlay S x y A).1 a b) (ha : ∀ v, R.active v ↔ (U.localAt S A v).live = true)

include hv ha in
omit [Fintype V] in
private theorem owner_exists (v : R.V) : ∃ w, H.host w = v.val.1 :=
  (H.live _).mp (U.registered_live S x y A hv _ ((ha _).mp v.property))

/-- The original graph is retained, while the outline supplies the diagram and counters. -/
abbrev board : Geometry.Board (U.revised S) (U.overlay S x y A) a b u where
  realization := R
  single := rfl
  V := V
  host := H.host
  adj := H.adj
  frozen := H.frozen
  index := H.index
  owner v := (U.owner_exists S x y A hv H R ha v).choose
  owns v := (U.owner_exists S x y A hv H R ha v).choose_spec
  sym := H.sym
  exterior := U.registered_exterior S x y A hv
  linked v w i l he _ := by
    obtain ⟨c, _, hn, hf, _, hw, _⟩ := U.overlay_link S x y A hv.2 _ _ _ _ he
    let ov := (U.owner_exists S x y A hv H R ha v)
    let ow := (U.owner_exists S x y A hv H R ha w)
    have had : ow.choose ∈ H.adj ov.choose := by
      apply (H.edge _ _).mpr
      rw [ov.choose_spec, ow.choose_spec]
      exact ⟨c, hn, hf⟩
    exact ⟨had, H.separate _ _ had, hw⟩
  neighbor v w i l he := by
    obtain ⟨c, hp, hn, hf, _⟩ := U.overlay_link S x y A hv.2 _ _ _ _ he
    let ov := (U.owner_exists S x y A hv H R ha v)
    let ow := (U.owner_exists S x y A hv H R ha w)
    have hi : c = H.index ov.choose ow.choose := by
      apply H.indexed
      · rwa [ov.choose_spec, ow.choose_spec]
      · rwa [ov.choose_spec]
    rw [U.pattern_overlay, ← hi]
    exact hp
  live := H.live
  fixed := H.fixed
  closed := H.closed
  reciprocal := H.reciprocal
  edge := H.edge
  core := H.core
  load i l := by
    rw [U.load_overlay S x y A (i, l, 0)]
    simp only [ha, chargeTicket, atTicket]
    exact congrArg (fun n : ℕ => if (U.localAt S A (i, l, 0)).live then (n : ℝ) + u else 0)
      (Finset.sum_congr rfl fun s _ => (U.width_overlay S x y A (i, l, 0) s).symm)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end
