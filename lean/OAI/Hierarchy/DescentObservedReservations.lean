import OAI.Hierarchy.DescentCumulativeInputRows
import OAI.Hierarchy.DescentInstalledNames
import OAI.Hierarchy.DescentPaidTicketOrder

namespace OAI
/-! # Physical direct-link tickets from the populated pairs of good bases -/

namespace Hierarchy.DescentChosenRouter
open DescentGL DescentColonies DescentBaseProfile DescentRouterSlots
open scoped Classical BigOperators
noncomputable section
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I]
variable {k : ℕ}

/-- The old dyadic endpoint addresses and the reached key set are sufficient
to determine all paid links. Each pair is oriented from false to true. -/
structure Dyadic (V I : Type) [Fintype V] [DecidableEq V] [Fintype I] (k : ℕ) where
  b : V→ℕ
  hk : ∀v,b v≤k
  L : Layout k
  keys : Finset (V×ℕ)
  hub : V→Prop
  old : Bool→I→V×Block k
  bound : ℕ
  number : I ↪ Fin bound
  hostNumber : V↪ℕ

/-- Each physical paid ticket uses the input's true serial among the
previously observed bundles at the same ordered pair of bases. -/
structure Placement.OrderedTickets {H A : Type} [Fintype H] [Fintype A] {Y M : ℕ}
    (P : Placement V I H A k Y) (key : I↪Fin M) : Prop where
  serial : ∀p,(P.ticket p).2.val=(Finset.univ.filter (fun j=>
    key j.val<key p.val ∧
      ∀s,base P.b P.depth P.L P.keys P.hub P.old j s=base P.b P.depth P.L P.keys P.hub P.old p s)).card % P.span (P.ticket p).1
  pair_observed : Function.Surjective (fun p=>(P.ticket p).1)

instance {H A : Type} [Fintype H] [Fintype A] {Y M : ℕ} {P : Placement V I H A k Y} {key : I↪Fin M} :
    CoeFun (P.OrderedTickets key) (fun _=>∀p,(P.ticket p).2.val=(Finset.univ.filter (fun j=>
    key j.val<key p.val ∧
      ∀s,base P.b P.depth P.L P.keys P.hub P.old j s=base P.b P.depth P.L P.keys P.hub P.old p s)).card % P.span (P.ticket p).1) := ⟨Placement.OrderedTickets.serial⟩

namespace Dyadic
variable (D : Dyadic V I k)
abbrev G := Good D.b D.keys D.hub
abbrev Paid := {i // useRotor D.b D.hk D.L D.keys D.hub D.old i}
def endpoint (s : Bool) (p : D.Paid) : D.G := base D.b D.hk D.L D.keys D.hub D.old p s

def ordered (p : D.Paid) : D.G×D.G := (D.endpoint false p,D.endpoint true p)
abbrev Pairs := (Finset.univ.image D.ordered : Finset (D.G×D.G))
def edge (p : D.Paid) : D.Pairs := ⟨D.ordered p,Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩⟩
def endAt (s : Bool) (a : D.Pairs) : D.G := if s then a.val.2 else a.val.1
@[simp] theorem endAt_edge (s : Bool) (p : D.Paid) : D.endAt s (D.edge p)=D.endpoint s p := by
  cases s <;> rfl

abbrev Incident (s : Bool) (g : D.G) := {a : D.Pairs // D.endAt s a=g}
abbrev AtBase (s : Bool) (g : D.G) := {p : D.Paid // D.endAt s (D.edge p)=g}
abbrev OldAt (g : D.G) := {o : V×Block k // baseOf D.b D.hk D.L o=g.val}

def whole (s : Bool) (g : D.G) (p : D.AtBase s g) : D.OldAt g :=
  ⟨D.old s p.val.val,congrArg Subtype.val ((D.endAt_edge s p.val).symm.trans p.property)⟩

/-- The measured traffic inputs contain only original bundle multiplicities,
old tensor masses, shared contact capacities, and aggregate budgets. -/
structure Loads (Y : ℕ) (B S unit : ℝ) where
  weight : Bool→V×Block k→ℝ
  cap : D.Pairs→ℝ
  atom : ∀s o,0≤weight s o ∧ weight s o≤B
  full : ∀s (g : D.G),(∑o : D.OldAt g,weight s o.val)≤2*S
  carried : ∀s (g : D.G) (o : D.OldAt g),
    ((Finset.univ.filter (fun p : D.AtBase s g=>D.whole s g p=o)).card:ℝ)*unit≤weight s o.val
  amount : ∀a,(contactCounts D.edge a:ℝ)*unit≤cap a
  budget : ∀s (g : D.G),(∑a : D.Incident s g,cap a.val)≤2*S
  degree : ∀s (g : D.G),4*Fintype.card (D.Incident s g)≤Y

variable {Y : ℕ} [NeZero Y] {B S unit : ℝ} (L : D.Loads Y B S unit)
variable (pos : 0<S) (pu : 0<unit) (ub : unit≤B) (ys : (Y:ℝ)*B≤S)

def span (a : D.Pairs) := rowCount Y S (L.cap a)
include pos pu in
omit [NeZero Y] in
theorem room (s : Bool) (g : D.G) : (∑a : D.Incident s g,D.span L a.val)≤Y :=
  output_room (fun c : D.Incident s g => L.cap c.val) pos
    (fun c => (mul_nonneg (Nat.cast_nonneg _) pu.le).trans (L.amount c.val))
    (L.budget s g) (L.degree s g)

def paidNumber : D.Paid ↪ Fin D.bound := (Function.Embedding.subtype _).trans D.number

def ticket (p : D.Paid) : Reserve (D.span L) :=
  chooseOutput L.cap (contactCounts D.edge) pos pu L.amount (orderedIndex D.paidNumber D.edge p)

theorem ticket_read (p : D.Paid) :
    (D.ticket L pos pu p).2.val =
      (Finset.univ.filter (fun j : D.Paid=>D.number j.val<D.number p.val ∧ D.edge j=D.edge p)).card % D.span L (D.edge p) := by
  change (orderedIndex D.paidNumber D.edge p).2.val % D.span L (D.edge p)=_
  refine (congrArg (fun n => n % D.span L (D.edge p))
    (orderedIndex_read D.paidNumber D.edge p)).trans ?_
  apply congrArg (fun t : Finset D.Paid => t.card % D.span L (D.edge p))
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, paidNumber,
    Function.Embedding.trans_apply, Function.Embedding.subtype_apply]

theorem ticket_endpoint_read (p : D.Paid) :
    (D.ticket L pos pu p).2.val =
      (Finset.univ.filter (fun j : D.Paid=>D.number j.val<D.number p.val ∧
        ∀s,D.endpoint s j=D.endpoint s p)).card % D.span L (D.edge p) := by
  rw [D.ticket_read]
  apply congrArg (fun t : Finset D.Paid=>t.card % D.span L (D.edge p))
  ext j
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  apply and_congr_right
  intro _
  constructor
  · intro eqn s
    simpa only [endAt_edge] using congrArg (D.endAt s) eqn
  · intro eqn
    exact Subtype.ext (Prod.ext (eqn false) (eqn true))

theorem owned (p : D.Paid) (s : Bool) : D.endAt s (D.ticket L pos pu p).1=D.endpoint s p :=
  D.endAt_edge s p

def serial (s : Bool) (g : D.G) : D.AtBase s g ↪
    Σa : D.Incident s g,Fin (contactCounts D.edge a.val) :=
  sideIndex (D.endAt s) (orderedIndex D.paidNumber D.edge).toEmbedding g

def lastRow (s : Bool) (g : D.G) (p : D.AtBase s g) : Fin Y :=
  outputSlot _ (D.room L pos pu s g) (chooseOutput (fun a : D.Incident s g=>L.cap a.val)
    (fun a=>contactCounts D.edge a.val) pos pu (fun a=>L.amount a.val) (D.serial s g p))

/-- An old occupant within one dyadic base is identified completely by
its original block address. Its host position is fixed by the base. -/
def blockKey (g : D.G) : D.OldAt g ↪ Block k where
  toFun o := o.val.2
  inj' := by
    intro i j eq
    apply Subtype.ext
    exact Prod.ext ((congrArg Sigma.fst i.property).trans (congrArg Sigma.fst j.property).symm) eq

structure Allocation (s : Bool) (g : D.G) where
  choose : D.OldAt g→Fin Y
  choose_spec :
    (∀j,inputLoad Finset.univ (fun o : D.OldAt g=>L.weight s o.val) choose j≤3*S/Y) ∧
    (∀i,(∑j,(matrixOfBundles (choose ∘ D.whole s g) (D.lastRow L pos pu s g) i j:ℝ))≤9*S/(Y*unit)) ∧
    (∀j,(∑i,(matrixOfBundles (choose ∘ D.whole s g) (D.lastRow L pos pu s g) i j:ℝ))≤9*S/(Y*unit))

include ub ys in
private theorem assigned_matrix (s : Bool) (g : D.G) (rows : D.OldAt g → Fin Y)
    (load : ∀ j, inputLoad Finset.univ (fun o : D.OldAt g => L.weight s o.val) rows j ≤ 3*S/Y) :
    (∀ i, (∑ j, (matrixOfBundles (rows ∘ D.whole s g) (D.lastRow L pos pu s g) i j : ℝ)) ≤ 9*S/(Y*unit)) ∧
    (∀ j, (∑ i, (matrixOfBundles (rows ∘ D.whole s g) (D.lastRow L pos pu s g) i j : ℝ)) ≤ 9*S/(Y*unit)) := by
  have bounds := good_base_matrix_raw_of_rows (E:=D.AtBase s g) (I:=D.OldAt g) (C:=D.Incident s g)
    (Y:=Y) (B:=B) (S:=S) (u:=unit) (fun a => L.cap a.val) (fun a => contactCounts D.edge a.val)
    (fun o => L.weight s o.val) (D.whole s g) (D.serial s g) pos pu ub ys (fun o => L.atom s o.val)
    (L.full s g) (fun a => L.amount a.val) (L.budget s g) (L.degree s g) (fun o => by
      refine (congrArg (fun f : Finset (D.AtBase s g) => (f.card : ℝ)*unit) ?_).le.trans (L.carried s g o)
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]) rows load
  dsimp only [lastRow, Function.comp_def] at bounds ⊢
  exact bounds

include ub ys in
def assignment (s : Bool) (g : D.G) : Allocation D L pos pu s g :=
  let mass (o : D.OldAt g) := L.weight s o.val
  let rows : D.OldAt g → Fin Y := Cumulative.row (D.blockKey g) mass S
  have load : ∀ j, inputLoad Finset.univ mass rows j ≤ 3*S/Y :=
    Cumulative.bound (Y:=Y) (D.blockKey g) mass S B pos.le (fun o => (L.atom s o.val).1)
      (fun o => (L.atom s o.val).2) (L.full s g) ys
  { choose := rows, choose_spec := ⟨load, D.assigned_matrix L pos pu ub ys s g rows load⟩ }

def row (s : Bool) (o : V×Block k) : Fin Y :=
  if good : baseOf D.b D.hk D.L o∉validBases D.b D.keys ∧ ¬D.hub o.1 then
    (D.assignment L pos pu ub ys s ⟨baseOf D.b D.hk D.L o,good⟩).choose ⟨o,rfl⟩
  else 0

theorem row_whole (s : Bool) (g : D.G) (o : D.OldAt g) :
    D.row L pos pu ub ys s o.val=(D.assignment L pos pu ub ys s g).choose o := by
  rcases o with ⟨o,ho⟩
  rcases g with ⟨g,good⟩
  change baseOf D.b D.hk D.L o = g at ho
  subst g
  exact dite_eq_left good

theorem row_at (s : Bool) (g : D.G) (p : D.AtBase s g) :
    D.row L pos pu ub ys s (D.old s p.val.val)=
      (D.assignment L pos pu ub ys s g).choose (D.whole s g p) :=
  D.row_whole L pos pu ub ys s g (D.whole s g p)

theorem whole_input_bound (s : Bool) (g : D.G) (j : Fin Y) :
    inputLoad Finset.univ (fun o : D.OldAt g=>L.weight s o.val)
      (fun o=>D.row L pos pu ub ys s o.val) j≤3*S/Y := by
  simpa only [D.row_whole L pos pu ub ys s g] using!
    (D.assignment L pos pu ub ys s g).choose_spec.1 j

theorem row_side (same : ∀o,L.weight true o=L.weight false o) (o : V×Block k) :
    D.row L pos pu ub ys true o = D.row L pos pu ub ys false o := by
  unfold row
  split <;> rename_i good
  · let g : D.G := ⟨baseOf D.b D.hk D.L o,good⟩
    let q : D.OldAt g := ⟨o,rfl⟩
    change Cumulative.row (Y:=Y) (D.blockKey g) (fun z : D.OldAt g=>L.weight true z.val) S q =
      Cumulative.row (Y:=Y) (D.blockKey g) (fun z : D.OldAt g=>L.weight false z.val) S q
    rw [show (fun z : D.OldAt g=>L.weight true z.val)=(fun z : D.OldAt g=>L.weight false z.val) from
      funext (fun z=>same z.val)]
  · rfl

variable {H : Type} [Fintype H] (fallback : Bool→V×Block k→H)
def install : Placement V I H D.Pairs k Y where
  b := D.b
  depth := D.hk
  L := D.L
  keys := D.keys
  hub := D.hub
  old := D.old
  row := D.row L pos pu ub ys
  fall := fallback
  ends := D.endAt
  span := D.span L
  room := D.room L pos pu
  ticket := D.ticket L pos pu
  owned := D.owned L pos pu

/-- A reserved slot can be empty, while its ordered pair is always witnessed by an old paid grain. -/
theorem ticket_pair_surjective : Function.Surjective (fun p=>(D.ticket L pos pu p).1) := by
  intro a
  obtain ⟨p,_,ends⟩:=Finset.mem_image.mp a.property
  exact ⟨p,Subtype.ext ends⟩

theorem installed_tickets : (D.install L pos pu ub ys fallback).OrderedTickets D.number :=
  ⟨fun p=>D.ticket_endpoint_read L pos pu p,D.ticket_pair_surjective L pos pu⟩

end Dyadic
end
end Hierarchy.DescentChosenRouter

end OAI
