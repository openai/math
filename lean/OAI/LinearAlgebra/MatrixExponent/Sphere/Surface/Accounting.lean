import OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Pull
import OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Ledger

/-! # A crossing in two adjacent cells -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface

open Finset Motion
open scoped Classical
variable {F T X Y E : Type} [Field F] {r t P : ℕ}

theorem Cell.test_mul_left (P : ℕ) (x : X) (c : Cell F r t T E X) (h : E → Wedge r)
    (k : F) (f : Test F r t) :
    c.test P x h (fun a b => k * f a b) = k * c.test P x h f :=
  batch_mul_left _ _ _ _ _

theorem Cell.test_mul_right (P : ℕ) (x : X) (c : Cell F r t T E X) (h : E → Wedge r)
    (k : F) (f : Test F r t) :
    c.test P x h (fun a b => f a b * k) = c.test P x h f * k :=
  batch_mul_right _ _ _ _ _

def Unused (i : E) (l : List (E × F)) : Prop := ∀ j ∈ l, j.1 ≠ i

theorem ends_update (i : E) (h : E → Wedge r) (v : Wedge r) (l : List (E × F)) (he : Unused i l) :
    ends P (Function.update h i v) l = ends P h l := by
  apply List.flatMap_congr
  intro j hj
  rw [Function.update_of_ne (he j hj)]

theorem Cell.eval_update (c : Cell F r t T E X) (x : X) (i : E) (h : E → Wedge r)
    (v : Wedge r) (he : Unused i c.ports) :
    c.eval P x (Function.update h i v) = c.eval P x h := by
  simp only [Cell.eval, ends_update _ _ _ _ he]

/-- A cell with one designated seam temporarily removed. -/
structure Socket (F : Type) (r t : ℕ) (T E X : Type) where
  before : List (E × F)
  after : List (E × F)
  stations : List (Station F r t T X)

namespace Socket

variable (v : Socket F r t T E X)

def base : Cell F r t T E X := ⟨v.before ++ v.after, v.stations⟩
def plug (i : E) (z : F) : Cell F r t T E X := ⟨v.before ++ (i, z) :: v.after, v.stations⟩

def sign (d : E → ℕ) (e m : ℕ) : F :=
  (-1) ^ ((m + sumA v.stations + portWeight d v.before) * e)

theorem plugged {e : ℕ} (x : X) (d : E → ℕ) (i : E) (z : F) (h : E → Wedge r)
    (hh : ∀ j, j ≠ i → energy (h j).val = d j) (hi : Unused i v.base.ports)
    (a : Level r e) (f : Test F r t) (hf : Signed f) :
    (v.plug i z).test P x (Function.update h i a.val) f =
      v.sign d e 0 * v.base.test P x h (lead (z ^ P) a.val f) := by
  change Unused i (v.before ++ v.after) at hi
  have hpre : Unused i v.before := fun j hj => hi j (List.mem_append_left _ hj)
  have eq := port_front P x v.stations (Function.update h i a.val) v.before v.after (i, z) f hf
  rw [ends_update _ _ _ _ hpre, ends_update _ _ _ _ hi, Function.update_self,
    a.property, weight_ends P d h v.before (fun j hj => hh _ (hpre j hj))] at eq
  simpa only [plug, sign, base, Cell.test, lead, zero_add, List.append_assoc] using eq

theorem plugged_insert {e : ℕ} (x : Y) (π : Y → X) (u : Station F r t T Y)
    (d : E → ℕ) (i : E) (z : F) (h : E → Wedge r)
    (hh : ∀ j, j ≠ i → energy (h j).val = d j) (hi : Unused i v.base.ports)
    (a : Level r e) (f : Test F r t) (hf : Signed f) :
    (((v.plug i z).pull π id).insert u).test P x (Function.update h i a.val) f =
      v.sign d e u.a * v.base.test P (π x) h (frontOne P x u (lead (z ^ P) a.val f)) := by
  let w : Socket F r t T E Y := ⟨v.before, v.after, u :: v.stations.map (Station.pull · π id)⟩
  have eq := w.plugged x d i z h hh hi a f hf (P := P)
  have es : w.sign d e 0 = v.sign d e u.a := by simp [sign, w, sumA, Station.pull, Function.comp_def]
  have eb : w.base = (v.base.pull π id).insert u := rfl
  rw [es, eb, Cell.test_insert, Cell.test_pull] at eq
  exact eq

end Socket
namespace Passage

variable {u : Station F r t T X} (s : Passage P u)
variable (v w : Cell F r t T E X) (d : E → ℕ)

structure Fits : Prop where
  near : v.Fixed P (s.A.erase (s.z ^ P)) s.B
  far : ∃ D, w.Fixed P (s.C.erase (s.y ^ P)) D
  a : v.bigA d = s.a
  b : sumB v.stations = s.b
  c : w.bigA d = s.c

private theorem advance_cells (p l : ℕ) [ExpChar F p] (hP : P = p ^ l) (hs : s.Fits v w d)
    (k k' : T) :
    let S := lowering F r
    let f := s.weights p l hP
    ∀ (x : X) (h : E → Wedge r),
      (∀ j ∈ v.ports, energy (h j.1).val = d j.1) → (∀ j ∈ w.ports, energy (h j.1).val = d j.1) →
      (∑ b : Level r s.e, v.test P x h (frontOne P x u (lead (s.z ^ P) b.val s.coeff)) *
        w.test P x h (lead (s.y ^ P) b.val forms)) =
        ∑ i : s.Branch, f i * ∑ y : Level t u.b, ∑ b : Level r i.height,
          v.test P x h (frontOne P (x, y) (s.leaves k i) (lead (s.z ^ P) b.val forms)) *
          w.test P x h (frontOne P (x, y) (s.arrives k' S i) (lead (s.y ^ P) b.val forms)) := by
  intro S f
  have hf := s.advance p l hP k k'
  obtain ⟨D, hD⟩ := hs.far
  intro x h hv hw
  have e := v.test_congr P x d h hv hs.near (fun a b ha hb wa wb =>
    w.test_congr P x d h hw hD (fun c d hc _ wc _ =>
      hf x a b c d ha hb hc (wa.trans hs.a) (wb.trans hs.b) (wc.trans hs.c)))
  simpa only [Cell.test_sum, Cell.test_mul_left, Cell.test_mul_right] using e

variable (L R : Socket F r t T E X) (j : E)

def left (k : T) (i : s.Branch) :=
  ((L.plug j s.z).pull Prod.fst id).insert (s.leaves k i)

def right (k : T) (S : Lower F r) (i : s.Branch) :=
  ((R.plug j s.y).pull Prod.fst id).insert (s.arrives k S i)

def signed (p l : ℕ) [ExpChar F p] (hP : P = p ^ l) (i : s.Branch) : F :=
  L.sign d s.e u.a * R.sign d s.e 0 * s.weights p l hP i /
    (L.sign d i.height 0 * R.sign d i.height i.2.2.1.val)

/-- Both endpoints keep their original seam order. The signs are
absorbed into the scalar weight of the branch. -/
theorem crossing (p l : ℕ) [ExpChar F p] (hP : P = p ^ l) (hs : s.Fits L.base R.base d)
    (hl : Unused j L.base.ports) (hr : Unused j R.base.ports) (k k' : T) :
    let S := lowering F r
    let f := s.signed d L R p l hP
    ∀ (x : X) (h : E → Wedge r),
      (∀ i, i ≠ j → energy (h i).val = d i) →
      (∑ a : Level r s.e,
        ((L.plug j s.z).insert u).test P x (Function.update h j a.val) s.coeff *
          (R.plug j s.y).eval P x (Function.update h j a.val)) =
        ∑ i : s.Branch, f i * ∑ y : Level t u.b, ∑ a : Level r i.height,
          (s.left L j k i).eval P (x, y) (Function.update h j a.val) *
          (s.right R j k' S i).eval P (x, y) (Function.update h j a.val) := by
  intro S coeff
  let f := s.weights p l hP
  have hf := s.advance_cells L.base R.base d p l hP hs k k'
  let c := L.sign d s.e u.a * R.sign d s.e 0
  let b (i : s.Branch) := L.sign d i.height (s.leaves k i).a * R.sign d i.height (s.arrives k' S i).a
  have hb (i) : b i ≠ 0 := by simp [b, Socket.sign]
  intro x h he
  rw [show coeff = (fun i => c * f i / b i) from rfl]
  have a (v : Level r s.e) :
      ((L.plug j s.z).insert u).test P x (Function.update h j v.val) s.coeff *
          (R.plug j s.y).eval P x (Function.update h j v.val) = c *
        (L.base.test P x h (frontOne P x u (lead (s.z ^ P) v.val s.coeff)) *
          R.base.test P x h (lead (s.y ^ P) v.val forms)) := by
    have hx := L.plugged_insert x id u d j s.z h he hl v s.coeff (coefficient_signed _ _ _ _ _) (P := P)
    rw [Cell.pull_id] at hx
    have hy := R.plugged x d j s.y h he hr v forms forms_signed (P := P)
    change _ * (R.plug j s.y).test P x _ forms = _
    rw [hx, hy, mul_mul_mul_comm]
    rfl
  have b' (i : s.Branch) (y : Level t u.b) (v : Level r i.height) :
      (s.left L j k i).eval P (x, y) (Function.update h j v.val) *
          (s.right R j k' S i).eval P (x, y) (Function.update h j v.val) = b i *
        (L.base.test P x h (frontOne P (x, y) (s.leaves k i) (lead (s.z ^ P) v.val forms)) *
          R.base.test P x h (frontOne P (x, y) (s.arrives k' S i) (lead (s.y ^ P) v.val forms))) := by
    have hx := L.plugged_insert (x, y) Prod.fst (s.leaves k i) d j s.z h he hl v forms forms_signed (P := P)
    have hy := R.plugged_insert (x, y) Prod.fst (s.arrives k' S i) d j s.y h he hr v forms forms_signed (P := P)
    change (s.left L j k i).test P (x, y) _ forms * (s.right R j k' S i).test P (x, y) _ forms = _
    rw [left, right, hx, hy, mul_mul_mul_comm]
  simp only [a, b', ← mul_sum]
  rw [hf x h (fun i hi => he _ (hl i hi)) (fun i hi => he _ (hr i hi)), mul_sum]
  exact sum_congr rfl fun i _ => by rw [← mul_assoc, ← mul_assoc, div_mul_cancel₀ _ (hb i)]

end Passage
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface
end

/-! # Exact local transformations inside a closed sewn surface -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface

open Finset Function Motion
open scoped Classical

structure Scene (F : Type) (r t : ℕ) (T V E X : Type) where
  cell : V → Cell F r t T E X
  level : E → ℕ

variable {F T V E X : Type} [Field F] [Fintype V] [Fintype E] {r t P : ℕ}

namespace Scene

variable (C : Scene F r t T V E X)

def value (P : ℕ) (x : X) : F := eval P C.cell C.level x

def observe (P : ℕ) (v : V) (f : Test F r t) (x : X) : F :=
  contractGraph (update (fun i => (C.cell i).eval P x) v (fun h => (C.cell v).test P x h f)) C.level

def put (v : V) (c : Cell F r t T E X) : Scene F r t T V E X := ⟨update C.cell v c, C.level⟩

theorem observe_forms (v : V) (x : X) : C.observe P v forms x = C.value P x := by
  unfold observe
  change contractGraph (update _ _ ((C.cell v).eval P x)) _ = _
  rw [update_eq_self]
  rfl

/-- Change the local contraction while leaving all shared levels fixed. -/
theorem replace {I : Type} [Fintype I] (v : V) (f : Test F r t)
    (w : I → F) (c : I → Cell F r t T E X) (g : I → Test F r t)
    (h : ∀ (x : X) (a : E → Wedge r), (∀ e, energy (a e).val = C.level e) →
      (C.cell v).test P x a f = ∑ i, w i * (c i).test P x a (g i)) (x : X) :
    C.observe P v f x = ∑ i, w i * (C.put v (c i)).observe P v (g i) x := by
  unfold observe
  rw [contractGraph_replace _ _ v w (fun i a => (c i).test P x a (g i)) (by simpa using h x)]
  refine sum_congr rfl fun i _ => congrArg (w i * ·) ?_
  unfold put
  simp only [update_self, update_idem]
  congr 1
  funext y
  by_cases hy : y = v
  · subst y; simp
  · simp [hy]

/-- Interpolate a cell simultaneously for all exterior assignments. -/
theorem reconstruct (p l : ℕ) [ExpChar F p] (v : V)
    (S B seams : Finset F) (hB : B ⊆ S) (hs : seams ⊆ S) (collector : F)
    (hc : collector ∈ S) (hc' : collector ∉ seams) (g L : ℕ) (hg : seams.card ≤ g)
    (z : F) (hz : z ∉ S) (st : ∀ a ∈ (C.cell v).stations, a.pos = z ∨ a.pos ∈ B)
    (pt : ∀ i ∈ (C.cell v).ports, i.2 ∈ S) :
    let P := p ^ l
    let D := poleOrder P ((C.cell v).orderA C.level) (C.cell v).orderB B
    ∃ w : (Σ y : S, Fin (orders seams collector D g L y.val)) → F, ∀ x,
      C.value P x = ∑ j, w j * C.observe P v
        (coefficient P (powered P S) B j.1.val ((j.2.val : ℤ) - D j.1.val)) x := by
  intro P D
  obtain ⟨w, hw⟩ := reconstruct_cells (r := r) (t := t) p l ((C.cell v).orderA C.level)
    (C.cell v).orderB S B seams hB hs collector hc hc' g L hg z hz
  refine ⟨w, fun x => ?_⟩
  exact contractGraph_replace _ _ v w _ (fun h hh => hw _ _ rfl rfl st pt x h (fun j _ => hh _))

/-- Rotate two blocks of stations into position for fusion. -/
theorem rotate (v : V) (f : Test F r t) (hf : Signed f)
    (a b c : List (Station F r t T X)) (h : (C.cell v).stations = a ++ b ++ c) (x : X) :
    C.observe P v f x = (-1 : F) ^ (sumA a * sumA b + sumB a * sumB b) *
      (C.put v ⟨(C.cell v).ports, b ++ a ++ c⟩).observe P v f x := by
  have e := C.replace (P := P) v f (fun _ : Unit => (-1 : F) ^ (sumA a * sumA b + sumB a * sumB b))
    (fun _ => ⟨(C.cell v).ports, b ++ a ++ c⟩) (fun _ => f) (by
      intro x h' _
      rw [Fintype.sum_unique, show C.cell v = ⟨(C.cell v).ports, a ++ b ++ c⟩ by rw [← h]]
      exact Surface.rotate P x a b c _ _ _ hf) x
  simpa using e

theorem merge (p l : ℕ) [ExpChar F p] (v : V) (c : Cell F r t T E X)
    (a b : Station F r t T X) (h : C.cell v = (c.insert b).insert a) (k : T)
    (A B : Finset F) (ha : a.pos ^ (p ^ l) ∈ A) (ha' : a.pos ∈ B) (hb : b.pos ^ (p ^ l) ∉ A)
    (hb' : b.pos ∉ B) (hc : c.Fixed (p ^ l) (A.erase (a.pos ^ (p ^ l))) (B.erase a.pos))
    (j : ℤ) (x : X) :
    let P := p ^ l
    C.observe P v (coefficient P A B a.pos j) x =
      ∑ q : merges P a b ((C.cell v).orderA C.level) (C.cell v).orderB j,
        (C.put v (c.insert (mergeAt a b k q))).value P x := by
  intro P
  let I := merges P a b ((C.cell v).orderA C.level) (C.cell v).orderB j
  have e := C.replace (P := P) v (coefficient P A B a.pos j) (fun _ : I => 1)
    (fun q => c.insert (mergeAt a b k q)) (fun _ => forms) (by
      intro x u hu
      have e := c.merge p l C.level a b k A B ha ha' hb hb' hc j x u (fun _ _ => hu _)
      rw [← h] at e
      dsimp only at e
      rw [← sum_attach] at e
      simp only [one_mul]
      exact e) x
  simpa only [one_mul, observe_forms] using e

variable {u : Station F r t T X} (s : Passage P u) (v w : V) (j : E)
variable (L R : Socket F r t T E X) (k k' : T)

/-- Replace both ends of one seam. Other cells ignore the new private wire. -/
def crossed (S : Lower F r) (i : s.Branch) : Scene F r t T V E (X × Level t u.b) where
  cell := update (update (fun z => (C.cell z).pull Prod.fst id) v (s.left L j k i)) w
    (s.right R j k' S i)
  level := update C.level j i.height

/-- The outside sum indexes orders, levels and regular evaluations. The
residue state is an ordinary wire inside each resulting network. -/
theorem cross (p l : ℕ) [ExpChar F p] (hP : P = p ^ l) (hs : s.Fits L.base R.base C.level)
    (hvw : v ≠ w) (he : C.level j = s.e) (hv : C.cell v = (L.plug j s.z).insert u)
    (hw : C.cell w = R.plug j s.y) (hl : Unused j L.base.ports) (hr : Unused j R.base.ports)
    (other : ∀ z, z ≠ v → z ≠ w → Unused j (C.cell z).ports) :
    let S := lowering F r
    let f := s.signed C.level L R p l hP
    ∀ x,
      C.observe P v s.coeff x = ∑ i, f i * ∑ y : Level t u.b,
        (C.crossed s v w j L R k k' S i).value P (x, y) := by
  intro S f
  have hf := s.crossing C.level L R j p l hP hs hl hr k k'
  intro x
  let g := update (fun i => (C.cell i).eval P x) v (fun h => (C.cell v).test P x h s.coeff)
  have hg (z) (hz : z ≠ v) (hz' : z ≠ w) (h : E → Wedge r) (a) :
      g z (update h j a) = g z h := by
    simp only [g, update_of_ne hz, Cell.eval_update _ _ _ _ _ (other z hz hz')]
  let I := s.Branch × Level t u.b
  let left (i : I) := (s.left L j k i.1).eval P (x, i.2)
  let right (i : I) := (s.right R j k' S i.1).eval P (x, i.2)
  have move := contractGraph_seam g C.level v w hvw j hg
    (fun i : I => f i.1) (fun i => i.1.height) left right (by
      intro h hh
      rw [he, Fintype.sum_prod_type]
      simp only [g, update_self, update_of_ne hvw.symm, hv, hw, left, right, ← mul_sum]
      exact hf x h hh)
  change contractGraph g _ = _
  rw [move, Fintype.sum_prod_type]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun y _ => congrArg (f i * ·) ?_
  let C' := C.crossed s v w j L R k k' S i
  change _ = contractGraph (fun z => (C'.cell z).eval P (x, y)) C'.level
  congr 1
  funext z h
  unfold C' crossed
  by_cases hz : z = w
  · subst z; simp [right]
  by_cases hz' : z = v
  · subst z; simp [left, hvw]
  simp [g, hz, hz', Cell.eval_pull]

end Scene
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface
end

/-!
# States of the motion procedure

An active station carries its crossing count. A residue, including an
original auxiliary mark, is passive. A collector keeps its name and
position. Ordinary wires created on crossing are numbered in order
of creation and contracted separately from the seam indices.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface

open Finset Function
open scoped Classical

inductive Role where
  | active (count : ℕ)
  | residue
  | collector
  deriving DecidableEq

def Role.clock : Role → ℕ
  | .active n => n
  | _ => 0

structure Tag (V T : Type) where
  role : Role
  name : Option T
  reads : Finset (V ⊕ ℕ)

variable {F T V E X : Type} [Field F] {r t : ℕ}

def Tag.join (u v : Tag V T) : Tag V T :=
  if u.role = .collector then {u with reads := u.reads ∪ v.reads}
  else {v with reads := u.reads ∪ v.reads}

def Tag.leave (j : ℕ) : Tag V T := ⟨.residue, none, {.inr j}⟩

def Tag.take (v : Tag V T) (j : ℕ) : Tag V T :=
  ⟨.active (v.role.clock + 1), v.name, insert (.inr j) v.reads⟩

abbrev Stack (X : Type) (t : ℕ) : List ℕ → Type
  | [] => X
  | n :: l => Stack X t l × Level t n

def traceStack (t : ℕ) (x : X) : (l : List ℕ) → (Stack X t l → F) → F
  | [], f => f x
  | n :: ns, f => traceStack t x ns (fun y => ∑ h : Level t n, f (y, h))

structure Stage (F : Type) (r t : ℕ) (T V E X : Type) where
  hidden : List ℕ
  scene : Scene F r t (Tag V T) V E (Stack X t hidden)
  hits : E → ℕ
  expired : ℕ
  footprint : V → Finset (V ⊕ ℕ)

namespace Stage

variable (s : Stage F r t T V E X)

abbrev St := Station F r t (Tag V T) (Stack X t s.hidden)
abbrev Ct := Cell F r t (Tag V T) E (Stack X t s.hidden)
abbrev Sock := Socket F r t (Tag V T) E (Stack X t s.hidden)

def edges (v : V) := ((s.scene.cell v).ports.map Prod.fst).toFinset

def value [Fintype V] [Fintype E] (P : ℕ) (x : X) :=
  traceStack t x s.hidden (s.scene.value P)

def put (v : V) (c : s.Ct) : Stage F r t T V E X :=
  {s with scene := s.scene.put v c}

def freeze (v : V) (c : s.Ct) (u : s.St) : Stage F r t T V E X :=
  {s.put v (c.insert {u with label := {u.label with role := .collector}}) with expired := s.expired + 1}

def advance {P : ℕ} {u : s.St} (a : Passage P u) (v w : V) (j : E) (L R : s.Sock)
    (S : Lower F r) (i : a.Branch) : Stage F r t T V E X where
  hidden := u.b :: s.hidden
  scene := s.scene.crossed a v w j L R (Tag.leave s.hidden.length) (u.label.take s.hidden.length) S i
  hits := update s.hits j (s.hits j + 1)
  expired := s.expired
  footprint k := if k = v ∨ k = w then insert (.inr s.hidden.length) (s.footprint k ∪ u.label.reads)
    else s.footprint k

/-- At most one mover is away from its initial cell. -/
def Ready (v : V) (rest : List s.St) : Prop :=
  (∀ u ∈ rest, u.label.role.clock = 0) ∧
  ∀ w, w ≠ v → ∀ u ∈ (s.scene.cell w).stations, u.label.role.clock = 0

/-- Support of one expansion step. Branch weights are separate from
the transition, so the same invariants apply to all linear combinations. -/
inductive Step (P g H U : ℕ) : Stage F r t T V E X → Stage F r t T V E X → Prop where
  | perm (s : Stage F r t T V E X) (v : V) (ls : List s.St) (hs : (s.scene.cell v).stations.Perm ls) :
      Step P g H U s (s.put v ⟨(s.scene.cell v).ports, ls⟩)
  | expire (s : Stage F r t T V E X) (v : V) (c : s.Ct) (u : s.St) (hv : s.scene.cell v = c.insert u)
      (ha : u.label.role = .active U) (ready : s.Ready v c.stations) :
      Step P g H U s (s.freeze v c u)
  | merge (s : Stage F r t T V E X) (v : V) (c : s.Ct) (a b : s.St) (n : ℕ)
      (hv : s.scene.cell v = (c.insert b).insert a) (ha : b.label.role = .active n)
      (ready : s.Ready v (a :: c.stations)) (j : ℤ) (q : ℤ × ℤ)
      (hq : q ∈ merges P a b ((s.scene.cell v).orderA s.scene.level) (s.scene.cell v).orderB j)
      (bound : j ≤ if a.label.role = .collector then (g * (energyOf P b + 2 * P * H) : ℕ) else 0) :
      Step P g H U s (s.put v (c.insert (mergeAt a b (a.label.join b.label) q)))
  | cross (s : Stage F r t T V E X) (v w : V) (j : E) (L R : s.Sock) (u : s.St) (a : Passage P u)
      (S : Lower F r) (i : a.Branch) (n : ℕ) (hv : s.scene.cell v = (L.plug j a.z).insert u)
      (hw : s.scene.cell w = R.plug j a.y) (ne : v ≠ w)
      (he : s.scene.level j = a.e) (hh : a.H = H)
      (ha : u.label.role = .active n) (hn : n < U) (ready : s.Ready v L.stations)
      (fixed : S = Motion.lowering F r) :
      Step P g H U s (s.advance a v w j L R S i)

end Stage
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface
end

/-! # Incidence, stationary positions, and selection of the next mover -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface

open Finset Function
open scoped Classical
variable {F T V E X : Type} {r t P g H U : ℕ}

def Cell.positions (c : Cell F r t T E X) := c.stations.map Station.pos ++ c.ports.map Prod.snd

namespace Stage

variable (s : Stage F r t T V E X)

def ports (v : V) := (s.scene.cell v).ports

/-- A static, loopless seam incidence pattern. -/
structure Layout (src dst : E → V) (g : ℕ) : Prop where
  loopless : ∀ i, src i ≠ dst i
  incident : ∀ v i, i ∈ (s.ports v).map Prod.fst ↔ src i = v ∨ dst i = v
  unique : ∀ v, ((s.ports v).map Prod.fst).Nodup
  degree : ∀ v, (s.ports v).length ≤ g

/-- Dynamic invariants of the motion procedure. -/
structure Valid (U : ℕ) : Prop where
  distinct : ∀ v, (s.scene.cell v).positions.Nodup
  collector : ∀ v, ∃ u ∈ (s.scene.cell v).stations, u.label.role = .collector
  bound : ∀ v u, u ∈ (s.scene.cell v).stations → u.label.role.clock ≤ U
  focus : ∀ v u, u ∈ (s.scene.cell v).stations → u.label.role.clock ≠ 0 →
    ∀ w b, b ∈ (s.scene.cell w).stations → b.label.role.clock ≠ 0 → w = v ∧ b = u

def Stopped : Prop := ∀ v u, u ∈ (s.scene.cell v).stations → ∀ n, u.label.role ≠ .active n

def Room (M N : ℕ) : Prop := ∀ v, (s.scene.cell v).positions.length ≤ M ∧
  (s.scene.cell v).bigA s.scene.level + sumB (s.scene.cell v).stations ≤ N

abbrev Reach [Field F] (P g H U : ℕ) (y : Stage F r t T V E X) :=
  Relation.ReflTransGen (Step P g H U) s y

variable [Field F] {s} {s' : Stage F r t T V E X}

theorem Step.ports_eq (h : Step P g H U s s') : s'.ports = s.ports := by
  funext i
  cases h with
  | perm v ls hs =>
    by_cases hi : i = v <;> simp [ports, put, Scene.put, hi]
  | expire v c u hv =>
    by_cases hi : i = v <;> simp [ports, freeze, put, Scene.put, hi, hv, Cell.insert]
  | merge v c a b n hv =>
    by_cases hi : i = v <;> simp [ports, put, Scene.put, hi, hv, Cell.insert]
  | cross v w j L R u a S k n hv hw ne =>
    by_cases hi : i = w
    · simp [ports, advance, Scene.crossed, hi, hw, Passage.right, Cell.insert, Cell.pull]
    by_cases hi' : i = v
    · simp [ports, advance, Scene.crossed, hi', ne, hv, Passage.left, Cell.insert, Cell.pull]
    simp [ports, advance, Scene.crossed, hi, hi', Cell.pull]

theorem Step.edges_eq (h : Step P g H U s s') : s'.edges = s.edges :=
  congrArg (fun f => fun v => ((f v).map Prod.fst).toFinset) h.ports_eq

theorem Step.layout {src dst : E → V} (h : Step P g H U s s') (a : s.Layout src dst g) :
    s'.Layout src dst g :=
  ⟨a.loopless, h.ports_eq.symm ▸ a.incident, h.ports_eq.symm ▸ a.unique, h.ports_eq.symm ▸ a.degree⟩

end Stage
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface
end

/-!
# Energy and progress of the motion procedure

Each active mark keeps one reserve; a stationary residue has no reserve.
All energies use units of `1 / (2P)`. In particular the public seam
energy is multiplied by `P`.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface
open Finset Function
open scoped Classical

variable {F T E V X : Type} {r t P H g U : ℕ}

def Role.mobile (M : ℕ) : Role → ℕ → ℕ
  | .active _, e => e + M
  | .residue, e => e
  | .collector, _ => 0

def Role.collected : Role → ℕ → ℕ
  | .collector, e => e
  | _, _ => 0

def Role.fuel (U : ℕ) : Role → ℕ
  | .active i => 2 + 2 * (U - i)
  | _ => 1

namespace Stage
variable (s : Stage F r t T V E X)

/-- A local sum over the marks, independent of their order and tables. -/
def tally (P : ℕ) (f : Role → ℕ → ℕ) (v : V) :=
  ((s.scene.cell v).stations.map (fun u => f u.label.role (energyOf P u))).sum

def ledger [Fintype V] (P H : ℕ) : Ledger V E where
  mobile := s.tally P (Role.mobile (2 * P * H))
  collected := s.tally P Role.collected
  seam e := P * s.scene.level e
  hits := s.hits
  clock := ∑ v, s.tally P (fun r _ => r.clock) v
  expired := s.expired

/-- Each remaining hop pays for the new residue and one step of progress. -/
def potential [Fintype V] (U : ℕ) := ∑ v, s.tally 0 (fun r _ => r.fuel U) v

private theorem tally_perm (v : V) (ls : List s.St) (hs : (s.scene.cell v).stations.Perm ls)
    (f : Role → ℕ → ℕ) (w : V) :
    (s.put v ⟨(s.scene.cell v).ports, ls⟩).tally P f w = s.tally P f w := by
  by_cases he : w = v
  · subst w
    simp only [tally, put, Scene.put, update_self]
    exact (hs.symm.map _).sum_eq
  · simp [tally, put, Scene.put, he]

private theorem tally_freeze (v : V) (c : s.Ct) (u : s.St)
    (hv : s.scene.cell v = c.insert u) (f : Role → ℕ → ℕ) (w : V) :
    (s.freeze v c u).tally P f w + (if w = v then f u.label.role (energyOf P u) else 0) =
    s.tally P f w + (if w = v then f .collector (energyOf P u) else 0) := by
  by_cases he : w = v
  · subst w
    simp [tally, freeze, put, Scene.put, hv, Cell.insert, energyOf, add_comm, add_left_comm]
  · simp [tally, freeze, put, Scene.put, he]

private theorem tally_merge (v : V) (c : s.Ct) (a b u : s.St)
    (hv : s.scene.cell v = (c.insert b).insert a) (f : Role → ℕ → ℕ) (w : V) :
    (s.put v (c.insert u)).tally P f w +
      (if w = v then f a.label.role (energyOf P a) + f b.label.role (energyOf P b) else 0) =
    s.tally P f w + (if w = v then f u.label.role (energyOf P u) else 0) := by
  by_cases he : w = v
  · subst w
    simp [tally, put, Scene.put, hv, Cell.insert, add_comm, add_left_comm, add_assoc]
  · simp [tally, put, Scene.put, he]

variable [Field F]

private theorem tally_cross (P' : ℕ) (v w : V) (j : E) (L R : s.Sock) (u : s.St) (a : Passage P u)
    (S : Lower F r) (i : a.Branch)
    (hv : s.scene.cell v = (L.plug j a.z).insert u) (hw : s.scene.cell w = R.plug j a.y)
    (ne : v ≠ w) (f : Role → ℕ → ℕ) (z : V) :
    (s.advance a v w j L R S i).tally P' f z +
      (if z = v then f u.label.role (energyOf P' u) else 0) =
    s.tally P' f z +
      (if z = v then f .residue (energyOf P' (a.leaves (Tag.leave s.hidden.length) i)) else 0) +
      (if z = w then f (.active (u.label.role.clock + 1))
        (energyOf P' (a.arrives (u.label.take s.hidden.length) S i)) else 0) := by
  by_cases h : z = w
  · simp [tally, advance, Scene.crossed, h, hw, ne.symm, Passage.right, Cell.insert, Cell.pull, Station.pull,
      Passage.arrives, transfer, Tag.take, energyOf, Function.comp_def, add_comm]
  by_cases h' : z = v
  · simp [tally, advance, Scene.crossed, h', hv, ne, Passage.left, Cell.insert, Cell.pull, Station.pull,
      Passage.leaves, residue, Tag.leave, energyOf, Function.comp_def, add_comm, add_left_comm]
  simp [tally, advance, Scene.crossed, h, h', Cell.pull, Station.pull, energyOf, Function.comp_def]


variable [Fintype V]

omit [Field F] in
theorem potential_perm (v : V) (ls : List s.St) (hs : (s.scene.cell v).stations.Perm ls) :
    (s.put v ⟨(s.scene.cell v).ports, ls⟩).potential U = s.potential U := by
  simp only [potential, s.tally_perm v ls hs]

omit [Field F] in
theorem potential_expire (v : V) (c : s.Ct) (u : s.St)
    (hv : s.scene.cell v = c.insert u) (ha : u.label.role = .active U) :
    (s.freeze v c u).potential U < s.potential U := by
  have h := sum_congr rfl fun z (_ : z ∈ univ) =>
    s.tally_freeze (P := 0) v c u hv (fun r _ => r.fuel U) z
  simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true, ha] at h
  change (s.freeze v c u).potential U + (2 + 2 * (U - U)) = s.potential U + 1 at h
  omega

omit [Field F] in
theorem potential_merge (v : V) (c : s.Ct) (a b u : s.St) {n : ℕ}
    (hv : s.scene.cell v = (c.insert b).insert a) (ha : b.label.role = .active n)
    (hj : u.label = a.label.join b.label) :
    (s.put v (c.insert u)).potential U < s.potential U := by
  have h := sum_congr rfl fun z (_ : z ∈ univ) =>
    s.tally_merge (P := 0) v c a b u hv (fun r _ => r.fuel U) z
  simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true] at h
  change (s.put v (c.insert u)).potential U + (a.label.role.fuel U + b.label.role.fuel U) =
    s.potential U + u.label.role.fuel U at h
  have ht : u.label.role.fuel U < a.label.role.fuel U + b.label.role.fuel U := by
    cases he : a.label.role <;> simp [hj, Tag.join, he, ha, Role.fuel]
  omega

theorem potential_advance (v w : V) (j : E) (L R : s.Sock) (u : s.St) (a : Passage P u)
    (S : Lower F r) (i : a.Branch) {n : ℕ}
    (hv : s.scene.cell v = (L.plug j a.z).insert u) (hw : s.scene.cell w = R.plug j a.y)
    (ne : v ≠ w) (ha : u.label.role = .active n) (hn : n < U) :
    (s.advance a v w j L R S i).potential U < s.potential U := by
  have h := sum_congr rfl fun z (_ : z ∈ univ) =>
    s.tally_cross 0 v w j L R u a S i hv hw ne (fun r _ => r.fuel U) z
  simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true, ha] at h
  change (s.advance a v w j L R S i).potential U + (2 + 2 * (U - n)) =
    s.potential U + 1 + (2 + 2 * (U - (n + 1))) at h
  omega

omit [Field F] in
theorem potential_le (U : ℕ) :
    s.potential U ≤ (2 + 2 * U) * ∑ v, (s.scene.cell v).stations.length := by
  rw [mul_sum]
  apply sum_le_sum
  intro v _
  unfold tally
  generalize (s.scene.cell v).stations = us
  induction us with
  | nil => simp
  | cons a as ih =>
    have h : a.label.role.fuel U ≤ 2 + 2 * U := by cases a.label.role <;> simp [Role.fuel] <;> omega
    simpa [mul_add, add_comm] using Nat.add_le_add h ih

variable [Fintype E] {s} {s' : Stage F r t T V E X}

omit [Fintype V] [Fintype E] in
/-- At a continued fusion the total mobile energy does not grow.
Only terminal fusion is allowed a positive Laurent order. -/
private theorem merge_bounds (a b : s.St) {n k l : ℕ} {j : ℤ} {q : ℤ × ℤ}
    (ha : b.label.role = .active n) (hq : q ∈ merges P a b k l j)
    (bound : j ≤ if a.label.role = .collector then (g * (energyOf P b + 2 * P * H) : ℕ) else 0) :
    let c := mergeAt a b (a.label.join b.label) q
    let μ := if a.label.role = .collector then energyOf P b + 2 * P * H else 0
    let mob := Role.mobile (2 * P * H)
    mob c.label.role (energyOf P c) + μ ≤
      mob a.label.role (energyOf P a) + mob b.label.role (energyOf P b) ∧
    Role.collected c.label.role (energyOf P c) ≤
      Role.collected a.label.role (energyOf P a) + Role.collected b.label.role (energyOf P b)
        + (1 + 2 * g) * μ ∧
    c.label.role.clock ≤ a.label.role.clock + b.label.role.clock := by
  intro c μ mob
  have hc : c.label = a.label.join b.label := rfl
  have he : (energyOf P c : ℤ) = energyOf P a + energyOf P b + 2 * j :=
    energy_merge P a b _ hq
  cases hr : a.label.role <;>
    simp [hc, Tag.join, ha, hr, mob, Role.mobile, Role.collected, Role.clock, μ, -Nat.cast_add, -Nat.cast_mul] at bound ⊢
  · omega
  · omega
  · have nonneg : (0 : ℤ) ≤ (2 * P * H : ℕ) := by positivity
    rw [← Nat.cast_le (α := ℤ)]
    push_cast at bound nonneg ⊢
    linarith only [he, bound, nonneg]

theorem Step.budget (h : Step P g H U s s') :
    Ledger.Budget s.edges g (2 * P * H) U (s.ledger P H) (s'.ledger P H) := by
  let M := 2 * P * H
  let mob := Role.mobile M
  let col := Role.collected
  let clk := fun (r : Role) (_ : ℕ) => r.clock
  cases h with
  | perm v ls hs =>
    have he : (s.put v ⟨(s.scene.cell v).ports, ls⟩).ledger P H = s.ledger P H := by
      have ht (f) := funext (s.tally_perm (P := P) v ls hs f)
      simp only [ledger, ht]
      rfl
    rw [he]
    exact .refl
  | expire v c u hv ha =>
    let q := s.freeze v c u
    refine Ledger.Budget.collect (fun w => if w = v then energyOf P u else 0) ?_ ?_ rfl rfl ?_
    · intro w
      have h := s.tally_freeze (P := P) v c u hv mob w
      change q.tally P mob w + (if w = v then energyOf P u else 0) ≤ s.tally P mob w
      rw [ha] at h
      change q.tally P mob w + (if w = v then energyOf P u + M else 0) =
        s.tally P mob w + (if w = v then 0 else 0) at h
      split_ifs at h ⊢ <;> omega
    · intro w
      have h := s.tally_freeze (P := P) v c u hv col w
      change q.tally P col w ≤ s.tally P col w + (1 + 2 * g) * (if w = v then energyOf P u else 0)
      rw [ha] at h
      change q.tally P col w + (if w = v then 0 else 0) =
        s.tally P col w + (if w = v then energyOf P u else 0) at h
      have := Nat.le_mul_of_pos_left (energyOf P u) (show 0 < 1 + 2 * g by omega)
      split_ifs at h ⊢ <;> omega
    · have h := sum_congr rfl fun w (_ : w ∈ univ) => s.tally_freeze (P := P) v c u hv clk w
      simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true, ha] at h
      change (q.ledger P H).clock + U = (s.ledger P H).clock + 0 at h
      change U * (s.expired + 1) + (q.ledger P H).clock ≤ U * s.expired + (s.ledger P H).clock
      rw [mul_add]
      omega
  | merge v c a b n hv ha _ j q hq bound =>
    let u := mergeAt a b (a.label.join b.label) q
    let y := s.put v (c.insert u)
    let μ := if a.label.role = .collector then energyOf P b + M else 0
    obtain ⟨h₁, h₂, h₃⟩ := merge_bounds a b ha hq bound
    change mob u.label.role (energyOf P u) + μ ≤
      mob a.label.role (energyOf P a) + mob b.label.role (energyOf P b) at h₁
    change col u.label.role (energyOf P u) ≤
      col a.label.role (energyOf P a) + col b.label.role (energyOf P b) + (1 + 2 * g) * μ at h₂
    refine Ledger.Budget.collect (fun w => if w = v then μ else 0) ?_ ?_ rfl rfl ?_
    · intro w
      have h := s.tally_merge (P := P) v c a b u hv mob w
      change (s.put v (c.insert u)).tally P mob w + (if w = v then μ else 0) ≤ s.tally P mob w
      split_ifs at h ⊢ <;> omega
    · intro w
      have h := s.tally_merge (P := P) v c a b u hv col w
      change (s.put v (c.insert u)).tally P col w ≤ s.tally P col w + (1 + 2 * g) * (if w = v then μ else 0)
      split_ifs at h ⊢ <;> omega
    · have h := sum_congr rfl fun w (_ : w ∈ univ) => s.tally_merge (P := P) v c a b u hv clk w
      simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true] at h
      change (y.ledger P H).clock + (a.label.role.clock + b.label.role.clock) =
        (s.ledger P H).clock + u.label.role.clock at h
      change u.label.role.clock ≤ a.label.role.clock + b.label.role.clock at h₃
      change U * s.expired + (y.ledger P H).clock ≤ U * s.expired + (s.ledger P H).clock
      omega
  | cross v w j L R u a S i n hv hw ne he hh ha =>
    let q := s.advance a v w j L R S i
    let l := energyOf P (a.leaves (Tag.leave s.hidden.length) i)
    let r := energyOf P (a.arrives (u.label.take s.hidden.length) S i)
    have hl := a.energy_step (Tag.leave s.hidden.length) (u.label.take s.hidden.length) S i
    rw [hh] at hl
    change l + r ≤ energyOf P u ∧ P * i.height + (energyOf P u + M) ≤ P * a.e at hl
    have hw' : j ∈ s.edges w := by simp [edges, hw, Socket.plug]
    refine Ledger.Budget.cross v w j hw' (energyOf P u + M) (r + M) (by omega)
      (by omega) ?_ ?_ ?_ ?_ ?_
    · intro z
      have h := s.tally_cross P v w j L R u a S i hv hw ne mob z
      rw [ha] at h
      change q.tally P mob z + (if z = v then energyOf P u + M else 0) =
        s.tally P mob z + (if z = v then l else 0) + (if z = w then r + M else 0) at h
      change q.tally P mob z + (if z = v then r + M else 0) ≤
        s.tally P mob z + (if z = w then r + M else 0)
      split_ifs at h ⊢ <;> omega
    · funext z
      have h := s.tally_cross P v w j L R u a S i hv hw ne col z
      rw [ha] at h
      change q.tally P col z + (if z = v then 0 else 0) =
        s.tally P col z + (if z = v then 0 else 0) + (if z = w then 0 else 0) at h
      change q.tally P col z = s.tally P col z
      simpa only [ite_self, add_zero] using h
    · intro k
      by_cases hk : k = j
      · simpa [ledger, advance, Scene.crossed, hk, he] using hl.2
      · simp [ledger, advance, Scene.crossed, hk]
    · intro k
      by_cases hk : k = j <;> simp [ledger, advance, hk]
    · have h := sum_congr rfl fun z (_ : z ∈ univ) => s.tally_cross P v w j L R u a S i hv hw ne clk z
      simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true, ha] at h
      change (q.ledger P H).clock + n = (s.ledger P H).clock + 0 + (n + 1) at h
      change U * s.expired + (q.ledger P H).clock ≤ U * s.expired + (s.ledger P H).clock + 1
      omega

omit [Fintype V] [Fintype E] in
theorem Step.stations_le (h : Step P g H U s s') (z : V) :
    (s'.scene.cell z).stations.length + (∑ e ∈ s.edges z, s.hits e) ≤
      (s.scene.cell z).stations.length + ∑ e ∈ s.edges z, s'.hits e := by
  cases h with
  | perm v ls hs =>
    by_cases h : z = v <;> simp [put, Scene.put, h, hs.length_eq]
  | expire v c u hv =>
    by_cases h : z = v <;> simp [freeze, put, Scene.put, h, hv, Cell.insert]
  | merge v c a b n hv =>
    by_cases h : z = v <;> simp [put, Scene.put, h, hv, Cell.insert]
  | cross v w j L R u a S i n hv hw ne =>
    have hu e : (s.advance a v w j L R S i).hits e = s.hits e + if e = j then 1 else 0 := by
      by_cases h : e = j <;> simp [advance, h]
    simp_rw [hu, sum_add_distrib, sum_ite_eq']
    by_cases hz : z = w
    · have hj : j ∈ s.edges w := by simp [edges, hw, Socket.plug]
      simp [hz, hj, advance, Scene.crossed, hw, Passage.right, Cell.insert, Cell.pull]
      omega
    by_cases hz' : z = v
    · simp [hz', ne, advance, Scene.crossed, hv, Passage.left, Cell.insert, Cell.pull]
    simp [hz, hz', advance, Scene.crossed, Cell.pull]

def collectors (s : Stage F r t T V E X) := ∑ v, s.tally 0 (fun r _ => r.collected 1) v

omit [Fintype E] in
theorem Step.collectors (h : Step P g H U s s') :
    s'.collectors + s.expired = s.collectors + s'.expired := by
  let f := fun (r : Role) (_ : ℕ) => r.collected 1
  cases h with
  | perm v ls hs =>
    simp only [Stage.collectors, s.tally_perm v ls hs]
    rfl
  | expire v c u hv ha =>
    have h := sum_congr rfl fun z (_ : z ∈ univ) => s.tally_freeze (P := 0) v c u hv f z
    simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true, ha] at h
    change (s.freeze v c u).collectors + 0 = s.collectors + 1 at h
    change _ = s.collectors + (s.expired + 1)
    omega
  | merge v c a b n hv ha _ j q =>
    let u := mergeAt a b (a.label.join b.label) q
    have h := sum_congr rfl fun z (_ : z ∈ univ) => s.tally_merge (P := 0) v c a b u hv f z
    simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true, ha] at h
    change (s.put v (c.insert u)).collectors + (a.label.role.collected 1 + 0) =
      s.collectors + (a.label.join b.label).role.collected 1 at h
    have he : (a.label.join b.label).role.collected 1 = a.label.role.collected 1 := by
      cases hz : a.label.role <;> simp [Tag.join, hz, ha, Role.collected]
    rw [he] at h
    change (s.put v (c.insert u)).collectors + s.expired = s.collectors + s.expired
    omega
  | cross v w j L R u a S i n hv hw ne he hh ha =>
    have h := sum_congr rfl fun z (_ : z ∈ univ) => s.tally_cross 0 v w j L R u a S i hv hw ne f z
    simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true, ha] at h
    change (s.advance a v w j L R S i).collectors + 0 = s.collectors + 0 + 0 at h
    exact congrArg (· + s.expired) (by simpa using h)

omit [Fintype V] [Fintype E] in
theorem Reach.ports_eq (h : s.Reach P g H U s') : s'.ports = s.ports := by
  induction h with
  | refl => rfl
  | tail _ q ih => exact q.ports_eq.trans ih

omit [Fintype V] [Fintype E] in
theorem Reach.edges_eq (h : s.Reach P g H U s') : s'.edges = s.edges :=
  congrArg (fun f => fun v => ((f v).map Prod.fst).toFinset) h.ports_eq

theorem Reach.budget (h : s.Reach P g H U s') :
    Ledger.Budget s.edges g (2 * P * H) U (s.ledger P H) (s'.ledger P H) := by
  induction h with
  | refl => exact .refl
  | tail v q ih => exact ih.trans ((Reach.edges_eq v) ▸ q.budget)

omit [Fintype V] [Fintype E] in
theorem Reach.stations_le (h : s.Reach P g H U s') (v : V) :
    (s'.scene.cell v).stations.length + (∑ e ∈ s.edges v, s.hits e) ≤
      (s.scene.cell v).stations.length + ∑ e ∈ s.edges v, s'.hits e := by
  induction h with
  | refl => rfl
  | tail w q ih =>
    have hz := q.stations_le v
    rw [Reach.edges_eq w] at hz
    omega

omit [Fintype E] in
theorem Reach.collectors (h : s.Reach P g H U s') :
    s'.collectors + s.expired = s.collectors + s'.expired := by
  induction h with
  | refl => rfl
  | tail _ q ih => have := q.collectors; omega
end Stage
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface
end
