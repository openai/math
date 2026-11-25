import OAI.Computability.NearSquareRoot.InterchangeStageRoute
import OAI.Computability.NearSquareRoot.InterchangeROMTableSeries

/-! # Natural-number matrices for the five grouped interchange gates -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMStageTable

abbrev Role := ℕ × ℕ × ℕ × ℕ
abbrev Ground := Role × ℕ
abbrev Term := Ground × ℕ

def plain (v : ℕ) : Role := (0,0,v,0)
def reserve (v b : ℕ) : Role := (1,0,v,b)
def active (j v b : ℕ) : Role := (2,j,v,b)
def rect (j b : ℕ) : Role := (3,j,0,b)
def rankTerm (j i k : ℕ) : Role := (4,j,i,k)
def mixed (j i : ℕ) : Role := (5,j,i,0)
def label (j v : ℕ) : Role := (6,j,v,0)

/-- Numerical fields of the rectangle and row-mixer certificate. The mask
arguments are the rectangle followed by the label. -/
structure Data where
  p : ℕ
  labels : ℕ
  rectangles : ℕ
  queries : ℕ
  ranks : ℕ
  lanes : ℕ
  src : ℕ → ℕ → Bool
  dst : ℕ → ℕ → Bool
  row : ℕ → ℕ
  col : ℕ → ℕ
  minor : ℕ → ℕ → ℕ
  base : ℕ → ℕ → ℕ
  query : ℕ → ℕ → ℕ → ℕ

def term (u : Role) (k c : ℕ) : Term := ((u,k),c)

/-- Enumerate and concatenate the contributions in a fixed finite axis. -/
def across (n : ℕ) (f : ℕ → List Term) : List Term := (List.range n).flatMap f

/-- The first table shares a partial sum across all destinations of one rectangle. -/
def partials (g : Data) (o : Role) (d : ℕ) : List Term :=
  if o.1 = 0 then [term o d 1] else
    across g.labels fun v => if g.src o.2.2.2 v then [term (active o.2.1 v o.2.2.2) d 1] else []

/-- Singleton and incident rows use the same column of the selected minor. -/
def mix (g : Data) (o : Role) (d : ℕ) : List Term :=
  if o.1 = 5 then across g.ranks fun i =>
    term (rankTerm o.2.1 i 0) d (g.minor o.2.2.1 i) ::
      across g.rectangles fun b => if g.dst b (g.row i) then
        [term (rankTerm o.2.1 i (b+1)) d (g.minor o.2.2.1 i)] else []
  else [term o d 1]

/-- Distribution includes the negative, retained rectangle term. -/
def scatter (g : Data) (o : Role) (d : ℕ) : List Term :=
  if o.1 = 0 then [term o d 1] else
  if o.1 = 6 then across g.ranks fun i => if o.2.2.1 = g.col i then
    [term (rankTerm o.2.1 i 0) d 1] else []
  else term (rect o.2.1 o.2.2.2) d (g.p-1) ::
    across g.ranks fun i => if g.src o.2.2.2 (g.col i) then
      [term (rankTerm o.2.1 i (o.2.2.2+1)) d 1] else []

/-- The query operators are independently supplied matrices on the ground lanes. -/
def collect (g : Data) (o : Role) (d : ℕ) : List Term :=
  let queries := across g.queries fun j => across g.lanes fun k =>
    [term (if o.1 = 0 then label j o.2.2.1 else active j o.2.2.1 o.2.2.2) k (g.query j d k)]
  if o.1 = 0 then (across g.lanes fun k => [term (plain o.2.2.1) k (g.base d k)]) ++ queries
  else queries

/-- The final gate adds all the destination contributions to the retained row. -/
def finish (g : Data) (o : Role) (d : ℕ) : List Term :=
  term o d 1 :: across g.rectangles fun b => if g.dst b o.2.2.1 then
    [term (reserve o.2.2.1 b) d 1] else []

def terms (g : Data) (gate : ℕ) (o : Ground) : List Term :=
  match gate with
  | 0 => partials g o.1 o.2
  | 1 => mix g o.1 o.2
  | 2 => scatter g o.1 o.2
  | 3 => collect g o.1 o.2
  | _ => finish g o.1 o.2

def coefficient (terms : List Term) (i : Ground) : ℕ :=
  (terms.map fun a => if a.1 = i then a.2 else 0).sum

def matrix (g : Data) (gate : ℕ) (inputs outputs : List Ground) : List (List ℕ) :=
  outputs.map fun o => inputs.map (coefficient (terms g gate o))

def value {p : ℕ} (x : Ground → ZMod p) (terms : List Term) : ZMod p :=
  (terms.map fun t => (t.2 : ZMod p) * x t.1).sum

theorem coefficient_mulVec {A : Type} [Fintype A] (p : ℕ)
    (source : A → Ground) (hs : Function.Injective source) (ts : List Term)
    (covered : ∀ t ∈ ts, ∃ a, source a = t.1) (x : Ground → ZMod p) :
    ∑ a, (coefficient ts (source a) : ZMod p) * x (source a) = value x ts := by
  induction ts with
  | nil => simp [coefficient,value]
  | cons t rest ih =>
    obtain ⟨a,ha⟩ := covered t List.mem_cons_self
    have e (i : A) : t.1 = source i ↔ a = i := ha ▸ hs.eq_iff
    simp only [coefficient,List.map_cons,List.sum_cons,Nat.cast_add,add_mul,Finset.sum_add_distrib]
    rw [show (∑ b, (((if t.1 = source b then t.2 else 0 : ℕ) : ℕ) : ZMod p) * x (source b)) =
      (t.2 : ZMod p) * x t.1 by
        rw [Fintype.sum_eq_single a (fun b hb => by simp [(e b).not.mpr (Ne.symm hb)])]
        simp [ha]]
    exact congrArg ((t.2 : ZMod p) * x t.1 + ·) (ih fun u hu => covered u (List.mem_cons_of_mem _ hu))

end InterchangeROMStageTable

end NearSquareRoot
end Computability
end OAI
