import OAI.Hierarchy.TaggedWireExpansion

namespace OAI
/-! # Chronological histories of ordinary-sum wire substitutions -/

noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open scoped Classical BigOperators
variable {F : Type*} [Field F] {S : ℕ}

/-- The state carries a unique finite enumeration in the matrix expression and the raw tensor. -/
theorem state_sum_congr {A : Type*} (left right : Fintype A) (f : A→F) :
    (@Finset.univ A left).sum f=(@Finset.univ A right).sum f := by
  cases Subsingleton.elim left right
  rfl

/-- All choices retain their exact multiplicities on every adaptive branch. -/
def History {X : Type*} (choices : X → Type) (next : ∀ x, choices x → X) : ℕ → X → Type
  | 0,_ => Unit
  | d+1,x => Σ j : choices x, History choices next d (next x j)

variable {X : Type*} (choices : X → Type) (next : ∀ x,choices x → X) [∀ x,Fintype (choices x)]

instance historyFinite : (d : ℕ) → (x : X) → Fintype (History choices next d x)
  | 0,_ => inferInstanceAs (Fintype Unit)
  | d+1,x =>
    letI : ∀ c : choices x,Fintype (History choices next d (next x c)) := fun c =>
      historyFinite d (next x c)
    inferInstanceAs (Fintype (Σ c : choices x,History choices next d (next x c)))

def last : (d : ℕ) → (x : X) → History choices next d x → X
  | 0,x,_ => x
  | d+1,x,j => last d (next x j.1) j.2

/-- An adaptive finite schedule expands the starting wire into one ordinary
signed tensor per terminal history. The terminal restriction witnesses the
composition of every local site map selected along that particular history. -/
def telescope (wire : X → Widths S)
    (step : ∀ x, Expansion (raw F (wire x)) (choices x) (fun c=>wire (next x c))) :
    (d : ℕ) → (x : X) → Expansion (raw F (wire x)) (History choices next d x)
      (fun j => wire (last choices next d x j))
  | 0,x => Expansion.transport (wire x) (restrict_refl _)
  | d+1,x => (step x).bind (fun c=>telescope wire step d (next x c))

private def joinFields {A : Type} {B : A→Type} {n d : ℕ}
    (head : A ↪ (Fin n→Bool)) (tail : ∀a,B a ↪ (Fin d→Fin n→Bool)) :
    Sigma B ↪ (Fin (d+1)→Fin n→Bool) where
  toFun p := Fin.cases (head p.1) (tail p.1 p.2)
  inj' := by
    rintro ⟨a,u⟩ ⟨b,v⟩ eqn
    change (Fin.cases (head a) (tail a u) : Fin (d+1)→Fin n→Bool)=Fin.cases (head b) (tail b v) at eqn
    have same : a=b := head.injective (by simpa only [Fin.cases_zero] using congrFun eqn 0)
    subst b
    have rest : u=v := (tail a).injective (funext fun i=>by simpa only [Fin.cases_succ] using congrFun eqn i.succ)
    cases rest
    rfl

/-- Records on a chronological path encode into the actual per-round control
words. Reading all blocks recovers the path, including dependent later choices. -/
def fields {B : ℕ} (encode : ∀ x, choices x ↪ (Fin B → Bool)) :
    (d : ℕ) → (x : X) → History choices next d x ↪ (Fin d → Fin B → Bool)
  | 0,_ => (⟨fun _=>Fin.elim0,fun _ _ _=>Subsingleton.elim ..⟩ : Unit ↪ (Fin 0→Fin B→Bool))
  | d+1,x => joinFields (encode x) (fun c=>fields encode d (next x c))

def encodeHistory {B : ℕ} (encode : ∀x,choices x ↪ (Fin B → Bool)) (d : ℕ) (x : X) :
    History choices next d x ↪ (Fin (d*B) → Bool) where
  toFun a i := let z := finProdFinEquiv.symm i
               fields choices next encode d x a z.1 z.2
  inj' := by
    intro a b eqn
    apply (fields choices next encode d x).injective
    funext i j
    have digit := congrFun eqn (finProdFinEquiv (i,j))
    change (fields choices next encode d x a) (finProdFinEquiv.symm (finProdFinEquiv (i,j))).1
      (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2 =
      (fields choices next encode d x b) (finProdFinEquiv.symm (finProdFinEquiv (i,j))).1
      (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2 at digit
    simpa only [Equiv.symm_apply_apply] using digit

/-- Starting from a local restriction of the real matching/catalyst tensor
to the initial physical wires provides the same expansion on its original legs. -/
def from_initial (T : Raw.{0} (Fin S) F) (wire : X → Widths S)
    (step : ∀ x, Expansion (raw F (wire x)) (choices x) (fun c=>wire (next x c)))
    (d : ℕ) (x : X) (initial : T.Restricts (raw F (wire x))) :
    Expansion T (History choices next d x) (fun j=>wire (last choices next d x j)) := by
  let N := telescope choices next wire step d x
  let A := initial.choose
  have coeff := initial.choose_spec
  let term (a : History choices next d x) (v : ∀ i,T.Leg i) :=
    ∑ y : ∀ i,State (wire x) i, N.part a y * ∏ i,A i (v i) (y i)
  refine ⟨term,?_,?_⟩
  · funext v
    rw [Finset.sum_apply]
    have source : T.coeff v = ∑ y : ∀ i,State (wire x) i,(raw F (wire x)).coeff y * ∏ i,A i (v i) (y i) :=
      (coeff v).trans (state_sum_congr _ _ _)
    have pt (y : ∀i,State (wire x) i) : (raw F (wire x)).coeff y=∑ a,N.part a y := N.atPoint y
    rw [source]
    simp_rw [pt,Finset.sum_mul]
    unfold term
    exact Finset.sum_comm
  · intro a
    refine restrict_trans (B:=State (wire x)) (Y:=N.part a) ?_ (N.image a)
    refine ⟨A,fun v=>?_⟩
    exact state_sum_congr _ _ _

end Hierarchy.WireTelescope

end
end OAI
