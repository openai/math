import OAI.ThreeFlat.Diagonal.ApproximatePort
import OAI.ThreeFlat.Diagonal.TickPins
import OAI.ThreeFlat.FoldInput

namespace OAI
/-! # Uniform input bits for the collapsed block trace

All teams share the same tick template. A tick reads D, its team and absolute
time number in little-endian order, fixed parameter bits, and the two auxiliary
and two touched chunk words. Collapse inputs list all such ticks first and then
the old and new inactive halves.
-/

namespace ThreeFlat.Diagonal.ApproximateImage

open ApproximatePort

variable {α β : Type*} {d nt ns np a n teams chunks : ℕ}

abbrev pinCount (d nt ns np a : ℕ) := d + (nt + (ns + (np + (a + (a + (a+a))))))

/-- Concatenate the public and replaceable tick fields in tape order. -/
def fields (D : Fin d → α) (team : Fin nt → α) (step : Fin ns → α) (params : Fin np → α)
    (oldAux newAux oldChunk newChunk : Fin a → α) : Fin (pinCount d nt ns np a) → α :=
  Fin.append D (Fin.append team (Fin.append step (Fin.append params
    (Fin.append oldAux (Fin.append newAux (Fin.append oldChunk newChunk))))))

private theorem comp_append {m n : ℕ} (f : α → β) (x : Fin m → α) (y : Fin n → α) :
    f ∘ Fin.append x y = Fin.append (f ∘ x) (f ∘ y) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

theorem comp_fields (f : α → β) (D : Fin d → α) (team : Fin nt → α) (step : Fin ns → α)
    (params : Fin np → α) (oldAux newAux oldChunk newChunk : Fin a → α) :
    f ∘ fields D team step params oldAux newAux oldChunk newChunk =
      fields (f ∘ D) (f ∘ team) (f ∘ step) (f ∘ params)
        (f ∘ oldAux) (f ∘ newAux) (f ∘ oldChunk) (f ∘ newChunk) := by simp [fields, comp_append]

def digits (n k : ℕ) (i : Fin k) : Bool := n.testBit i.val

def tickPort (block : ℕ) (params : Fin np → Bool) (j : Fin (n+1)) (team : Fin teams) :
    Fin (pinCount d nt ns np a) → ApproximatePort (Fin chunks) d n a :=
  fields ApproximatePort.publicBit (.literal ∘ digits team.val nt)
    (.literal ∘ digits (block*(n+1)+j.val) ns) (.literal ∘ params)
    (.leftAux j) (.rightAux j) (.leftChunk j) (.rightChunk j)

def tickPins (D : Fin d → Bool) (block : ℕ) (params : Fin np → Bool)
    (j : Fin (n+1)) (team : Fin teams) (oldChunk newChunk oldAux newAux : Fin a → Bool) :
    Fin (pinCount d nt ns np a) → Bool :=
  fields D (digits team.val nt) (digits (block*(n+1)+j.val) ns) params oldAux newAux oldChunk newChunk

private theorem preceding {A : Type*} (n : ℕ) (v : Fin (n+1) → A) (i : Fin n) :
    beforeWord n (v 0) (fun j => v j.succ) i = v i.castSucc := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases rfl (fun k => ?_) i
    simpa [beforeWord] using ih (fun j => v j.succ) k

theorem beforeWord_eq_cons {A : Type*} (z : A) (v : Fin (n+1) → A) :
    beforeWord (n+1) z v = Fin.cons (α := fun _ => A) z (Fin.init v) := by
  funext i
  refine Fin.cases rfl (fun k => ?_) i
  simpa [beforeWord, Fin.init] using preceding n v k

theorem read_tickPort (D : Fin d → Bool) (block : ℕ) (params : Fin np → Bool)
    (f : BlockFixing (n+1) (Fin a → Bool) (Fin a → Bool)) (l r : Fin chunks → Fin a → Bool)
    (j : Fin (n+1)) (team : Fin teams) :
    read D f l r ∘ tickPort (nt:=nt) (ns:=ns) block params j team =
      fixingPins (tickPins D block params) f j team := by
  rw [tickPort, comp_fields]
  simp [ApproximatePort.read, tickPins, fixingPins, beforeWord_eq_cons, Function.comp_def]

/-- Decode an external pin of the full collapse evaluator. -/
def port (block : ℕ) (params : Fin np → Bool) :
    FoldInput.Port (n+1) teams (pinCount d nt ns np a) (chunks*a) → ApproximatePort (Fin chunks) d n a
  | .inl ((j,team),k) => tickPort block params j team k
  | .inr (flag,idx) =>
    let p := finProdFinEquiv.symm idx
    if flag then .rightCatalyst p.1 p.2 else .leftCatalyst p.1 p.2

def select (block : ℕ) (params : Fin np → Bool) :
    Fin ((n+1)*teams*pinCount d nt ns np a+2*(chunks*a)) → ApproximatePort (Fin chunks) d n a :=
  port block params ∘ FoldInput.rowMajor.symm

@[simp] theorem select_tick (D : Fin d → Bool) (block : ℕ) (params : Fin np → Bool)
    (f : BlockFixing (n+1) (Fin a → Bool) (Fin a → Bool)) (l r : Fin chunks → Fin a → Bool)
    (j : Fin (n+1)) (team : Fin teams) (k : Fin (pinCount d nt ns np a)) :
    read D f l r (select block params (FoldInput.rowMajor (.inl ((j,team),k)))) =
      fixingPins (tickPins D block params) f j team k := by
  simpa [select, port] using congrFun (read_tickPort D block params f l r j team) k

@[simp] theorem select_boundary (D : Fin d → Bool) (block : ℕ) (params : Fin np → Bool)
    (f : BlockFixing (n+1) (Fin a → Bool) (Fin a → Bool)) (l r : Fin chunks → Fin a → Bool)
    (flag : Bool) (i : Fin chunks) (j : Fin a) :
    read D f l r (select (nt:=nt) (ns:=ns) (teams:=teams) block params
      (FoldInput.rowMajor (.inr (flag,finProdFinEquiv (i,j))))) =
        if flag then r i j else l i j := by
  cases flag <;> simp [select, port, ApproximatePort.read]

end ThreeFlat.Diagonal.ApproximateImage

end OAI
