import OAI.ThreeFlat.Diagonal.TraceCircuitArray

namespace OAI
/-! # Dense bit addresses for fixed endpoints and internal block states

External halves and the auxiliary word are concatenated in a single state.
Each intermediate state is guessed once and serves both blocks that meet there.
-/

namespace ThreeFlat.Diagonal.BoundaryWire

open TraceCircuit

abbrev State (chunks a : ℕ) := (Bool → Fin chunks → Fin a → Bool) × (Fin a → Bool)
def stateWidth (chunks a : ℕ) := (chunks*a + chunks*a) + a

def stateEquiv (chunks a : ℕ) : State chunks a ≃ (Fin (stateWidth chunks a) → Bool) :=
  let half := blocks chunks a
  let halves := (Equiv.boolArrowEquivProd _).trans
    ((Equiv.prodCongr half half).trans (Fin.appendEquiv _ _))
  (Equiv.prodCongr halves (Equiv.refl _)).trans (Fin.appendEquiv _ _)

variable {chunks a d t n : ℕ}

theorem stateEquiv_apply (s : State chunks a) :
    stateEquiv chunks a s = Fin.append
      (Fin.append (blocks chunks a (s.1 false)) (blocks chunks a (s.1 true))) s.2 := rfl

def chunkSite (half : Bool) (slot : Fin chunks) (bit : Fin a) : Fin (stateWidth chunks a) :=
  (if half then Fin.natAdd (chunks*a) (finProdFinEquiv (slot,bit))
   else (finProdFinEquiv (slot,bit)).castAdd (chunks*a)).castAdd a

def auxSite (chunks : ℕ) (bit : Fin a) : Fin (stateWidth chunks a) :=
  Fin.natAdd (chunks*a + chunks*a) bit

@[simp] theorem stateEquiv_chunkSite (s : State chunks a) (half : Bool)
    (slot : Fin chunks) (bit : Fin a) :
    stateEquiv chunks a s (chunkSite half slot bit) = s.1 half slot bit := by
  cases half <;> simp only [stateEquiv_apply, chunkSite, Bool.false_eq_true, ite_false, ite_true,
    Fin.append_left, Fin.append_right, blocks_at]

@[simp] theorem stateEquiv_auxSite (s : State chunks a) (bit : Fin a) :
    stateEquiv chunks a s (auxSite chunks bit) = s.2 bit := by
  simp only [stateEquiv_apply, auxSite, Fin.append_right]

def pinWidth (chunks a d : ℕ) := d + (stateWidth chunks a + stateWidth chunks a)

def pinBits (D : Fin d → Bool) (x y : State chunks a) : Fin (pinWidth chunks a d) → Bool :=
  Fin.append D (Fin.append (stateEquiv chunks a x) (stateEquiv chunks a y))

def hiddenWidth (chunks a t n : ℕ) := t*stateWidth chunks a + (t+1)*(n*a)

abbrev Guesses (chunks a t n : ℕ) :=
  (Fin t → State chunks a) × (Fin (t+1) → Fin n → Fin a → Bool)

def guessEquiv (chunks a t n : ℕ) : Guesses chunks a t n ≃ (Fin (hiddenWidth chunks a t n) → Bool) :=
  let states := (Equiv.piCongrRight (fun _ : Fin t => stateEquiv chunks a)).trans
    (blocks t (stateWidth chunks a))
  let interior := (Equiv.piCongrRight (fun _ : Fin (t+1) => blocks n a)).trans
    (blocks (t+1) (n*a))
  (Equiv.prodCongr states interior).trans (Fin.appendEquiv _ _)

theorem guessEquiv_apply (g : Guesses chunks a t n) :
    guessEquiv chunks a t n g = Fin.append
      (blocks t (stateWidth chunks a) (fun i => stateEquiv chunks a (g.1 i)))
      (blocks (t+1) (n*a) (fun i => blocks n a (g.2 i))) := rfl

abbrev Source (chunks a t n d : ℕ) := BitSource (hiddenWidth chunks a t n) (pinWidth chunks a d)

def publicSource (j : Fin d) : Source chunks a t n d :=
  .pin (j.castAdd (stateWidth chunks a + stateWidth chunks a))

private def endpointSource (right : Bool) (j : Fin (stateWidth chunks a)) : Source chunks a t n d :=
  .pin (Fin.natAdd d (if right then Fin.natAdd (stateWidth chunks a) j else j.castAdd _))

private def stateSource (i : Fin t) (j : Fin (stateWidth chunks a)) : Source chunks a t n d :=
  .hidden ((finProdFinEquiv (i,j)).castAdd ((t+1)*(n*a)))

def oldSource (i : Fin (t+1)) (j : Fin (stateWidth chunks a)) : Source chunks a t n d :=
  Fin.cons (α := fun _ => Source chunks a t n d) (endpointSource false j) (fun s => stateSource s j) i

def newSource (i : Fin (t+1)) (j : Fin (stateWidth chunks a)) : Source chunks a t n d :=
  Fin.snoc (α := fun _ => Source chunks a t n d) (fun s => stateSource s j) (endpointSource true j) i

def interiorSource (i : Fin (t+1)) (k : Fin n) (j : Fin a) : Source chunks a t n d :=
  .hidden (Fin.natAdd (t*stateWidth chunks a) (finProdFinEquiv (i, finProdFinEquiv (k,j))))

variable (D : Fin d → Bool) (x y : State chunks a) (g : Guesses chunks a t n)

@[simp] theorem publicSource_read (j : Fin d) :
    (publicSource j).read (guessEquiv chunks a t n g) (pinBits D x y) = D j := by
  simp [publicSource, BitSource.read, pinBits]

private theorem stateSource_read (i : Fin t) (j : Fin (stateWidth chunks a)) :
    (stateSource i j).read (guessEquiv chunks a t n g) (pinBits D x y) =
      stateEquiv chunks a (g.1 i) j := by
  simp only [stateSource, BitSource.read, guessEquiv_apply, Fin.append_left, blocks_at]

@[simp] theorem oldSource_read (i : Fin (t+1)) (j : Fin (stateWidth chunks a)) :
    (oldSource i j).read (guessEquiv chunks a t n g) (pinBits D x y) =
      stateEquiv chunks a (Fin.cons (α := fun _ => State chunks a) x g.1 i) j := by
  refine Fin.cases ?_ (fun s => ?_) i
  · simp [oldSource, endpointSource, BitSource.read, pinBits]
  · simpa [oldSource] using stateSource_read D x y g s j

@[simp] theorem newSource_read (i : Fin (t+1)) (j : Fin (stateWidth chunks a)) :
    (newSource i j).read (guessEquiv chunks a t n g) (pinBits D x y) =
      stateEquiv chunks a (Fin.snoc (α := fun _ => State chunks a) g.1 y i) j := by
  refine Fin.lastCases ?_ (fun s => ?_) i
  · simp only [newSource, Fin.snoc_last, endpointSource, ite_true, BitSource.read, pinBits,
      Fin.append_right]
  · simpa [newSource] using stateSource_read D x y g s j

@[simp] theorem interiorSource_read (i : Fin (t+1)) (k : Fin n) (j : Fin a) :
    (interiorSource i k j).read (guessEquiv chunks a t n g) (pinBits D x y) = g.2 i k j := by
  simp only [interiorSource, BitSource.read, guessEquiv_apply, Fin.append_right, blocks_at]

end ThreeFlat.Diagonal.BoundaryWire

end OAI
