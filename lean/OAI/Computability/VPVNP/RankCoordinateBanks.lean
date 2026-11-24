import OAI.Computability.VPVNP.RankCoordinateOrdinal

/-!
# Installing ordinal and scalar readers in disjoint auxiliary banks

The public address and result ports are shared with the caller. An injective
map places only the reader's auxiliary stacks in a selected part of the host
bank. A call updates that part in place and preserves every exterior stack,
including the data used by the other coordinate readers.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.FiniteRoutine

variable {K L : Type} [DecidableEq K] [DecidableEq L]

/-- A framed call needs a separate input-size bound only on the exterior
ports. The callee's bounded run already covers every port in its image. -/
theorem BoundedRun.framed_exterior {r : FiniteRoutine K} {ports : K → L} (hp : Function.Injective ports)
    {S A t : ℕ} {s u : Stacks L} {small out : Stacks K} (run : r.BoundedRun S t small out)
    (ext : ∀ j, (∀ i, ports i ≠ j) → (s j).length ≤ A)
    (hin : ∀ i, s (ports i) = small i) (hu : ∀ i, u (ports i) = out i)
    (hout : ∀ j, (∀ i, ports i ≠ j) → u j = s j) : (r.onPorts ports).BoundedRun (max S A) t s u := by
  have h := FiniteRoutine.BoundedRun.onPorts (a := r) hp s (run.enlarge (Nat.le_max_left S A))
    (fun j hj => (ext j hj).trans (Nat.le_max_right S A))
  rwa [installStacks_frame hp hin (fun _ _ => rfl), installStacks_frame hp hu hout] at h

end RAMTape.FiniteRoutine

namespace RankQuery.Stack

open RAMTape

namespace OrdinalRead

variable {K L : Type}

/-- Rename the auxiliary ports while retaining the ordinal and result words. -/
def auxPorts (E : K → L) : Port K → Port L
  | .input => .input
  | .result => .result
  | .aux k => .aux (E k)

/-- Mount an ordinal reader on a new auxiliary bank while retaining its public input and result
ports. -/
def onAux (E : K → L) (read : FiniteRoutine (Port K)) := read.onPorts (auxPorts E)

private theorem auxPorts_injective {E : K → L} (hE : Function.Injective E) :
    Function.Injective (auxPorts E) := by
  intro x y h
  cases x <;> cases y <;> simp_all [auxPorts, hE.eq_iff]

theorem CorrectSpace.onAux [DecidableEq K] [DecidableEq L] {r n w B S A : ℕ}
    {read : FiniteRoutine (Port K)} {g : Fin r → Fin n} {smallReady : Stacks K → Prop} {ready : Stacks L → Prop}
    (hc : CorrectSpace read g w B S smallReady) (E : K → L) (hE : Function.Injective E)
    (project : ∀ s, ready s → smallReady (s ∘ E))
    (preserve : ∀ s out, ready s → smallReady out → ready (installStacks E s out))
    (exterior : ∀ s, ready s → ∀ j, (∀ i, E i ≠ j) → (s j).length ≤ A) :
    CorrectSpace (OrdinalRead.onAux E read) g w B (max S A) ready := by
  intro i s hs
  obtain ⟨t, ht, out, ho, run⟩ := hc i (s ∘ E) (project s hs)
  refine ⟨t, ht, installStacks E s out, preserve s out hs ho, ?_⟩
  apply FiniteRoutine.BoundedRun.framed_exterior (auxPorts_injective hE) run
  · intro k hk
    cases k with
    | input => exact (hk .input rfl).elim
    | result => exact (hk .result rfl).elim
    | aux j => exact exterior s hs j (fun a h => hk (.aux a) (congrArg Port.aux h))
  · intro k; cases k <;> rfl
  · intro k
    cases k with
    | aux a => exact installStacks_at hE s out a
    | _ => rfl
  · intro k hk
    cases k with
    | aux j => exact installStacks_outside s out (fun a h => hk (.aux a) (congrArg Port.aux h))
    | input => rfl
    | result => exact (hk .result rfl).elim

end OrdinalRead

namespace MacaulayRead

variable {K L : Type}

/-- The row and column words and the result stay at their original public ports. -/
def auxPorts (E : K → L) : Port K → Port L
  | .row => .row
  | .col => .col
  | .result => .result
  | .aux k => .aux (E k)

/-- Mount a Macaulay entry reader on a new auxiliary bank while retaining its row, column, and
result ports. -/
def onAux (E : K → L) (read : FiniteRoutine (Port K)) := read.onPorts (auxPorts E)

private theorem auxPorts_injective {E : K → L} (hE : Function.Injective E) :
    Function.Injective (auxPorts E) := by
  intro x y h
  cases x <;> cases y <;> simp_all [auxPorts, hE.eq_iff]

theorem CorrectSpace.onAux [DecidableEq K] [DecidableEq L] {p e n m w v B S A : ℕ}
    {c : SliceArithmetic.Vector p e} {read : FiniteRoutine (Port K)} {M : Matrix (Fin n) (Fin m) (Scalar c)}
    {smallReady : Stacks K → Prop} {ready : Stacks L → Prop}
    (hc : CorrectSpace read M w v B S smallReady) (E : K → L) (hE : Function.Injective E)
    (project : ∀ s, ready s → smallReady (s ∘ E))
    (preserve : ∀ s out, ready s → smallReady out → ready (installStacks E s out))
    (exterior : ∀ s, ready s → ∀ j, (∀ i, E i ≠ j) → (s j).length ≤ A) :
    CorrectSpace (MacaulayRead.onAux E read) M w v B (max S A) ready := by
  intro i j s hs
  obtain ⟨t, ht, out, ho, run⟩ := hc i j (s ∘ E) (project s hs)
  refine ⟨t, ht, installStacks E s out, preserve s out hs ho, ?_⟩
  apply FiniteRoutine.BoundedRun.framed_exterior (auxPorts_injective hE) run
  · intro k hk
    cases k with
    | row => exact (hk .row rfl).elim
    | col => exact (hk .col rfl).elim
    | result => exact (hk .result rfl).elim
    | aux j => exact exterior s hs j (fun a h => hk (.aux a) (congrArg Port.aux h))
  · intro k; cases k <;> rfl
  · intro k
    cases k with
    | aux a => exact installStacks_at hE s out a
    | _ => rfl
  · intro k hk
    cases k with
    | aux j => exact installStacks_outside s out (fun a h => hk (.aux a) (congrArg Port.aux h))
    | row | col => rfl
    | result => exact (hk .result rfl).elim

end MacaulayRead

namespace Coordinate.ThreeBanks

variable {X Y Z : Type}

/-- A disjoint union of three auxiliary stack banks allows the readers to keep their own
working data. -/
abbrev Host (X Y Z : Type) := X ⊕ Y ⊕ Z

/-- Place a port in the first of the three disjoint banks. -/
def left (x : X) : Host X Y Z := .inl x
/-- Place a port in the second bank, separated from the first and third reader workspaces. -/
def middle (y : Y) : Host X Y Z := .inr (.inl y)
/-- Place a port in the third of the three disjoint banks. -/
def right (z : Z) : Host X Y Z := .inr (.inr z)

theorem left_injective : Function.Injective (left (X := X) (Y := Y) (Z := Z)) := Sum.inl_injective
theorem middle_injective : Function.Injective (middle (X := X) (Y := Y) (Z := Z)) :=
  Sum.inr_injective.comp Sum.inl_injective
theorem right_injective : Function.Injective (right (X := X) (Y := Y) (Z := Z)) :=
  Sum.inr_injective.comp Sum.inr_injective

/-- Independent readiness of the two selectors and the scalar reader. -/
def Ready (rx : Stacks X → Prop) (ry : Stacks Y → Prop) (rz : Stacks Z → Prop) (s : Stacks (Host X Y Z)) : Prop :=
  rx (s ∘ left) ∧ ry (s ∘ middle) ∧ rz (s ∘ right)

variable {rx : Stacks X → Prop} {ry : Stacks Y → Prop} {rz : Stacks Z → Prop} {s : Stacks (Host X Y Z)}

theorem project_left (hs : Ready rx ry rz s) : rx (s ∘ left) := hs.1
theorem project_middle (hs : Ready rx ry rz s) : ry (s ∘ middle) := hs.2.1
theorem project_right (hs : Ready rx ry rz s) : rz (s ∘ right) := hs.2.2

private theorem project_install {K L : Type} {E : K → L} (hp : Function.Injective E)
    (base : Stacks L) (out : Stacks K) : installStacks E base out ∘ E = out :=
  funext (installStacks_at hp base out)

private theorem project_other {K L J : Type} {E : K → L} {F : J → L}
    (sep : ∀ i j, E i ≠ F j) (base : Stacks L) (out : Stacks K) :
    installStacks E base out ∘ F = base ∘ F :=
  funext fun j => installStacks_outside base out fun i => sep i j

theorem preserve_left (hs : Ready rx ry rz s) {out : Stacks X} (ho : rx out) :
    Ready rx ry rz (installStacks left s out) := by
  unfold Ready
  rw [project_install left_injective,
    project_other (E := left) (F := middle) (fun _ _ h => by cases h),
    project_other (E := left) (F := right) (fun _ _ h => by cases h)]
  exact ⟨ho, hs.2⟩

theorem preserve_middle (hs : Ready rx ry rz s) {out : Stacks Y} (ho : ry out) :
    Ready rx ry rz (installStacks middle s out) := by
  unfold Ready
  rw [project_install middle_injective,
    project_other (E := middle) (F := left) (fun _ _ h => by cases h),
    project_other (E := middle) (F := right) (fun _ _ h => by cases h)]
  exact ⟨hs.1, ho, hs.2.2⟩

theorem preserve_right (hs : Ready rx ry rz s) {out : Stacks Z} (ho : rz out) :
    Ready rx ry rz (installStacks right s out) := by
  unfold Ready
  rw [project_install right_injective,
    project_other (E := right) (F := left) (fun _ _ h => by cases h),
    project_other (E := right) (F := middle) (fun _ _ h => by cases h)]
  exact ⟨hs.1, hs.2.1, ho⟩

/-- A common component cap bounds every exterior stack of each mounted call. -/
theorem length_le {A : ℕ} (hx : ∀ b, rx b → ∀ k, (b k).length ≤ A)
    (hy : ∀ b, ry b → ∀ k, (b k).length ≤ A) (hz : ∀ b, rz b → ∀ k, (b k).length ≤ A)
    (hs : Ready rx ry rz s) (k : Host X Y Z) : (s k).length ≤ A := by
  rcases k with k | k | k
  · exact hx _ hs.1 k
  · exact hy _ hs.2.1 k
  · exact hz _ hs.2.2 k

end Coordinate.ThreeBanks

end RankQuery.Stack

end VPVNP
end Computability
end OAI
