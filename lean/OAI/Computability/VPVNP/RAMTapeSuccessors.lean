import OAI.Computability.VPVNP.RAMTapeSuccessorDispatch
import OAI.Computability.VPVNP.RAMTapeSuccessorEdge
import OAI.Computability.VPVNP.RAMTapeSuccessorInitial

/-!
# Executing the two successor checks of a RAM processor

One uniform finite stack program examines the site address, reads the outgoing
eight words and then the incoming eight words, and checks both fields. The
first site installs the public initial state. The terminal site emits a false
outgoing-presence flag. The unconsumed incident bits are the sorting fields.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Successors

open BurstRAM RAMLayout RAMSerialization

/-- Outgoing and incoming sides of a site's successor check. -/
inductive Side where
  | send | receive
  deriving DecidableEq

instance : Fintype Side := derive_fintype% _

/-- Shared address, incident, width, cap, and scratch registers together with side-specific
words, flags, and records. -/
inductive Port where
  | address | incident | width | cap | initial | tmp | capTmp | outPresent
  | running (side : Side) | verdict (side : Side) | record (side : Side) | word (side : Side) (i : Fin 8)
  deriving DecidableEq, Fintype

/-- Connect a single-edge reader to the shared incident stacks and the selected side's word,
flag, and record registers. -/
def edgePorts (side : Side) : SuccessorEdge.Port → Port
  | .input => .incident
  | .width => .width
  | .tmp => .tmp
  | .cap => .cap
  | .capTmp => .capTmp
  | .running => .running side
  | .verdict => .verdict side
  | .record => .record side
  | .word i => .word side i

private theorem edgePorts_inj (side : Side) : Function.Injective (edgePorts side) := by
  intro i j h
  cases i <;> cases j <;> simp_all [edgePorts]

/-- Connect initial-state normalization to the public initial word, received state word,
received running bit, and scratch stacks. -/
def initialPorts : SuccessorInitial.Port → Port
  | .initial => .initial
  | .state => .word .receive 2
  | .running => .running .receive
  | .sourceTmp => .tmp
  | .outTmp => .capTmp

private theorem initialPorts_inj : Function.Injective initialPorts := by
  intro i j h
  cases i <;> cases j <;> simp_all [initialPorts]

/-- Install the public initial state at a site with no incoming edge and immediately return at
an interior receive site. -/
def normalizeIfFirst (incoming : Bool) : FiniteRoutine Port :=
  if incoming then .ret else SuccessorInitial.normalize initialPorts

private def emitPresent (outgoing : Bool) : FiniteRoutine Port :=
  FiniteRoutine.ofRoutine (Routine.push Port.outPresent outgoing)

/-- Check outgoing and incoming fields in stream order, normalize the first site's state, and
emit the outgoing-presence bit. -/
def body (outgoing incoming : Bool) : FiniteRoutine Port :=
  (((SuccessorEdge.edge (edgePorts .send) outgoing).followedBy
    (SuccessorEdge.edge (edgePorts .receive) incoming)).followedBy
      (normalizeIfFirst incoming)).followedBy (emitPresent outgoing)

/-- This table is independent of the word length, site count and site identifier. -/
def read : FiniteRoutine Port := SuccessorEnds.dispatch .address .tmp body

variable {w : ℕ}

/-- Register bank after one side's field check, with the unconsumed incident tail and that
side's updated words, record, and flags. -/
def afterEdge (s : Stacks Port) (side : Side) (present : Bool) (bits : Fin (8 * w) → Bool)
    (cap : Word w) (tail : List Bool) : Stacks Port :=
  let row := SuccessorEdge.edgeResult (s ∘ edgePorts side) present bits cap tail
  fun p ↦ match p with
    | .incident => tail
    | .running t => if t = side then row .running else s p
    | .verdict t => if t = side then row .verdict else s p
    | .record t => if t = side then row .record else s p
    | .word t i => if t = side then row (.word i) else s p
    | _ => s p

private theorem edge_runs (s : Stacks Port) (side : Side) (present : Bool) (bits : Fin (8*w) → Bool)
    (cap : Word w) (tail : List Bool) (hin : s .incident = List.ofFn bits ++ tail)
    (hw : s .width = List.replicate w true) (hc : s .cap = BurstRAM.wordBits cap)
    (ht : s .tmp = []) (hu : s .capTmp = []) (hblank : ∀ i, s (.word side i) = []) :
    (SuccessorEdge.edge (edgePorts side) present).Runs (113*w+49) s
      (afterEdge s side present bits cap tail) := by
  have he := SuccessorEdge.edge_runs (edgePorts side) (edgePorts_inj side) present s bits cap tail
    hin hw hc ht hu hblank
  have hf : installStacks (edgePorts side) s
      (SuccessorEdge.edgeResult (s ∘ edgePorts side) present bits cap tail) =
        afterEdge s side present bits cap tail := by
    apply installStacks_frame (edgePorts_inj side)
    · intro k
      cases k <;> simp [afterEdge, edgePorts, SuccessorEdge.edgeResult]
    · intro k hk
      cases k with
      | incident => exact (hk .input rfl).elim
      | running t | verdict t | record t =>
        by_cases h : t = side
        · subst t
          first | exact (hk .running rfl).elim | exact (hk .verdict rfl).elim | exact (hk .record rfl).elim
        · simp [afterEdge, h]
      | word t i =>
        by_cases h : t = side
        · subst t
          exact (hk (.word i) rfl).elim
        · simp [afterEdge, h]
      | _ => rfl
  rwa [hf] at he

/-- Install the public initial word and a true running bit in the incoming registers when the
site has no incoming edge. -/
def afterNormalize (s : Stacks Port) (incoming : Bool) : Stacks Port :=
  if incoming then s else Function.update (Function.update s (.word .receive 2) (s .initial))
    (.running .receive) (true :: (s (.running .receive)).tail)

/-- Step count of first-site normalization, including the single return step when an incoming
edge is present. -/
def normalizeCost (w : ℕ) (incoming : Bool) := if incoming then 1 else 8*w+5

private theorem normalize_runs (s : Stacks Port) (incoming : Bool) (ht : s .tmp = []) (hu : s .capTmp = [])
    (hi : (s .initial).length = w) (hs : (s (.word .receive 2)).length = w) :
    (normalizeIfFirst incoming).Runs (normalizeCost w incoming) s (afterNormalize s incoming) := by
  cases incoming with
  | false => exact SuccessorInitial.normalize_runs initialPorts_inj s ht hu hi hs
  | true => exact Routine.runs_ret s

/-- Final register bank after both edge checks, first-site normalization, and emission of the
outgoing-presence bit. -/
def finish (s : Stacks Port) (outgoing incoming : Bool) (sent received : Fin (8*w) → Bool)
    (cap : Word w) (suffix : List Bool) : Stacks Port :=
  let a := afterEdge s .send outgoing sent cap (List.ofFn received ++ suffix)
  let b := afterEdge a .receive incoming received cap suffix
  let c := afterNormalize b incoming
  Function.update c .outPresent (outgoing :: c .outPresent)

/-- Step count for the site-address scan, both eight-word successor checks, first-site
normalization, and outgoing flag emission. -/
def steps (d w : ℕ) (incoming : Bool) : ℕ :=
  4*d+3 + (((113*w+49)+(113*w+49)) + normalizeCost w incoming + 1)

theorem steps_le (d w : ℕ) (incoming : Bool) : steps d w incoming ≤ 4*d+234*w+107 := by
  cases incoming <;> simp [steps, normalizeCost] <;> omega

/-- Both outgoing and incoming words are preserved for the call loop. The two
record payloads are independently available to the sorted predecessor check.
The result includes a canonicality flag for each raw field, even if malformed. -/
theorem read_runs {d : ℕ} (s : Stacks Port) (v : Word d) (cap initial : Word w)
    (sent received : Fin (8*w) → Bool) (suffix : List Bool)
    (hv : s .address = BurstRAM.wordBits v)
    (hin : s .incident = List.ofFn sent ++ (List.ofFn received ++ suffix))
    (hw : s .width = List.replicate w true) (hc : s .cap = BurstRAM.wordBits cap)
    (hi : s .initial = BurstRAM.wordBits initial) (ht : s .tmp = []) (hu : s .capTmp = [])
    (hblank : ∀ side i, s (.word side i) = []) :
    let outgoing := decide (v.val + 1 < 2 ^ d)
    let incoming := decide (0 < v.val)
    read.Runs (steps d w incoming) s (finish s outgoing incoming sent received cap suffix) := by
  intro outgoing incoming
  apply SuccessorEnds.dispatch_runs .address .tmp (by decide) body s v hv ht
  let a := afterEdge s .send outgoing sent cap (List.ofFn received ++ suffix)
  let b := afterEdge a .receive incoming received cap suffix
  have ha := edge_runs s .send outgoing sent cap _ hin hw hc ht hu (hblank .send)
  have hb := edge_runs a .receive incoming received cap suffix rfl hw hc ht hu (hblank .receive)
  have hn := normalize_runs b incoming ht hu (show (s .initial).length = w from hi ▸ length_wordBits initial)
    (show (b (.word .receive 2)).length = w from BurstRAM.length_wordBits _)
  exact (((ha.followedBy hb).followedBy hn).followedBy (Routine.runs_push Port.outPresent outgoing (afterNormalize b incoming)))

/-- The incident vector in the precise layout of (10.1) supplies both fields
without a bit lookup oracle. -/
theorem read_incident_runs {d H : ℕ} (s : Stacks Port) (v : Word d) (cap initial : Word w)
    (inc : Fin (width d H w) → Bool)
    (hv : s .address = BurstRAM.wordBits v) (hin : s .incident = List.ofFn inc)
    (hw : s .width = List.replicate w true) (hc : s .cap = BurstRAM.wordBits cap)
    (hi : s .initial = BurstRAM.wordBits initial) (ht : s .tmp = []) (hu : s .capTmp = [])
    (hblank : ∀ side i, s (.word side i) = []) :
    read.Runs (steps d w (decide (0 < v.val))) s
      (finish s (decide (v.val+1 < 2^d)) (decide (0 < v.val))
        (fun j ↦ inc (offset d H w (.inl (0, j)))) (fun j ↦ inc (offset d H w (.inl (1, j))))
        cap ((List.ofFn inc).drop (16*w))) :=
  read_runs s v cap initial _ _ _ hv
    (hin.trans (by simpa only [List.append_assoc] using SuccessorFields.incident_prefix inc)) hw hc hi ht hu hblank

end RAMTape.Successors

end VPVNP
end Computability
end OAI
