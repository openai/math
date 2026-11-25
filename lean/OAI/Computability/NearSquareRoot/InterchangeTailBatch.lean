import OAI.Computability.NearSquareRoot.BoundedBranch
import OAI.Computability.IntegerMultiplication.Code.Fold

/-! # Batching successive full-stream recursive interchanges

A single control loop consumes a forest of physical headers, one per call.
It keeps the remaining headers on register one and hands the only copy of the
current payload to the child. Each header crosses between registers twice
over the entire batch. The right-hand jump reuses the loop's continuation.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeBatch

open IntegerMultiplication IntegerMultiplication.Code Space

/-- Each reply is the physical payload of the following call, including the
first and last stream in the statement. -/
inductive Chain {X : Type*} (payload reply : X → Tree) : Tree → List X → Tree → Prop
  | nil (x : Tree) : Chain payload reply x [] x
  | cons (q : X) {tail : List X} {y : Tree} (rest : Chain payload reply (reply q) tail y) :
      Chain payload reply (payload q) (q :: tail) y

/-- No element of the schedule contains a payload tree. -/
abbrev headers {X : Type*} (header : X → Tree) (qs : List X) := Task.forest header qs

private def openBatch : Cmd :=
  splitRoot 0 (fun _ => .pass) (move 0 1 2)

private def prepare : Cmd := (move 1 0 2).join (pack 0)

/-- The pending schedule stays in register one even when the child uses that
register for temporary trees. A child's certificate is polymorphic in its deck. -/
def loop (invoke : Cmd) : Cmd :=
  splitRoot 1 (fun _ => .pass) (prepare.join (invoke.join (.again 0)))

def batch (invoke : Cmd) : Cmd := openBatch.join (.tie (loop invoke))

/-- Local preparation and recursive work share the same live-space allowance.
The child is charged only for the still-parked headers and its own work. -/
def dataSpace (volume headerSize childSpace : ℕ) :=
  max (volume + 100*(headerSize+1)) (headerSize + childSpace)

/-- Only the call which returns to the next iteration saves a continuation. -/
def returnSpace (headerSize childDepth : ℕ) :=
  max (100*(headerSize+1)) (childDepth+1)

private theorem run_loop {X : Type*} (header payload reply : X → Tree)
    (time : X → ℕ) (invoke : Cmd) (env : Env) (V H S D : ℕ)
    {x y : Tree} {qs : List X} (chain : Chain payload reply x qs y)
    (hx : ∀ q ∈ qs, (payload q).count ≤ V) (hy : y.count ≤ V)
    (hsize : (headers header qs).count ≤ H)
    (child : ∀ q ∈ qs, ∀ d base, DeckCap base d →
      BoundedFits (loop invoke :: env) invoke
        (pile 0 (.fork (header q) (payload q)) d) (pile 0 (reply q) d)
        (time q) (base + S) D)
    (r : Code.Deck) (base : ℕ) (hr : DeckCap base r) :
    BoundedFits (loop invoke :: env) (loop invoke)
      (pile 1 (headers header qs) (pile 0 x r)) (pile 0 y r)
      ((qs.map time).sum + 60*(headers header qs).count)
      (base + dataSpace V H S) (returnSpace H D) := by
  have hw : V + 100*(H+1) ≤ dataSpace V H S := le_max_left ..
  have hc : H + S ≤ dataSpace V H S := le_max_right ..
  have rd : 100*(H+1) ≤ returnSpace H D := le_max_left ..
  have cd : D+1 ≤ returnSpace H D := le_max_right ..
  induction chain with
  | nil x =>
    have raw := hr.pile 0 x
    have tag := raw.pile 1 (.atom false)
    refine (BoundedFits.bit (c := fun _ => .pass) (b := false)
      (BoundedFits.pass (raw.mono (by omega)))
      (tag.mono (by simp only [Tree.count]; omega)) (by omega)).mono ?_ le_rfl le_rfl
    simp [headers,Tree.count]
  | @cons q qs y rest ih =>
    let tail := headers header qs
    let Γ := loop invoke :: env
    let cap := base + dataSpace V H S
    have ht : (header q).count + tail.count + 1 ≤ H := by
      simpa only [headers, Task.forest_cons, Tree.count, tail] using hsize
    have hv := hx q List.mem_cons_self
    have Htail : (headers header qs).count ≤ H := by change tail.count ≤ H; omega
    have next := ih (fun k hk => hx k (List.mem_cons_of_mem _ hk)) hy Htail
      (fun k hk => child k (List.mem_cons_of_mem _ hk))
    have saved := hr.pile 1 tail
    have call := child q List.mem_cons_self _ _ saved
    have call' := call.mono le_rfl (show base + tail.count + S ≤ cap by dsimp [cap]; omega) le_rfl
    have rr := (hr.pile 0 (payload q)).pile 1 tail
    have loaded := rr.pile 1 (header q)
    have shell := (hr.pile 0 (payload q)).pile 1 (.fork (header q) tail)
    have trans : Fits Γ prepare (pile 1 (header q) (pile 1 tail (pile 0 (payload q) r)))
        (pile 0 (.fork (header q) (payload q)) (pile 1 tail r)) (42*(header q).count+3) := by
      have mv := fits_move (i := 1) (j := 0) (u := 2) (by decide) (by decide)
        (header q) Γ (pile 1 tail (pile 0 (payload q) r))
      have close := fits_pack (header q) (payload q) (pile 1 tail r) 0 Γ
      rw [pile_comm 0 (payload q) r 1 tail (by decide)] at close
      exact mv.join close
    have prep := BoundedFits.of_fits trans (cap := cap) (depth := 42*(header q).count+3)
      (fun j => by have u := loaded j; dsimp only [cap]; omega) le_rfl
    rw [← pile_comm 0 (reply q) r 1 tail (by decide)] at next
    have ret := next.again0
    have calls := call'.join ret cd
    have body := prep.join calls (by omega)
    refine (BoundedFits.pair (c := fun _ => .pass) body
      (shell.mono (by simp only [Tree.count]; dsimp only [cap]; omega)) (by omega)).mono ?_
      le_rfl le_rfl
    simp only [headers, Task.forest_cons, Tree.count, List.map_cons, List.sum_cons, tail] at *
    omega

/-- A fixed batch command, for an arbitrary runtime-length header list.
The non-child time is linear in the total serialized header length. Peak
space takes a maximum between local processing and the child with its
pending headers. It is independent of the number of preceding calls. -/
theorem run_batch {X : Type*} (header payload reply : X → Tree)
    (time : X → ℕ) (invoke : Cmd) (env : Env) (V S D : ℕ)
    {x y : Tree} {qs : List X} (chain : Chain payload reply x qs y)
    (hx : ∀ q ∈ qs, (payload q).count ≤ V) (hy : y.count ≤ V)
    (child : ∀ q ∈ qs, ∀ d base, DeckCap base d →
      BoundedFits (loop invoke :: env) invoke
        (pile 0 (.fork (header q) (payload q)) d) (pile 0 (reply q) d)
        (time q) (base + S) D)
    (r : Code.Deck) (base : ℕ) (hr : DeckCap base r) :
    BoundedFits env (batch invoke) (pile 0 (.fork (headers header qs) x) r) (pile 0 y r)
      ((qs.map time).sum + 110*((headers header qs).count+1))
      (base + dataSpace V (headers header qs).count S)
      (returnSpace (headers header qs).count D) := by
  let h := headers header qs
  have hV : x.count ≤ V := by cases chain with
    | nil => exact hy
    | cons q => exact hx q List.mem_cons_self
  have opened : Fits env openBatch (pile 0 (.fork h x) r) (pile 1 h (pile 0 x r))
      (42*h.count+4) :=
    fits_pair (fits_move (i:=0) (j:=1) (u:=2) (by decide) (by decide) h env (pile 0 x r))
  have work : V + 100*(h.count+1) ≤ dataSpace V h.count S := le_max_left ..
  have depth : 100*(h.count+1) ≤ returnSpace h.count D := le_max_left ..
  have pre := BoundedFits.of_fits opened (cap := base+dataSpace V h.count S)
    (depth := 42*h.count+4) (fun i => by
      have := hr.pile 0 (.fork h x) i
      simp only [Tree.count] at this
      omega) le_rfl
  have execute := run_loop header payload reply time invoke env V h.count S D
    chain hx hy le_rfl child r base hr
  exact (pre.join execute.tie (by omega)).mono (by dsimp only [h] at *; omega) le_rfl le_rfl

end InterchangeBatch

end NearSquareRoot
end Computability
end OAI
