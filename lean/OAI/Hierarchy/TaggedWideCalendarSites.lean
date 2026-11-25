import OAI.Hierarchy.TaggedWideHost
import OAI.Hierarchy.TaggedWirePartyTrace

namespace OAI
/-! # Wiring the entry, chronological signed transitions and terminal site

All dates and all sites use one public pin type. A date's output state
is the next date's input in the chronological state assignment.
-/

noncomputable section
namespace Hierarchy.Tagged.WideCalendarSites
open ThreeFlat Routing
open LinearAlgebra.SpectralBooks ChordGraph
open WireTelescope WireTelescope.CalendarTape ProtocolRAM.Calendar
open scoped Classical BigOperators

variable {F : Type*} [Field F] {V : Type} [Fintype V] {n S : ℕ}

abbrev Net (F : Type*) (V : Type) [Fintype V] := BitNetwork F (Fintype.card V)

def components (entry finish : Net F V) (row : Fin n → Net F V) : Option (Option (Fin n)) → Net F V
  | none => finish
  | some none => entry
  | some (some j) => row j

/-- A static physical network for one site's full tape. -/
def site (entry finish : Net F V) (row : Fin n → Net F V) : Net F V :=
  WideHost.localFamily (A:=fun _ => V) (components entry finish row) (fun _ i => .inl i)

theorem site_value (entry finish : Net F V) (row : Fin n → Net F V) (v : V→Bool) :
    TypedWiring.value (site entry finish row) v =
      TypedWiring.value finish v * (TypedWiring.value entry v * ∏ j, TypedWiring.value (row j) v) := by
  rw [site, WideHost.localFamily_eval]
  simp only [Fintype.prod_option, components]
  rfl

omit [Field F] in
theorem site_size (entry finish : Net F V) (row : Fin n → Net F V) :
    (site entry finish row).cells + (site entry finish row).internal =
      finish.cells + finish.internal + ((entry.cells + entry.internal) + ∑ j, ((row j).cells+(row j).internal)) := by
  rw [site, WideHost.localFamily_size]
  simp only [Fintype.sum_option, components]

def network (entry finish : Fin S → Net F V) (row : Fin S → Fin n → Net F V) : Net F V :=
  WideHost.localFamily (A:=fun _ => V) (fun s => site (entry s) (finish s) (row s)) (fun _ i => .inl i)

theorem network_value (entry finish : Fin S → Net F V) (row : Fin S → Fin n → Net F V) (v : V→Bool) :
    TypedWiring.value (network entry finish row) v =
      ∏ s, TypedWiring.value (site (entry s) (finish s) (row s)) v := by
  rw [network, WideHost.localFamily_eval]
  rfl

omit [Field F] in
theorem network_size (entry finish : Fin S → Net F V) (row : Fin S → Fin n → Net F V) :
    (network entry finish row).cells + (network entry finish row).internal =
      ∑ s, ((finish s).cells + (finish s).internal + (((entry s).cells + (entry s).internal) +
        ∑ j, ((row s j).cells + (row s j).internal))) := by
  rw [network, WideHost.localFamily_size]
  exact Finset.sum_congr rfl (fun s _ => site_size (entry s) (finish s) (row s))

variable {X : Type} (slot : Event → Slot X) (wire : X → Widths S)
    (M : ∀ e x (c : (slot e).choice x), SiteMatrix (State (wire x)) (State (wire ((slot e).next x c))) F)

/-- The last actual state retained by this one chronological site assignment. -/
def last (s : Fin S) : (es : List Event) → (x : X) → (p : Path slot es x) →
    State (wire x) s → PartyStates slot wire s es x p → State (wire (terminal slot es x p)) s
  | [], _, _, start, _ => start
  | e::es, x, p, _, states => last s es ((slot e).next x p.1) p.2 states.1 states.2

/-- Each fixed date block is evaluated at the two states it connects. -/
def Reads (s : Fin S) : (es : List Event) → (x : X) → (p : Path slot es x) →
    State (wire x) s → PartyStates slot wire s es x p → (Fin es.length → F) → Prop
  | [], _, _, _, _, _ => True
  | e::es, x, p, start, states, obs =>
    obs 0 = M e x p.1 s start states.1 ∧
    Reads s es ((slot e).next x p.1) p.2 states.1 states.2 (fun j => obs j.succ)

theorem product_steps (s : Fin S) (es : List Event) (x : X) (p : Path slot es x)
    (finish : State (wire (terminal slot es x p)) s → F)
    (start : State (wire x) s) (states : PartyStates slot wire s es x p) (obs : Fin es.length → F)
    (read : Reads slot wire M s es x p start states obs) :
    finish (last slot wire s es x p start states) * ∏ j, obs j =
      partyWeight slot wire M s es x p finish start states := by
  induction es generalizing x with
  | nil => simp [last,partyWeight]
  | cons e es ih =>
    change _ * (∏ j : Fin (es.length+1),obs j) = _
    rw [Fin.prod_univ_succ,read.1]
    change finish (last slot wire s es ((slot e).next x p.1) p.2 states.1 states.2) *
      (M e x p.1 s start states.1 * ∏ j : Fin es.length, obs j.succ) = _
    rw [mul_left_comm, ih _ p.2 finish states.1 states.2 _ read.2]
    exact mul_comm _ _

theorem site_on_state (s : Fin S) (es : List Event) (x : X) (p : Path slot es x)
    (start : State (wire x) s) (states : PartyStates slot wire s es x p)
    (finish : State (wire (terminal slot es x p)) s → F) (first : F)
    (E T : Net F V) (row : Fin es.length→Net F V) (v : V→Bool)
    (entryRead : TypedWiring.value E v=first)
    (endRead : TypedWiring.value T v=finish (last slot wire s es x p start states))
    (steps : Reads slot wire M s es x p start states (fun j=>TypedWiring.value (row j) v)) :
    TypedWiring.value (site E T row) v = partyWeight slot wire M s es x p finish start states * first := by
  rw [site_value,entryRead,endRead,← product_steps slot wire M s es x p finish start states _ steps]
  ring

end Hierarchy.Tagged.WideCalendarSites

end
end OAI
