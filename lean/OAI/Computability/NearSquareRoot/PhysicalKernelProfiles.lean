import OAI.Computability.NearSquareRoot.FixedCandidateRowRelease
import OAI.Computability.NearSquareRoot.SynchronizedPermutationBudgetDispatch

/-! # Combining the actual time and space profiles of the six transport programs

Both CRT directions are run once at each multiplication. Within each Fourier
word the per-row clock covers its permutation and Walsh directions. A full
CRT time bound is therefore kept out of the per-row clock. Peak space can be
shared by all six programs.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate

open IntegerMultiplication Code DigitPacking FixedPoint FixedLayer SynchronizedLayers
  SynchronizedPermutationBudget Filter

inductive TransportKind
  | crt (inverse : Bool)
  | permutation (adjoint : Bool)
  | walsh (adjoint : Bool)
  deriving DecidableEq

namespace TransportKind

def all : List TransportKind :=
  [.crt false,.crt true,.permutation false,.permutation true,.walsh false,.walsh true]

theorem mem_all (k : TransportKind) : k ∈ all := by
  cases k with
  | crt b => cases b <;> decide
  | permutation b => cases b <;> decide
  | walsh b => cases b <;> decide

def perRow {P : Type} (ticks : TransportKind → P → ℕ → ℕ) : TransportKind → P → ℕ → ℕ
  | .crt _,_,_ => 0
  | .permutation d,p,n => ticks (.permutation d) p n
  | .walsh d,p,n => ticks (.walsh d) p n

end TransportKind

/-- An input-length estimate for an entire forward or inverse CRT, including
every stage of its directory. -/
def RouteBound (γ : ℝ) (clock : ℕ → ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, (clock n : ℝ) ≤ C*n*logScale n^γ

theorem RouteBound.add {γ : ℝ} {f g : ℕ → ℕ} (hf : RouteBound γ f) (hg : RouteBound γ g) :
    RouteBound γ (fun n => f n+g n) := by
  obtain ⟨C,hC,fc⟩ := hf
  obtain ⟨D,hD,gc⟩ := hg
  refine ⟨C+D,by positivity,?_⟩
  filter_upwards [fc,gc] with n a b
  push_cast
  calc
    _ ≤ _ := add_le_add a b
    _ = _ := by ring

set_option maxHeartbeats 2200000 in
/-- Assemble the common tape machine from independently costed transport
files. The joint good tuple can be selected non-effectively in this estimate
because all tuple files are already executed by the same effective scheduler. -/
theorem uniform_of_profiles {P : Type} [Primcodable P] [Inhabited P]
    (K : P → ℕ) (hK : Computable K) (hN : ∀ p,2 ≤ K p)
    (hv : ∀ p (i : LargeInput (K p)), Directory i.val.width)
    (hd : ∀ p (i : LargeInput (K p)),4 ≤ (box i.val.width).length)
    (hk : ∀ p (i : LargeInput (K p)),1024 ≤ addressBits i.val.width)
    (space time : TransportKind → P → ℕ → ℕ)
    (crt : EffectiveCRTAt K (space (.crt false)) (time (.crt false)) (fun p i => route (hv p i)))
    (undo : EffectiveCRTAt K (space (.crt true)) (time (.crt true)) (fun p i => afterInverseCRT (hv p i)))
    (perm : ∀ d, EffectiveImplementsAt (fun p (i : LargeInput (K p)) => i.val.width) hv (fun _ _ => d) hd
      (space (.permutation d)) (time (.permutation d)) .permutation)
    (walsh : ∀ d, EffectiveImplementsAt (fun p (i : LargeInput (K p)) => i.val.width) hv (fun _ _ => d) hd
      (space (.walsh d)) (time (.walsh d)) .walsh)
    (good : ∀ j : ℕ, ∃ p : P, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < (1:ℝ)/2+1/(j+2:ℝ) ∧
      (∀ b, LinearArena (space b p)) ∧
      (∀ d,RouteBound ((1:ℝ)/2+1/(j+2:ℝ)) (time (.crt d) p)) ∧
      (∀ d,RowClock ρ (time (.permutation d) p)) ∧ (∀ d,RowClock ρ (time (.walsh d) p))) :
    UniformMultiplicationSpec := by
  let tags := TransportKind.all
  let tick := TransportKind.perRow time
  let A := commonArena tags space
  let u := commonClock tags space tick
  let v (p : P) (n : ℕ) := time (.crt false) p n + time (.crt true) p n
  have prices (k : TransportKind) (p : P) (n : ℕ) :=
    individual_bounds tags (TransportKind.mem_all k) space tick p n
  apply uniformMultiplicationSpec_of_row_guesses K hK hN hv hd hk A v u
    (fun p n => (common_bounds tags space tick p n).1)
    (fun p i => (common_bounds tags space tick p i.val.width).2.1)
    (fun p i => (common_bounds tags space tick p i.val.width).2.2)
  · exact crt.mono (fun _ _ => Nat.le_add_right ..) (fun p e => (prices (.crt false) p e.1.val.width).1)
  · exact undo.mono (fun _ _ => Nat.le_add_left ..) (fun p e => (prices (.crt true) p e.1.val.width).1)
  · intro d
    exact promote_row _ hv _ hd .permutation tags (TransportKind.mem_all (.permutation d)) space tick (perm d)
  · intro d
    exact promote_row _ hv _ hd .walsh tags (TransportKind.mem_all (.walsh d)) space tick (walsh d)
  · intro j
    obtain ⟨p,ρ,hρ,lt,lin,r,pm,w⟩ := good j
    have rt (b : TransportKind) : RowClock ρ (tick b p) := by
      cases b with
      | crt d => exact ⟨0,le_rfl,0,Eventually.of_forall (fun n => by simp [tick,TransportKind.perRow,integerBudget])⟩
      | permutation d => exact pm d
      | walsh d => exact w d
    obtain ⟨hs,ht⟩ := common_good tags space tick p hρ (fun b _ => lin b) (fun b _ => rt b)
    exact ⟨p,ρ,hρ,lt,hs,(r false).add (r true),ht⟩

end FixedCandidate

end NearSquareRoot
end Computability
end OAI
