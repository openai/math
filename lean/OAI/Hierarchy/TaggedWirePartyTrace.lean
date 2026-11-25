import OAI.Hierarchy.TaggedWireMatrixTrace

namespace OAI
/-! # A single physical site's signed product over all of its chronological states -/

noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ProtocolRAM.Calendar
open scoped Classical BigOperators

variable {S : ℕ} {F : Type*} [Field F] {X : Type} (slot : Event→Slot X) (wire : X→Widths S)
variable (M : ∀e x (a : (slot e).choice x),SiteMatrix (State (wire x)) (State (wire ((slot e).next x a))) F)

def PartyStates (s : Fin S) : (es : List Event)→(x : X)→Path slot es x→Type
  | [],_,_=>Unit
  | e::es,x,p=>State (wire ((slot e).next x p.1)) s × PartyStates s es ((slot e).next x p.1) p.2

instance partyFinite (s : Fin S) : ∀ es x p,Fintype (PartyStates slot wire s es x p)
  | [],_,_=>inferInstanceAs (Fintype Unit)
  | e::es,x,p=>
    letI := partyFinite s es ((slot e).next x p.1) p.2
    inferInstanceAs (Fintype (State (wire ((slot e).next x p.1)) s × PartyStates slot wire s es _ p.2))

def partyWeight (s : Fin S) : (es : List Event)→(x : X)→(p : Path slot es x)→
    (State (wire (terminal slot es x p)) s→F)→State (wire x) s→PartyStates slot wire s es x p→F
  | [],_,_,finish,v,_=>finish v
  | e::es,x,p,finish,v,t=>partyWeight s es ((slot e).next x p.1) p.2 finish t.1 t.2 * M e x p.1 s v t.1

theorem party_sum (s : Fin S) (es : List Event) (x : X) (p : Path slot es x)
    (finish : State (wire (terminal slot es x p)) s→F) (v : State (wire x) s) :
    (∑z,finish z * matrix slot wire M es x p s v z)=
      ∑t : PartyStates slot wire s es x p,partyWeight slot wire M s es x p finish v t := by
  induction es generalizing x with
  | nil=>
    change (∑z,finish z * (if z=v then 1 else 0))=∑_ : Unit,finish v
    simp only [Fintype.sum_unique,mul_ite,mul_one,mul_zero]
    refine (Finset.sum_eq_single v ?_ ?_).trans (ite_eq_left rfl)
    · intro z _ different
      exact ite_eq_right different
    · intro missing
      exact (missing (Finset.mem_univ v)).elim
  | cons e es ih=>
    obtain ⟨a,p⟩ := p
    let y := (slot e).next x a
    change (∑z,finish z*(∑m, matrix slot wire M es y p s m z*M e x a s v m))=
      ∑t : State (wire y) s × PartyStates slot wire s es y p,
        partyWeight slot wire M s es y p finish t.1 t.2 * M e x a s v t.1
    rw [Fintype.sum_prod_type]
    simp_rw [←Finset.sum_mul,←ih y p finish]
    simp only [Finset.mul_sum,Finset.sum_mul,mul_assoc]
    exact Finset.sum_comm

/-- Both neighboring operations at every physical time boundary receive
one and the same edge word. All independent native terminal edge words
are left open at this point. -/
theorem party_kernel {x₀ : X} {A Z : Fin S→Type} (entry : SiteMatrix A (State (wire x₀)) F)
    (s : Fin S) (es : List Event) (p : Path slot es x₀)
    (exit : SiteMatrix (State (wire (terminal slot es x₀ p))) Z F)
    [∀i,Fintype (Z i)] (v : A s) (z : Z s) :
    (SiteMatrix.compose entry (SiteMatrix.compose (matrix slot wire M es x₀ p) exit)) s v z =
      ∑t : State (wire x₀) s × PartyStates slot wire s es x₀ p,
        partyWeight slot wire M s es x₀ p (fun u=>exit s u z) t.1 t.2 * entry s v t.1 := by
  rw [Fintype.sum_prod_type]
  unfold SiteMatrix.compose
  simp_rw [party_sum slot wire M s es x₀ p,Finset.sum_mul]

end Hierarchy.WireTelescope.CalendarTape

end
end OAI
