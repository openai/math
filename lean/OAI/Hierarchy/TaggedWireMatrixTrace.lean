import OAI.Hierarchy.TaggedWireCalendarTape
import OAI.Hierarchy.TaggedWireSiteMatrix

namespace OAI
/-! # Signed chronological contractions for the literal physical site operators -/

noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ProtocolRAM.Calendar
open scoped Classical BigOperators

variable {F : Type*} [Field F] {S : ℕ}
namespace CalendarTape

variable {X : Type} (slot : Event→Slot X) (wire : X→Widths S)

abbrev Layer (x : X) := ∀i,State (wire x) i

variable (M : ∀e x (a : (slot e).choice x),
  SiteMatrix (State (wire x)) (State (wire ((slot e).next x a))) F)

/-- At each named party, the entries are multiplied over adjacent physical
time layers and their shared intermediate state is summed exactly once. -/
def matrix : (es : List Event)→(x : X)→(p : Path slot es x)→
    SiteMatrix (State (wire x)) (State (wire (terminal slot es x p))) F
  | [],_,_=>SiteMatrix.identity _
  | e::es,x,p=>SiteMatrix.compose (M e x p.1) (matrix es ((slot e).next x p.1) p.2)

/-- All intermediate site states, from the first post-event state through
the terminal one. There is no edge-word equality constraint on a consumed
local state. Its two adjacent operators receive the identical named value. -/
def Trace : (es : List Event)→(x : X)→Path slot es x→Type
  | [],_,_=>Unit
  | e::es,x,p=>Layer wire ((slot e).next x p.1) × Trace es ((slot e).next x p.1) p.2

instance traceFinite : ∀ es x p,Fintype (Trace slot wire es x p)
  | [],_,_=>inferInstanceAs (Fintype Unit)
  | e::es,x,p=>
    letI := traceFinite es ((slot e).next x p.1) p.2
    inferInstanceAs (Fintype (Layer wire ((slot e).next x p.1) × Trace slot wire es _ p.2))

def weight : (es : List Event)→(x : X)→(p : Path slot es x)→
    Layer wire x→Trace slot wire es x p→F
  | [],x,_,v,_=>(raw F (wire x)).coeff v
  | e::es,x,p,v,z=>weight es ((slot e).next x p.1) p.2 z.1 z.2 *
    ∏i,M e x p.1 i (v i) (z.1 i)

/-- For an exposed term the host may either sum the intermediate state tapes
explicitly or contract the ordinary product of the composed local matrices
against the terminal wire tensor on the true native edge widths. -/
theorem sum_trace (es : List Event) (x : X) (p : Path slot es x) (v : Layer wire x) :
    (∑ z : Trace slot wire es x p,weight slot wire M es x p v z) =
      SiteMatrix.act (matrix slot wire M es x p) (raw F (wire (terminal slot es x p))).coeff v := by
  induction es generalizing x with
  | nil =>
    change (∑ _ : Unit,(raw F (wire x)).coeff v)=SiteMatrix.act (SiteMatrix.identity _) _ v
    simp only [Fintype.sum_unique]
    exact (SiteMatrix.act_id (B:=State (wire x)) (raw F (wire x)).coeff v).symm
  | cons e es ih =>
    obtain ⟨a,tail⟩ := p
    let y := (slot e).next x a
    change (∑ z : Layer wire y × Trace slot wire es y tail,
      weight slot wire M es y tail z.1 z.2 * ∏i,M e x a i (v i) (z.1 i))=_
    rw [Fintype.sum_prod_type]
    simp_rw [←Finset.sum_mul,ih]
    exact SiteMatrix.act_compose (M e x a) (matrix slot wire M es y tail) _ v

theorem matrix_sum
    (stage : ∀e x v,(raw F (wire x)).coeff v =
      ∑a,SiteMatrix.act (M e x a) (raw F (wire ((slot e).next x a))).coeff v)
    (es : List Event) (x : X) (v : Layer wire x) :
    (raw F (wire x)).coeff v =
      ∑p : Path slot es x,SiteMatrix.act (matrix slot wire M es x p)
        (raw F (wire (terminal slot es x p))).coeff v := by
  induction es generalizing x with
  | nil =>
    change _ = ∑ _ : Unit,SiteMatrix.act (SiteMatrix.identity _) _ v
    simp only [Fintype.sum_unique]
    exact (SiteMatrix.act_id (B:=State (wire x)) (raw F (wire x)).coeff v).symm
  | cons e es ih =>
    rw [stage e x v]
    change _=∑ p : Σ a:(slot e).choice x,Path slot es ((slot e).next x a),
      SiteMatrix.act (SiteMatrix.compose (M e x p.1) (matrix slot wire M es _ p.2)) _ v
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro a _
    let y := (slot e).next x a
    have tail : (raw F (wire y)).coeff =
        fun u=>∑p : Path slot es y,SiteMatrix.act (matrix slot wire M es y p)
          (raw F (wire (terminal slot es y p))).coeff u := funext (ih y)
    rw [tail,SiteMatrix.act_sum]
    exact Finset.sum_congr rfl fun p _=> SiteMatrix.act_compose (M e x a) (matrix slot wire M es y p) _ v

/-- An ordinary signed expansion whose coefficient at every fixed selector
uses precisely the supplied stage matrices. -/
def matrixExpansion
    (stage : ∀e x v,(raw F (wire x)).coeff v =
      ∑a,SiteMatrix.act (M e x a) (raw F (wire ((slot e).next x a))).coeff v)
    (es : List Event) (x : X) : Expansion (raw F (wire x)) (Path slot es x)
      (fun p=>wire (terminal slot es x p)) where
  part p v := SiteMatrix.act (matrix slot wire M es x p) (raw F (wire (terminal slot es x p))).coeff v
  sum := by
    funext v
    rw [Finset.sum_apply]
    exact matrix_sum slot wire M stage es x v
  image p := by
    refine ⟨matrix slot wire M es x p,fun _=>?_⟩
    exact state_sum_congr _ _ _

/-- The entry, chronological signed replacements, and terminal wire copies
are composed at the same named party. Each selector therefore exposes
the actual end-to-end matrix on the original open pins. -/
def matrixExpansionFrom {T : Raw.{0} (Fin S) F}
    (stage : ∀e x v,(raw F (wire x)).coeff v =
      ∑a,SiteMatrix.act (M e x a) (raw F (wire ((slot e).next x a))).coeff v)
    (es : List Event) (x : X) (ends : Path slot es x→Widths S)
    (entry : SiteMatrix T.Leg (State (wire x)) F)
    (start : ∀v,T.coeff v=SiteMatrix.act entry (raw F (wire x)).coeff v)
    (exit : ∀p,SiteMatrix (State (wire (terminal slot es x p))) (State (ends p)) F)
    (finish : ∀p v,(raw F (wire (terminal slot es x p))).coeff v =
      SiteMatrix.act (exit p) (raw F (ends p)).coeff v) :
    Expansion T (Path slot es x) ends where
  part p := SiteMatrix.act (SiteMatrix.compose entry
    (SiteMatrix.compose (matrix slot wire M es x p) (exit p))) (raw F (ends p)).coeff
  sum := by
    funext v
    rw [Finset.sum_apply,start]
    have mid : (raw F (wire x)).coeff=fun z=>∑p : Path slot es x,
        SiteMatrix.act (matrix slot wire M es x p) (raw F (wire (terminal slot es x p))).coeff z :=
      funext (matrix_sum slot wire M stage es x)
    rw [mid,SiteMatrix.act_sum]
    apply Finset.sum_congr rfl
    intro p _
    have terminalEq := funext (finish p)
    rw [terminalEq]
    have internal := funext (SiteMatrix.act_compose (matrix slot wire M es x p) (exit p) (raw F (ends p)).coeff)
    rw [internal]
    exact SiteMatrix.act_compose entry (SiteMatrix.compose (matrix slot wire M es x p) (exit p))
      (raw F (ends p)).coeff v
  image p := by
    refine ⟨SiteMatrix.compose entry (SiteMatrix.compose (matrix slot wire M es x p) (exit p)),fun _=>?_⟩
    exact state_sum_congr _ _ _

end CalendarTape
end Hierarchy.WireTelescope

end
end OAI
