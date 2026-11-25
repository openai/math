import OAI.Hierarchy.DescentHostDirectory
import OAI.Hierarchy.DescentOldHostBall

namespace OAI
/-! # Earlier donor sites and the order of their physical coordinates -/
namespace Hierarchy.DescentOrdinaryDonorHalo
open DescentHostDirectory
open scoped Classical
noncomputable section
variable {V : Type} [DecidableEq V]

/-- Previous original-site order is restricted to the old sites whose actual
rack lies in this public four-hop neighborhood of the new (possibly merged)
source key. It is then a short monotone name at this source. -/
def siteSet {U : Type} [Fintype U] (near : V→Finset V) (pos : U→V) (key : Key V) :=
  Finset.univ.filter (fun u=>pos u∈around near 4 key.1)

theorem lex {a b x y p : ℕ} (hx:x<p) (hy:y<p) :
    a*p+x<b*p+y ↔ a<b ∨ a=b ∧ x<y := by
  have sep {u v i : ℕ} (sm : u<v) (fit : i<p) : u*p+i<v*p :=by
    have step:=Nat.mul_le_mul_right p (Nat.succ_le_of_lt sm);rw [Nat.succ_mul] at step;omega
  rcases lt_trichotomy a b with less|eq|more
  · have:=sep less hx;omega
  · subst b;omega
  · have:=sep more hy;omega

end
end Hierarchy.DescentOrdinaryDonorHalo

end OAI
