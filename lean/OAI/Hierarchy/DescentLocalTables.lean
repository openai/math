import OAI.Computability.BorderVNP.CrossingNetwork

namespace OAI
/-! # Constructing native tensor tables from coefficients supported on actual local ports -/

namespace Hierarchy.DescentLocalTables
open Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
variable {D : ℕ} {P K : Type*} {bits : P→ℕ} (N : Network D P bits)

def Supported (f : N.Assignment → Ports bits → N.Site → K) :=
  ∀v a b x y,(∀e,N.src e=v ∨ N.dst e=v → a e=b e) → (∀p,N.attach p=v → x p=y p) → f a x v=f b y v

def tables (f : N.Assignment → Ports bits → N.Site → K) : N.Tables K :=
  fun v inner outer => f
    (fun e=>if h : N.src e=v ∨ N.dst e=v then inner ⟨e,h⟩ else fun _=>false)
    (fun p=>if h : N.attach p=v then outer ⟨p,h⟩ else fun _=>false) v

theorem read (f : N.Assignment → Ports bits → N.Site → K) (locality : Supported N f)
    (a : N.Assignment) (p : Ports bits) (v : N.Site) : N.read (tables N f) a p v=f a p v := by
  exact locality v _ a _ p (fun e h=>by simp [h]) (fun q h=>by simp [h])

end
end Hierarchy.DescentLocalTables

end OAI
