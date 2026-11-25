import OAI.Hierarchy.DescentArchiveWorldShape
import OAI.Hierarchy.DescentBundleSelected
import OAI.Hierarchy.DescentBundleSplit
import OAI.Hierarchy.DescentCutAlignment

namespace OAI
/-! # A uniform stride and complete physical words on each reached site -/
namespace Hierarchy.DescentBundleHistory
open Computability.BorderVNP.Crossing DescentSixParty DescentHostDirectory DescentKernelHistory GadgetNetwork
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}

variable {B : BitDescription W}

def WorldShape.transport {V : MarkedWorld F d P bits} (eqv : W=V) (s : WorldShape p R B) :
    WorldShape p R (cast (congrArg BitDescription eqv) B) := by cases eqv;exact s

def WorldShape.selected (s : WorldShape p R B) (hp : 0<p) (one : 1≤R) (pins : ∀a,p∣bits a)
    {I C : Type} [Fintype I] (G : PoweredGadget F) (pick : I×Fin 2↪W.graph.Edge) (z : I→ℕ)
    (hz : ∀i,0<z i) (fit : ∀i a,W.graph.width (pick (i,a))=z i*G.b) {Z : ℕ} (room : ∀i,z i≤Z)
    (pack : W.graph.Site→C) (profile : I→Profile G.C) (units : ∀i,p∣z i) :
    WorldShape p R (B.selected G pick z hz fit room pack profile) where
  sites := Shape.selected W B G pick z hz fit room pack profile hp s.sites s.edges pins units
  stride v u j g := by
    rcases u with ⟨⟨x,h⟩,u⟩
    rcases x with x|⟨i,k⟩
    · exact s.stride x u j g
    · exact one
  edges e := physical_multiple W G pick z profile s.edges units e.val

def WorldShape.coalesced (s : WorldShape p R B) {V : Type} [DecidableEq V] (key : W.graph.Site→Key V)
    (hub : V→Bool) (k g : ℕ) : WorldShape p R (B.coalesced key hub k g) where
  sites := Shape.coalesced W B key hub k g s.sites s.edges
  stride _ u j g := s.stride u.1.val u.2 j g
  edges e := s.edges e.val

def WorldShape.pieces (s : WorldShape p R B) (m : W.graph.Edge→ℕ) (q : ℕ)
    (cut : ∀e∈W.core,W.graph.width e=m e*q) (hp : 0<p) (hq : 0<q) (unit : p∣q) :
    WorldShape p R (B.pieces m q cut) := by
  let t:=q/p
  have eqv : q=t*p := (Nat.div_mul_cancel unit).symm
  have ht : 0<t := Nat.div_pos (Nat.le_of_dvd hq unit) hp
  exact {
    sites := fun v => Shape.pieces W m q hp ht eqv v cut (s.sites v)
    stride := s.stride
    edges := fun e => match e with
      | .inl b => s.edges b.val
      | .inr _ => unit
  }

def WorldShape.granular (s : WorldShape p R B) (m : W.graph.Edge→ℕ) (q : ℕ)
    (cut : ∀e,W.graph.width e=m e*q) (hp : 0<p) (hq : 0<q) (unit : p∣q) :
    WorldShape p R (BitDescription.granular W m q cut B) := by
  let t:=q/p
  have eqt : q=t*p := (Nat.div_mul_cancel unit).symm
  have ht : 0<t := Nat.div_pos (Nat.le_of_dvd hq unit) hp
  exact {
    sites := fun v => Shape.granular W m q cut hp ht eqt v (s.sites v)
    stride := s.stride
    edges := fun _ => unit
  }

def namedMap (W : MarkedWorld F d P bits) (s : Equiv.Perm W.graph.Site) (e : Equiv.Perm W.graph.Edge) (v : W.graph.Site) :
    BlockMap p (boundaryWidth W.graph (s.symm v)) (boundaryWidth (PhysicalRename.graph W.graph s e) v)
      (PhysicalRename.boundaryBit W.graph s e v) where
  map := BlockRef.rename (PhysicalRename.boundary W.graph s e v) (fun b=>(PhysicalRename.boundary_width W.graph s e v b).symm)
  read _ _ := rfl

def WorldShape.renamed (r : WorldShape p R B) (s : Equiv.Perm W.graph.Site) (e : Equiv.Perm W.graph.Edge) :
    WorldShape p R (B.renamed s e) where
  sites v := (r.sites (s.symm v)).reroute (namedMap W s e v)
  stride v := r.stride (s.symm v)
  edges j := r.edges (e.symm j)

/-- For the actual recursively built history, every split in this normalization uses
its audited quantum. Transport only renames physical blocks. -/
def WorldShape.follow (hp : 0<p) {q : ℕ} (hq : 0<q) (unit : p∣q) (n : Normalize W)
    (aligned : Normalize.CutsEqual q n) (s : WorldShape p R B) : WorldShape p R (BitDescription.follow n B) := by
  induction n with
  | done => exact s
  | merge W V key hub k g tail ih => exact ih aligned (s.coalesced key hub k g)
  | named W a e tail ih => exact ih aligned (s.renamed a e)
  | split W q' m cut tail ih =>
    obtain ⟨rfl,ok⟩ := aligned
    exact ih ok (s.pieces m q' cut hp hq unit)


end
end Hierarchy.DescentBundleHistory

end OAI
