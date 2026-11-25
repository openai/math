import Mathlib.Tactic.FinCases
import OAI.ThreeFlat.Diagonal.CompressorNativeGraph

namespace OAI
/-! # Change of syntax for the compressor's parameterized word operations -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.Placement
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM
variable {A B : Type*} {o : Ops A} {p : Ops B} {f : A → B}

structure OpMap (o : Ops A) (p : Ops B) (f : A → B) : Prop where
  lit : ∀ n, f (o.lit n)=p.lit n
  bin : ∀ k x y, f (o.bin k x y)=p.bin k (f x) (f y)
  load : ∀ x, f (o.load x)=p.load (f x)
  choose : ∀ x y a b, f (o.choose x y a b)=p.choose (f x) (f y) (f a) (f b)

namespace OpMap
variable (h : OpMap o p f) (G : ArcColumns A) (C : Columns A) (d : ℕ)
include h

theorem siteIf (u : A) (a b : Site A) :
    (Site.select o u a b).map f = Site.select p (f u) (a.map f) (b.map f) := by
  simp [Site.select,Site.map,h.choose,h.lit]

theorem positionIf (u : A) (a b : Position A) :
    (Position.select o u a b).map f = Position.select p (f u) (a.map f) (b.map f) := by
  simp [Position.select,Position.map,h.siteIf,h.choose,h.lit]

theorem node (v x : A) : f (row o v x) = row p (f v) (f x) := by simp [row,h.load,h.bin]
theorem edge (v x i : A) : f (slot o d v x i)=slot p d (f v) (f x) (f i) := by
  simp [slot,h.node,h.bin,h.lit]
theorem bit (a : Position A) : f (thickBit o C a) = thickBit p (C.map f) (a.map f) := by
  simp [thickBit,h.bin,h.node,h.lit,Columns.map,Position.map,Site.map]
theorem shift (a : Site A) : (toggle o C a).map f = toggle p (C.map f) (a.map f) := by
  simp [toggle,h.bin,h.node,Site.map,Columns.map]
theorem step (a : Site A) (i : A) : (forward o C d a i).map f = forward p (C.map f) d (a.map f) (f i) := by
  simp [forward,h.edge,h.bin,Site.map,Columns.map]
theorem reverse (a : Site A) (i : A) : (backward o C d a i).map f = backward p (C.map f) d (a.map f) (f i) := by
  simp [backward,h.edge,h.bin,Site.map,Columns.map]

theorem placed (b : Bool) (x : Position A) : (owner o C d b x).map f = owner p (C.map f) d b (x.map f) := by
  cases b <;> simp [owner,Site.map,Columns.map,Position.map,forward,toggle,thickBit,
    h.choose,h.lit,h.node,h.bin,h.edge]

theorem fromParent (lay thin : Bool) (a : Site A) (i u : A) :
    (child o C d lay thin a i u).map f = child p (C.map f) d lay thin (a.map f) (f i) (f u) := by
  cases lay <;> cases thin <;> simp [child,Position.map,toggle,backward,Site.map,Columns.map,h.bin,h.node,h.edge]

theorem arc (inc : Bool) (a : Position A) (i : A) : (ends o G d inc a i).map f =
    ends p (G.map f) d inc (a.map f) (f i) := by
  cases inc <;> simp [ends,Ends.map,Position.map,Site.map,h.bin,h.edge,forward,backward,ArcColumns.map,Columns.map]

theorem occurrence (lay thin inc : Bool) (a : Site A) (i u j : A) :
    (fromChild o G d lay thin inc a i u j).map f =
      fromChild p (G.map f) d lay thin inc (a.map f) (f i) (f u) (f j) := by
  unfold fromChild
  rw [h.arc,h.fromParent]
  rfl

theorem parties (lay : Bool) (e : Ends A) :
    (roleSites o G d lay e).map f = roleSites p (G.map f) d lay (e.map f) := by
  have site (u : A) (a b : Position A) :
      ((Position.select o u a b).site).map f=(Position.select p (f u) (a.map f) (b.map f)).site :=
    congrArg Position.site (h.positionIf u a b)
  have slot (u : A) (a b : Position A) :
      f (Position.select o u a b).slot=(Position.select p (f u) (a.map f) (b.map f)).slot :=
    congrArg Position.slot (h.positionIf u a b)
  simp only [roleSites,RoleSites.map,h.shift,h.positionIf,site,slot,h.bit,h.choose,h.lit,
    h.step,h.placed,ArcColumns.map,Ends.map]

theorem digit (v r z : A) : f (appendDigit o v r z)=appendDigit p (f v) (f r) (f z) := by
  simp [appendDigit,h.bin]

theorem candidate (r : Radices A) (S : Graph.Stage) (lay rev thin inc : Bool) (v : Site A)
    (k : Fin 4) (j : Fin (S.pieces k)) (slot : Fin S.degree) (bits : Fin (2^S.colors)) (i : Fin S.degree) :
    (Graph.candidateWith o G r S lay rev thin inc v k j slot bits i).map f =
      Graph.candidateWith p (G.map f) (r.map f) S lay rev thin inc (v.map f) k j slot bits i := by
  let a := fromChild o G S.degree
  have enc (base : Site A) (e : Ends A) (s : RoleSites A) (i z : Fin 3) :
      (Graph.encodeCandidate o r S base e s i z k j).map f =
        Graph.encodeCandidate p (r.map f) S (base.map f) (e.map f) (s.map f) i z k j := by
    fin_cases i <;> fin_cases z <;>
      simp [Graph.encodeCandidate,Graph.Candidate.map,Graph.encodeBase,Graph.siteAt,Radices.map,RoleSites.map,
        Position.map,Site.map,Ends.map,h.choose,h.lit,h.bin,h.digit]
  simp only [Graph.candidateWith,enc,h.parties,h.occurrence,h.lit]

end OpMap
end ThreeFlat.Diagonal.CompressorPacking.Native.Placement

end OAI
