import OAI.Hierarchy.TaggedWireRoutes
import OAI.LinearAlgebra.SpectralBooks.PortWiring

namespace OAI
/-! # The literal equality gates at consecutive physical route occurrences -/

noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks SiteTensor
open scoped Classical BigOperators

variable {S : ℕ} {I E : Type} (G : PortGraph (Fin S) E)

/-- An oriented spine keeps the actual occurrence order, including every repeated
link and both possible orientations at the next endpoint. -/
inductive Spine : Fin S→List E→Fin S→Type where
  | nil (v) : Spine v [] v
  | cons (e : E) (side : Bool) {es b} :
    Spine (G.vertex e (!side)) es b → Spine (G.vertex e side) (e::es) b

namespace Spine
variable {G} {a b : Fin S} {es : List E}

theorem exists_of_walk (path : Traverses G a es b) : Nonempty (Spine G a es b) := by
  induction path with
  | nil a=>exact ⟨.nil a⟩
  | forward e _ ih=>exact ⟨.cons e false ih.some⟩
  | backward e _ ih=>exact ⟨.cons e true ih.some⟩

variable {V : Fin S→Type}
abbrev Read (V : Fin S→Type) (a : Fin S) := V a→Bool
abbrev Ports (G : PortGraph (Fin S) E) (V : Fin S→Type) (es : List E) :=
  ∀j : Fin es.length,∀s:Bool,Read V (G.vertex (es.get j) s)

/-- A local condition at u uses only the bits in the matrix at u. -/
def atSite (a : Fin S) (P : V a→Prop) (i : Fin S) (v : V i) : Prop :=
  ∀ h:i=a,P (h ▸ v)

theorem all_atSite (a : Fin S) (P : V a→Prop) (v : ∀i,V i) :
    (∀i,atSite a P i (v i)) ↔ P (v a) := by
  constructor
  · intro h; exact h a rfl
  · rintro h i rfl; exact h

/-- The implementation is an equality check per endpoint or internal turn:
the previous arrival must equal the next departure at their own shared party. -/
def stitches : {a b : Fin S}→{es : List E}→Spine G a es b →
    Read V a→Read V b→Ports G V es→(i:Fin S)→V i→Prop
  | _,_,_,.nil a,l,r,_,i,z=>atSite a (fun val=>l val=r val) i z
  | _,_,_,.cons e side tail,l,r,port,i,z=>
    atSite (G.vertex e side) (fun val=>l val=port 0 side val) i z ∧
      stitches tail (port 0 (!side)) r (fun j s=>port j.succ s) i z

/-- A tuple of native edge bits already has matching endpoint copies at
each hop. The local stitch tests then force the entire path to carry its
source bit and require that same bit at the destination. -/
theorem all_stitches (sp : Spine G a es b) (l : Read V a) (r : Read V b)
    (port : Ports G V es) (v : ∀i,V i) (word : Fin es.length→Bool)
    (read : ∀j s,port j s (v (G.vertex (es.get j) s))=word j) :
    (∀i,sp.stitches l r port i (v i)) ↔ l (v a)=r (v b) ∧ ∀j,word j=l (v a) := by
  induction sp with
  | nil a =>
    rw [show (∀ i,(Spine.nil (G:=G) a).stitches l r port i (v i)) ↔ l (v a)=r (v a) from all_atSite ..]
    exact ⟨fun h=>⟨h,fun j=>Fin.elim0 j⟩,And.left⟩
  | @cons e side rest dest tail ih =>
    change (∀i,atSite _ _ i (v i) ∧ tail.stitches _ r _ i (v i)) ↔ _
    have atHead (b : Bool) : port 0 b (v (G.vertex e b))=word 0:=read 0 b
    rw [forall_and,all_atSite,ih (port 0 (!side)) r (fun j s=>port j.succ s)
      (fun j=>word j.succ) (fun j s=>read j.succ s),atHead side,atHead (!side)]
    constructor
    · rintro ⟨first,last,all⟩
      exact ⟨first.trans last,fun j=>Fin.cases first.symm (fun k=>(all k).trans first.symm) j⟩
    · rintro ⟨same,all⟩
      exact ⟨(all 0).symm,(all 0).trans same,fun j=>(all j.succ).trans (all 0).symm⟩

end Spine

variable [Fintype I] [Fintype E] (C : PortGraph (Fin S) I) (route : I→List E)
variable (spine : ∀i,Spine G (C.tail i) (route i) (C.head i))

abbrev BitState {J : Type} (A : PortGraph (Fin S) J) (i : Fin S) := A.State (fun _=>Bool) i

/-- The two arguments are the actual old bit ports and the new physical bit ports
of this single named party. No global comparison is used by a party. -/
def bitStitches (s : Fin S) (x : BitState C s) (y : BitState G s) : Prop :=
  ∀i,(spine i).stitches (V:=fun v=>BitState C v × BitState G v)
    (fun z=>z.1 ⟨(i,false),rfl⟩) (fun z=>z.1 ⟨(i,true),rfl⟩)
    (fun j side z=>z.2 ⟨((route i).get j,side),rfl⟩) s (x,y)

def bitMatrix (F : Type*) [Field F] (s : Fin S) (x : BitState C s) (y : BitState G s) : F :=
  if bitStitches G C route spine s x y then 1 else 0

omit [Fintype I] [Fintype E] in
theorem bitStitches_iff (x : ∀s,BitState C s) (data : E→Bool)
    (row : (Σ i,Fin (route i).length)≃E) (number : ∀i j,row ⟨i,j⟩=(route i).get j) :
    (∀s,bitStitches G C route spine s (x s) (G.atVertex data s)) ↔
      (∀i,x (C.tail i) ⟨(i,false),rfl⟩=x (C.head i) ⟨(i,true),rfl⟩) ∧
      data=fun e=>let i:=(row.symm e).1; x (C.tail i) ⟨(i,false),rfl⟩ := by
  let v (s : Fin S) := (x s,G.atVertex data s)
  let l (i : I) (z : BitState C (C.tail i) × BitState G (C.tail i)) := z.1 ⟨(i,false),rfl⟩
  let r (i : I) (z : BitState C (C.head i) × BitState G (C.head i)) := z.1 ⟨(i,true),rfl⟩
  let port (i : I) : Spine.Ports G (fun s=>BitState C s × BitState G s) (route i) :=
    fun j side z=>z.2 ⟨((route i).get j,side),rfl⟩
  have stitch (i : I) := (spine i).all_stitches (l i) (r i) (port i) v
    (fun j=>data ((route i).get j)) (fun _ _=>rfl)
  constructor
  · intro all
    have one (i : I) := (stitch i).mp (fun s=>all s i)
    refine ⟨fun i=>(one i).1,?_⟩
    funext e
    obtain ⟨⟨i,j⟩,rfl⟩ := row.surjective e
    rw [row.symm_apply_apply,number]
    exact (one i).2 j
  · rintro ⟨ends,dataEq⟩ s i
    have pin (j : Fin (route i).length) : data ((route i).get j)=l i (v (C.tail i)) := by
      rw [←number i j,dataEq]
      exact congrArg (fun q : Σ i,Fin (route i).length=>x (C.tail q.1) ⟨(q.1,false),rfl⟩) (row.symm_apply_apply ⟨i,j⟩)
    exact (stitch i).mpr ⟨ends i,pin⟩ s

/-- Contracting these literal 0/1 site gates yields exactly the original
matching bits. Every valid boundary has one assignment to all routed
physical bit occurrences; an inconsistent input boundary has none. -/
theorem bit_route_action (F : Type*) [Field F] (x : ∀s,BitState C s)
    (row : (Σ i,Fin (route i).length)≃E) (number : ∀i j,row ⟨i,j⟩=(route i).get j) :
    C.wiring (K:=F) (fun _=>Bool) x =
      ∑ data : E→Bool,∏s,bitMatrix G C route spine F s (x s) (G.atVertex data s) := by
  simp only [bitMatrix,Fintype.prod_boole,fun data=>bitStitches_iff G C route spine x data row number,PortGraph.wiring]
  split_ifs with ok
  · simp [ok]
  · simp [ok]

end Hierarchy.WireTelescope

end
end OAI
