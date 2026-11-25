import OAI.Hierarchy.TaggedWireWordSpine
import OAI.Hierarchy.TaggedWireSiteTurns

namespace OAI
/-! # Per-word turns before the bit lanes are expanded -/

noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph AdaptiveProbe
open scoped Classical BigOperators

/-- First and last old port, or an oriented port at a literal hop position. -/
abbrev TurnRef := Bool ⊕ (ℕ × Bool)

def wordTurns {S : ℕ} (last : Fin S) (r : TurnRef) :
    List (Fin S × Bool) → TurnRef → ℕ → Fin S → List (TurnRef × TurnRef)
  | [],l,_,s=>if last=s then [(l,r)] else []
  | (v,b)::rest,l,j,s=>
    (if v=s then [(l,.inr (j,b))] else []) ++ wordTurns last r rest (.inr (j,!b)) (j+1) s

namespace Spine
variable {S : ℕ} {E T : Type} {G : PortGraph (Fin S) E} {a b : Fin S} {es : List E}

def itinerary : {a b : Fin S} → {es : List E} → Spine G a es b → List (Fin S × Bool)
  | _,_,_,.nil _=>[]
  | _,_,_,.cons e t tail=>(G.vertex e t,t)::itinerary tail

def itineraryOf (G : PortGraph (Fin S) E) : Fin S → List E → List (Fin S × Bool)
  | _,[]=>[]
  | v,e::xs=>
    let t:=decide (G.head e=v)
    (v,t)::itineraryOf G (G.vertex e (!t)) xs

theorem itinerary_eq (sp : Spine G a es b) (diff : ∀e,G.tail e≠G.head e) :
    itinerary sp=itineraryOf G a es := by
  induction sp with
  | nil v=>rfl
  | cons e t tail ih=>
    cases t <;> simp [itinerary,itineraryOf,PortGraph.vertex,Ne.symm (diff e)] at * <;> exact ih

theorem itinerary_map (G : PortGraph (Fin S) E) (C : PortGraph (Fin S) T) (row : T→E)
    (lo : ∀e,C.tail e=G.tail (row e)) (hi : ∀e,C.head e=G.head (row e))
    (a : Fin S) (xs : List T) : itineraryOf C a xs=itineraryOf G a (xs.map row) := by
  induction xs generalizing a with
  | nil=>rfl
  | cons i rest ih=>
    have vtx (t : Bool) : C.vertex i t=G.vertex (row i) t := by cases t <;> simp [PortGraph.vertex,lo,hi]
    simp only [List.map_cons,itineraryOf,hi,vtx,ih]

/-- General normalization. `read` uses only the state of the visited
party. No condition is required on the labels at unrelated parties. -/
theorem stitches_words {V : Fin S→Type} (sp : Spine G a es b)
    (read : ∀s,V s→TurnRef→Bool) (l r : TurnRef) (pos : ℕ) (s : Fin S) (z : V s) :
    sp.stitches (fun x=>read a x l) (fun x=>read b x r)
      (fun j t x=>read _ x (.inr (pos+j.val,t))) s z ↔
      Equality.agrees (wordTurns b r sp.itinerary l pos s) (read s z) := by
  have single (v : Fin S) (c d : TurnRef) :
      atSite v (fun x=>read v x c=read v x d) s z ↔
      Equality.agrees (if v=s then [(c,d)] else []) (read s z) := by
    by_cases eq:v=s
    · subst s;simp [atSite,Equality.agrees]
    · simp [atSite,Equality.agrees,eq,Ne.symm eq]
  induction sp generalizing pos l with
  | nil v=>exact single v l r
  | @cons e t xs v tail ih=>
    simp only [stitches,itinerary,wordTurns,Fin.val_zero,Nat.add_zero,Fin.val_succ]
    have next := ih (.inr (pos,!t)) (pos+1)
    have sh : ∀j : Fin xs.length,pos+(j.val+1)=pos+1+j.val := by intro;omega
    have app (u v : List (TurnRef × TurnRef)) :
        Equality.agrees (u++v) (read s z) ↔ Equality.agrees u (read s z) ∧ Equality.agrees v (read s z) := by
      simp [Equality.agrees,or_imp,forall_and]
    refine (and_congr (single (G.vertex e t) l (.inr (pos,t))) ?_).trans (app _ _).symm
    simpa only [sh,List.get_cons_zero,List.get_cons_succ'] using next

end Spine

variable {S n m : ℕ} (G : PortGraph (Fin S) (Fin m)) (C : PortGraph (Fin S) (Fin n))
    (route : Fin n→List (Fin m)) (bits : Fin n→ℕ)
    (a : Hop route bits≃Bundle (routeLoad route bits)) (located : ∀q,(a q).1=hopEdge route bits q)
    (path : ∀i,Traverses G (C.tail i) (route i) (C.head i))

def actualTurns (i : Fin n) (s : Fin S) :=
  wordTurns (C.head i) (.inl true) (Spine.itineraryOf G (C.tail i) (route i)) (.inl false) 0 s

/-- Private bit read at a named end, with a total definition away from the
local party and the valid itinerary. Only valid coordinates can occur in a
local word-turn test. -/
def readTurn (q : Bundle bits) (s : Fin S)
    (x : BitState (bitGraph C bits) s × BitState (bitGraph G (routeLoad route bits)) s) : TurnRef→Bool
  | .inl b=>if h : (bitGraph C bits).vertex q b=s then x.1 ⟨(q,b),h⟩ else false
  | .inr (j,b)=>if ht : j<(placedRoute route bits a q).length then
      let p := (placedRoute route bits a q).get ⟨j,ht⟩
      if h : (bitGraph G (routeLoad route bits)).vertex p b=s then x.2 ⟨(p,b),h⟩ else false
    else false

/-- Matrix acceptance is a conjunction indexed by the single itinerary of
each physical word, evaluated on all its live consecutive bit lanes. -/
theorem word_turns_iff (diff : ∀i,G.tail i≠G.head i) (s : Fin S)
    (x : BitState (bitGraph C bits) s) (y : BitState (bitGraph G (routeLoad route bits)) s) :
    bitStitches _ _ (placedRoute route bits a) (placedSpine route bits a located G C path) s x y ↔
      ∀ i,∀ t∈actualTurns G C route i s,∀ j : Fin (bits i),
        readTurn G C route bits a ⟨i,j⟩ s (x,y) t.1=readTurn G C route bits a ⟨i,j⟩ s (x,y) t.2 := by
  have each (q : Bundle bits) :=
    Spine.stitches_words (placedSpine route bits a located G C path q)
      (readTurn G C route bits a q) (.inl false) (.inl true) 0 s (x,y)
  have track (q : Bundle bits) :
      (placedSpine route bits a located G C path q).itinerary=
        Spine.itineraryOf G (C.tail q.1) (route q.1) := by
    rw [Spine.itinerary_eq _ (fun i=>diff i.1),Spine.itinerary_map G (bitGraph G _) Sigma.fst
      (fun _=>rfl) (fun _=>rfl),placedRoute_edges route bits a located]; rfl
  simp only [track, Nat.zero_add] at each
  have actual (q : Bundle bits) : (placedSpine route bits a located G C path q).stitches
      (V:=fun t=>BitState (bitGraph C bits) t × BitState (bitGraph G (routeLoad route bits)) t)
      (fun z=>z.1 ⟨(q,false),rfl⟩) (fun z=>z.1 ⟨(q,true),rfl⟩)
      (fun j side z=>z.2 ⟨((placedRoute route bits a q).get j,side),rfl⟩) s (x,y) ↔
      Equality.agrees (actualTurns G C route q.1 s) (readTurn G C route bits a q s (x,y)) := by
    let V := fun t => BitState (bitGraph C bits) t × BitState (bitGraph G (routeLoad route bits)) t
    have old (b : Bool) (z : V ((bitGraph C bits).vertex q b)) :
        readTurn G C route bits a q _ z (.inl b) = z.1 ⟨(q,b),rfl⟩ := by simp [readTurn]
    have left (z : V ((bitGraph C bits).tail q)) :
        readTurn G C route bits a q ((bitGraph C bits).tail q) z (.inl false) = z.1 ⟨(q,false),rfl⟩ := old false z
    have right (z : V ((bitGraph C bits).head q)) :
        readTurn G C route bits a q ((bitGraph C bits).head q) z (.inl true) = z.1 ⟨(q,true),rfl⟩ := old true z
    have hop (j : Fin (placedRoute route bits a q).length) (b : Bool)
        (z : V ((bitGraph G (routeLoad route bits)).vertex ((placedRoute route bits a q).get j) b)) :
        readTurn G C route bits a q _ z (.inr (j.val,b)) = z.2 ⟨((placedRoute route bits a q).get j,b),rfl⟩ := by
      simp [readTurn,j.isLt]
    have law := each q
    simp only [left,right,hop] at law
    have turns : wordTurns ((bitGraph C bits).head q) (.inl true)
        (Spine.itineraryOf G (C.tail q.1) (route q.1)) (.inl false) 0 s = actualTurns G C route q.1 s := rfl
    rw [turns] at law
    exact law
  constructor
  · intro ok i t mem j
    exact (actual ⟨i,j⟩).mp (ok _) t mem
  · intro ok q
    exact (actual q).mpr (fun t ht=>ok q.1 t ht q.2)

end Hierarchy.WireTelescope

end
end OAI
