import OAI.Hierarchy.TaggedWireRowGraph
import OAI.Hierarchy.TaggedWireHopBits
import OAI.Hierarchy.TaggedWireEdgeWords
import OAI.Hierarchy.TaggedWireNativeSlot
import OAI.Computability.VPVNP.RAMSerialization

namespace OAI
/-! # Copying physical native edge bits on the literal aggregate chord states -/

noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open AdaptiveProbe Computability.VPVNP.RAMSerialization
open scoped Classical BigOperators

variable {S n r : ℕ} {F : Type*} [Field F]

def sourcePort (ends : Fin n→Chord S) (bits : Fin n→ℕ) {v : Fin S}
    (p : (bitGraph (rowGraph ends) bits).Port v) : (portGraph S).Port v :=
  ⟨(ends p.1.1.1,p.1.2),by obtain ⟨⟨⟨i,j⟩,s⟩,atV⟩ := p; cases s <;> exact atV⟩

theorem blockSize (ends : Fin n→Chord S) (bits : Fin n→ℕ) (r : Fin n) :
    2^((bits r • unitChord (ends r)) (ends r))=2^(bits r) := by
  simp [unitChord]

def chunk (ends : Fin n→Chord S) (bits : Fin n→ℕ) (r : Fin n)
    (x : Index (installedWidths ends bits) (ends r)) : Fin (2^(bits r)) :=
  finCongr (blockSize ends bits r) (blockWireIndex (fun j=>bits j • unitChord (ends j)) (ends r) x r)

def rowBits (ends : Fin n→Chord S) (bits : Fin n→ℕ) {v : Fin S}
    (x : State (installedWidths ends bits) v) : BitState (bitGraph (rowGraph ends) bits) v :=
  fun p=>wordBits (bits p.1.1.1) (chunk ends bits p.1.1.1 (x (sourcePort ends bits p))) p.1.1.2

def wordBitsEquiv (bits : Fin n→ℕ) : (∀i,Fin (2^bits i))≃(Bundle bits→Bool) :=
  (Equiv.piCongrRight fun j=>wordBits (bits j)).trans (Equiv.piCurry (fun i (_:Fin (bits i))=>Bool)).symm

theorem rowBits_readEdges (ends : Fin n→Chord S) (bits : Fin n→ℕ) (data : ∀r,Fin (2^(bits r))) (s : Fin S) :
    rowBits ends bits (readEdges ends bits data s) =
      (bitGraph (rowGraph ends) bits).atVertex (wordBitsEquiv bits data) s := by
  funext p
  let j := p.1.1.1
  have saved := congrFun ((edgeWords ends bits).apply_symm_apply data) j
  change chunk ends bits j ((edgeWords ends bits).symm data (ends j))=data j at saved
  exact congrArg (fun t=>wordBits (bits j) t p.1.1.2) saved

theorem raw_as_bits (ends : Fin n→Chord S) (bits : Fin n→ℕ)
    (x : ∀s,State (installedWidths ends bits) s) :
    (raw F (installedWidths ends bits)).coeff x =
      (bitGraph (rowGraph ends) bits).wiring (K:=F) (fun _=>Bool) (fun s=>rowBits ends bits (x s)) := by
  let U := fun j=>bits j • unitChord (ends j)
  let L := fun e : Chord S=>x e.1.1 ⟨(e,false),rfl⟩
  let R := fun e : Chord S=>x e.1.2 ⟨(e,true),rfl⟩
  have same : (∀e,L e=R e) ↔ ∀q : Bundle bits,
      wordBits (bits q.1) (chunk ends bits q.1 (L (ends q.1))) q.2 =
      wordBits (bits q.1) (chunk ends bits q.1 (R (ends q.1))) q.2 := by
    constructor
    · intro all q; rw [all]
    · intro byBit e
      apply (blockWireIndex U e).injective
      funext j
      by_cases on : ends j=e
      · subst e
        have one : chunk ends bits j (L (ends j))=chunk ends bits j (R (ends j)) := by
          apply (wordBits (bits j)).injective
          funext i
          exact byBit ⟨j,i⟩
        exact (finCongr (blockSize ends bits j)).injective one
      · have tiny : 2^(U j e)=1 := by
          simp [U,unitChord,Ne.symm on]
        apply Fin.ext
        have lo := ((blockWireIndex U e (L e)) j).isLt
        have hi := ((blockWireIndex U e (R e)) j).isLt
        omega
  simp only [raw,PortGraph.wiring]
  split
  next chord =>
    split
    · rfl
    · rename_i bit
      exact (bit (same.mp chord)).elim
  next chord =>
    split
    · rename_i bit
      exact (chord (same.mpr bit)).elim
    · rfl

def chordRouterWith (old : Fin n→Chord S) (edge : Fin r→Chord S) (route : Fin n→List (Fin r)) (bits : Fin n→ℕ)
    (alloc : Hop route bits ≃ Bundle (routeLoad route bits)) (located : ∀h,(alloc h).1=hopEdge route bits h)
    (walk : ∀i,Traverses (rowGraph edge) ((old i).1.1) (route i) ((old i).1.2)) :
    SiteMatrix (State (installedWidths old bits)) (State (installedWidths edge (routeLoad route bits))) F :=
  fun s v z=>bitMatrix _ _ (placedRoute route bits alloc) (placedSpine route bits alloc located (rowGraph edge) (rowGraph old) walk)
    F s (rowBits old bits v) (rowBits edge _ z)

theorem chordRouterWith_action (old : Fin n→Chord S) (edge : Fin r→Chord S) (route : Fin n→List (Fin r)) (bits : Fin n→ℕ)
    (alloc : Hop route bits ≃ Bundle (routeLoad route bits)) (located : ∀h,(alloc h).1=hopEdge route bits h)
    (walk : ∀i,Traverses (rowGraph edge) ((old i).1.1) (route i) ((old i).1.2))
    (x : ∀s,State (installedWidths old bits) s) :
    (raw F (installedWidths old bits)).coeff x =
      SiteMatrix.act (chordRouterWith old edge route bits alloc located walk) (raw F (installedWidths edge (routeLoad route bits))).coeff x := by
  let new := routeLoad route bits
  let matrix := bitMatrix _ _ (placedRoute route bits alloc) (placedSpine route bits alloc located (rowGraph edge) (rowGraph old) walk) F
  let value := fun a : Bundle new→Bool=>∏s,matrix s (rowBits old bits (x s)) ((bitGraph (rowGraph edge) new).atVertex a s)
  rw [raw_as_bits,act_edge_words]
  refine (placed_action route bits alloc located (rowGraph edge) (rowGraph old) walk F _).trans ?_
  refine ((wordBitsEquiv new).sum_comp value).symm.trans ?_
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.prod_congr rfl
  intro s _
  change matrix s _ _=matrix s _ (rowBits edge new (readEdges edge new a s))
  rw [rowBits_readEdges]

/-- Use the bit offsets actually returned by the weighted prefix scan on
the chronological occurrence directory, ordered like the native reporter. -/
def chordRouter (old : Fin n→Chord S) (edge : Fin r→Chord S) (route : Fin n→List (Fin r)) (bits : Fin n→ℕ)
    {rows : ℕ} (ord : Fin rows≃Σi,Fin (route i).length)
    (walk : ∀i,Traverses (rowGraph edge) ((old i).1.1) (route i) ((old i).1.2)) :=
  chordRouterWith (F:=F) old edge route bits (NativeSlot.allocation route bits ord)
    (NativeSlot.allocation_edge route bits ord) walk

theorem chordRouter_action (old : Fin n→Chord S) (edge : Fin r→Chord S) (route : Fin n→List (Fin r)) (bits : Fin n→ℕ)
    {rows : ℕ} (ord : Fin rows≃Σi,Fin (route i).length)
    (walk : ∀i,Traverses (rowGraph edge) ((old i).1.1) (route i) ((old i).1.2))
    (x : ∀s,State (installedWidths old bits) s) :
    (raw F (installedWidths old bits)).coeff x =
      SiteMatrix.act (chordRouter old edge route bits ord walk)
        (raw F (installedWidths edge (routeLoad route bits))).coeff x :=
  chordRouterWith_action old edge route bits _ _ walk x

end Hierarchy.WireTelescope

end
end OAI
