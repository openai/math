import OAI.Hierarchy.ProbeTreeBroadcast
import OAI.LinearAlgebra.SpectralBooks.RawTiledTables

namespace OAI
/-! # The value transported by the actual installed selector chords -/

noncomputable section
namespace Hierarchy.Probe
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open scoped BigOperators Classical

variable {k n : ℕ} {F : Type*} [Field F]

def LooksConnected (q : Widths k) (n : ℕ) :=
  ∀ {W : Type} (v : Fin k→W), (∀e : Chord k,n≤q e → v e.val.1=v e.val.2) → ∀i j,v i=v j

theorem actual_links {B : Type} [Fintype B] (G : PortGraph (Fin k) B) (conn : BroadcastConnected G) (n : ℕ) :
    LooksConnected (G.chordWidths (fun _=>n)) n := by
  intro W v same
  apply conn v
  intro e
  have slice (t : Chord k) : G.chordWidth e n t≤G.chordWidths (fun _=>n) t := by
    change _≤(∑ j : B,G.chordWidth j n) t
    rw [Finsupp.finsetSum_apply]
    exact Finset.single_le_sum (f:=fun j=>G.chordWidth j n t) (fun _ _=>Nat.zero_le _) (Finset.mem_univ e)
  rcases lt_trichotomy (G.tail e) (G.head e) with lo|eqn|hi
  · let t : Chord k := ⟨(G.tail e,G.head e),lo⟩
    exact same t (by simpa [PortGraph.chordWidth,lo,t] using slice t)
  · rw [eqn]
  · let t : Chord k := ⟨(G.head e,G.tail e),hi⟩
    exact (same t (by simpa [PortGraph.chordWidth,not_lt.mpr hi.le,hi,t] using slice t)).symm

/-- The selected word occupies the low bits of each large enough chord;
spare high bits (including those of parallel links) are all zero. -/
def extendColour (q : Widths k) (e : Chord k) (c : Fin (2^n)) : Index q e :=
  if h : n≤q e then ⟨c.val,c.isLt.trans_le (Nat.pow_le_pow_right (by decide) h)⟩ else 0

theorem extendColour_injective (q : Widths k) (e : Chord k) (fit : n≤q e) :
    Function.Injective (extendColour (n:=n) q e) := by
  intro a b eqn
  exact Fin.ext (by simpa [extendColour,fit] using congrArg Fin.val eqn)

def colourState (q : Widths k) (i : Fin k) (c : Fin (2^n)) : State q i :=
  fun p=>extendColour q p.val.1 c

theorem colour_checks {W : Type} (code : W ↪ Fin (2^n)) (q : Widths k) (conn : LooksConnected q n)
    (root : Fin k) (f : Fin k→W) :
    (raw F q).coeff (fun i=>colourState q i (code (f i))) =
      if ∀ i, f i=f root then 1 else 0 := by
  let joined := ∀ e : Chord k,
    extendColour q e (code (f e.val.1))=extendColour q e (code (f e.val.2))
  have iff : joined ↔ ∀ i,f i=f root := by
    constructor
    · intro eqn i
      exact conn f (fun e h=>code.injective (extendColour_injective q e h (eqn e))) i root
    · intro constant e
      rw [constant e.val.1,constant e.val.2]
  dsimp only [raw,PortGraph.wiring]
  split
  next yes => exact (ite_eq_left (iff.mp yes)).symm
  next no => exact (ite_eq_right (fun h=>no (iff.mpr h))).symm

theorem sum_constant {W : Type} [Fintype W] (root : Fin k) (L : (Fin k → W) → F) :
    (∑ f : Fin k → W, (if ∀i, f i=f root then (1:F) else 0)*L f) = ∑ u : W,L (fun _=>u) := by
  let C (f : Fin k→W) := ∀i, f i=f root
  let eqv : {f : Fin k→W // C f} ≃ W :=
    {toFun:=fun f=>f.val root,invFun:=fun u=>⟨fun _=>u,fun _=>rfl⟩,
     left_inv:=fun f=>Subtype.ext (funext (fun i=>(f.property i).symm)),right_inv:=fun _=>rfl}
  simp only [ite_mul,one_mul,zero_mul]
  change (∑ f,if C f then L f else 0)=_
  rw [←Finset.sum_filter,←Finset.sum_subtype_eq_sum_filter,Finset.subtype_univ]
  exact Fintype.sum_equiv eqv _ _ fun f=>congrArg L (funext (fun i=>f.property i))

/-- Combining one genuine ordinary site map with its incident equality
sockets sums exactly once over every surviving selector value. -/
theorem sum_broadcast {W : Type} [Fintype W] (code : W ↪ Fin (2^n)) (q : Widths k) (conn : LooksConnected q n)
    (root : Fin k) (L : Fin k→W→F) :
    (∑ y : ∀i,State q i,(raw F q).coeff y *
      ∏ i,∑ u : W, (if y i=colourState q i (code u) then (1:F) else 0)*L i u) =
        ∑ u : W,∏ i,L i u := by
  simp_rw [Fintype.prod_sum,Finset.mul_sum,Finset.prod_mul_distrib,Fintype.prod_boole]
  rw [Finset.sum_comm]
  calc
    _ = ∑ f : Fin k→W,(raw F q).coeff (fun i=>colourState q i (code (f i)))*∏ i,L i (f i) := by
      apply Finset.sum_congr rfl
      intro f _
      let y₀ := fun i=>colourState q i (code (f i))
      have iff (y : ∀i,State q i) : (∀ i,y i=colourState q i (code (f i))) ↔ y=y₀ := funext_iff.symm
      simp only [iff,ite_mul,one_mul,zero_mul,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      rfl
    _ = _ := by
      simp_rw [colour_checks code q conn root]
      exact sum_constant root (fun f=>∏i,L i (f i))

end Hierarchy.Probe
end

end OAI
