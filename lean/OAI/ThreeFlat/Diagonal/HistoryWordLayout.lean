import OAI.ThreeFlat.Diagonal.HistoryPortBit
import OAI.ThreeFlat.Diagonal.SlotRefinement

namespace OAI
/-! # Stages with ordinary binary words on all incident edges -/

namespace ThreeFlat.Diagonal.HistoryContraction

open MotifBinaryPacking LinearAlgebra.SpectralBooks
open scoped Classical BigOperators
noncomputable section

variable {V E U D F Pins : Type} [Fintype V] [Fintype E] [Fintype U] [Fintype D] [CommSemiring F]

/-- Only boundary widths and directly enumerable port orders are required.
The external pins and their independent relocation are carried separately. -/
structure WordLayout (G : PortGraph V E) (w : E → ℕ) (Pins : Type) where
  count : V → ℕ
  order : ∀ v, Fin (count v) ≃ G.Port v
  ext : V → ℕ
  pin : ∀ v, Pins → Fin (ext v) → Bool

namespace WordLayout

variable {G : PortGraph V E} {w : E → ℕ} (L : WordLayout G w Pins)

abbrev shape (G : PortGraph V E) (w : E → ℕ) := SlotRefinement.shape G (fun e => Fin (2^w e))

def ports : PortLayout (shape G w) Pins where
  count := L.count
  port := L.order
  width := w
  binary a := (word (w a)).symm
  ext := L.ext
  pin := L.pin

variable {T : PortGraph U D} {b : D → ℕ} (W : WordLayout T b Pins)
    (own : V → U) (num : U → ℕ) (ord : ∀ u, Fin (num u) ≃ {v // own v=u})

/-- Binary private variables in old child order, and the half-word pins left
on the parent's public interface. -/
def prior (u : U) := ∑ i : Fin (num u), L.ports.halfBits (ord u i).val

def argSize (u : U) := prior L own num ord u + W.ports.halfBits u

def oldPin (u : U) (i : {v // own v=u}) (a : G.Port i.val) (j : Fin (w a.1.1)) : Fin (argSize L W own num ord u) :=
  let ix := (ord u).symm i
  let eq := congrArg (fun i : {v // own v=u} => L.ports.halfBits i.val) ((ord u).apply_symm_apply i)
  (finSigmaFinEquiv (n:= fun x => L.ports.halfBits (ord u x).val) ⟨ix,Fin.cast eq.symm (L.ports.portBit i.val a j)⟩).castAdd _

def newPin (u : U) (a : T.Port u) (j : Fin (b a.1.1)) : Fin (argSize L W own num ord u) :=
  Fin.natAdd (prior L own num ord u) (W.ports.portBit u a j)

/-- Assemble a physical rewrite at the selected term. Its type records that
both half-incidence alphabets use their actual word widths; every argument
pointer is supplied deterministically by the two port prefix tables. -/
structure Step (u : U) where
  net : Tree F (argSize L W own num ord u)
  value : ((i : {v // own v=u}) → G.State (fun a => Fin (2^w a)) i.val) → T.State (fun a => Fin (2^b a)) u → F
  eval : ∀ (pin : Fin (argSize L W own num ord u) → Bool) x y,
    (∀ i a j, pin (oldPin L W own num ord u i a j) = (x i a).val.testBit j.val) →
    (∀ a j, pin (newPin L W own num ord u a j) = (y a).val.testBit j.val) → net.compile.eval pin = value x y

end WordLayout

/-! This version accepts the actual target `Shape` of a rewrite. The typed
old/new readers skip the inherited external prefix of the selected site. -/
namespace PortLayout

variable {S : Shape} (L : PortLayout S Pins) {R : Rewrite S F} {t : Fin R.count} (W : PortLayout (R.target t) Pins)
  (num : (R.target t).Site → ℕ) (ord : ∀ v, Fin (num v) ≃ {i // R.owner t i=v})

def stageOld (v : (R.target t).Site) (u : {i // R.owner t i=v}) (a : S.graph.Port u.val) (j : Fin (L.width a.1.1)) :
    Fin (L.hidden num ord v+W.halfBits v) := (L.oldBit num ord v u a j).castAdd _

def stageNew (v : (R.target t).Site) (a : (R.target t).graph.Port v) (j : Fin (W.width a.1.1)) :
    Fin (L.hidden num ord v+W.halfBits v) := Fin.natAdd (L.hidden num ord v) (W.portBit v a j)

def wordsStage (kernel : ∀ v, Tree F (L.hidden num ord v+W.halfBits v))
    (trueKernel : ∀ v (pin : Fin (L.hidden num ord v+W.halfBits v) → Bool) x y,
      (∀ i a j, pin (L.stageOld W num ord v i a j) = L.binary a.1.1 (x i a) j) →
      (∀ a j, pin (L.stageNew W num ord v a j) = W.binary a.1.1 (y a) j) → (kernel v).compile.eval pin = R.kernel t v x y) :
    Stage R t L.form (L.inherit W num ord).form :=
  L.stage (L.inherit W num ord) num ord (L.inheritedIndex W num ord) (L.inherited_pin W num ord) kernel <| by
    intro v g y
    apply trueKernel
    · intro i a j
      exact (Fin.append_left ..).trans (L.oldBit_read num ord v i a j g)
    · intro a j
      exact (Fin.append_right ..).trans (W.portBit_read v y a j)

end PortLayout
end
end ThreeFlat.Diagonal.HistoryContraction

end OAI
