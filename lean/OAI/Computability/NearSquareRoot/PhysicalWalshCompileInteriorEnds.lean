import OAI.Computability.NearSquareRoot.PhysicalWalshCompileInteriorFrame
import OAI.Computability.NearSquareRoot.PhysicalWalshAgendaOps

/-! # Termination of the compiled interior pass for arbitrary native clocks -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileInterior

open IntegerMultiplication Code Space PhysicalWalsh PhysicalWalshNode Interior SwapPrefix
open PhysicalWalshCompileXorRoute PhysicalWalshCompile

/-- Resource bounds may depend on all input data. The command remains fixed. -/
def Ends {I : Type} (c : Cmd) (q r : I → Tree) : Prop :=
  ∃ t s : I → ℕ, ClosedRuns c t s q r

private theorem from_scans {I X Y : Type} [Codec X] [Codec Y] {c : Cmd} {f : X → Y}
    (h : Scans c f) (x : I → X) : Ends c (fun i => send (x i)) (fun i => send (f (x i))) := by
  obtain ⟨C,run⟩ := h
  exact ⟨fun i => size (x i),fun i => size (x i),C,fun i => run (x i)⟩

private theorem join_ends {I : Type} {q r v : I → Tree} {c d : Cmd}
    (h : Ends c q r) (g : Ends d r v) : Ends (c.join d) q v := by
  obtain ⟨_,_,run⟩ := h
  obtain ⟨_,_,run'⟩ := g
  exact ⟨_,_,AgendaOps.compose run run'⟩

private theorem left_ends {I : Type} {q r : I → Tree} {c : Cmd} (h : Ends c q r) (v : I → Tree) :
    Ends (left c) (fun i => .fork (q i) (v i)) (fun i => .fork (r i) (v i)) := by
  obtain ⟨_,_,run⟩ := h
  exact ⟨_,_,AgendaOps.left run v⟩

/-- The same two scans preserve a descriptor even if the intervening
native program takes an input-dependent amount of work. -/
private theorem chain_ends {K : Kit} {R : ℕ} (kit : Legal K R) {I : Type}
    (h : I → Header.Wire) (x y z : I → List Dusk.Pair) {c d : Cmd}
    (first : Ends c (fun i => send (h i,x i)) (fun i => send (y i)))
    (second : Ends d (fun i => send (h i,y i)) (fun i => send (z i))) :
    Ends (K.chain c d) (fun i => send (h i,x i)) (fun i => send (z i)) :=
  join_ends (join_ends (join_ends (from_scans kit.saves (fun i => (h i,x i)))
    (left_ends first (fun i => send (h i)))) (from_scans kit.swaps (fun i => (y i,h i)))) second

/-- Unrestricted correctness at the padded native boundary. -/
def NativeTotalOn (a W : ℕ) (pred : PhysicalWalshNode.Shape → Prop) (c : Cmd) : Prop :=
  Ends c (fun i : {t : XorInput W // pred t.shape} => .fork (rawHeader a W i.val.shape) (send (padded (a:=a) i.val)))
    (fun i => send (stream (paddedSize (a+1) W i.val.shape) (moved (a:=a) i.val)))

/-- Unrestricted correctness at the original real-lane boundary. -/
def TotalOn (a W : ℕ) (ha : 4 ≤ a) (pred : PhysicalWalshNode.Shape → Prop) (c : Cmd) : Prop :=
  Ends c (fun i : {t : XorInput W // pred t.shape} =>
    send (Header.wire (a+1) i.val.shape,laneFlat (a+1) W i.val.shape i.val.row))
    (fun i => send (laneFlat (a+1) W i.val.shape (PhysicalWalshNode.xor a (axes a ha) i.val.shape i.val.row)))

theorem large_frame_total {K : Kit} {R a W : ℕ} (hk : Legal K R)
    (ha : 4 ≤ a) {pred : PhysicalWalshNode.Shape → Prop} {pad head core crop : Cmd}
    (nativeRun : NativeTotalOn a W pred core)
    (padRun : let s (i : {t : XorInput W // pred t.shape}) := i.val.shape
      Ends pad (fun i => send (Header.wire (a+1) (s i),laneFlat (a+1) W (s i) i.val.row))
        (fun i => send (Header.wire (a+1) (s i),padded (a:=a) i.val)))
    (headRun : let s (i : {t : XorInput W // pred t.shape}) := i.val.shape
      Ends head (fun i => send (Header.wire (a+1) (s i),padded (a:=a) i.val))
        (fun i => .fork (rawHeader a W (s i)) (send (padded (a:=a) i.val))))
    (cropRun : let s (i : {t : XorInput W // pred t.shape}) := i.val.shape
      Ends crop (fun i => send (Header.wire (a+1) (s i),stream (paddedSize (a+1) W (s i)) (moved (a:=a) i.val)))
        (fun i => send (laneFlat (a+1) W (s i) (moved (a:=a) i.val)))) :
    TotalOn a W ha pred (pad.join (K.chain (head.join core) crop)) := by
  let s (i : {t : XorInput W // pred t.shape}) := i.val.shape
  let x (i : {t : XorInput W // pred t.shape}) := padded (a:=a) i.val
  let y (i : {t : XorInput W // pred t.shape}) := stream (paddedSize (a+1) W (s i)) (moved (a:=a) i.val)
  let z (i : {t : XorInput W // pred t.shape}) := laneFlat (a+1) W (s i) (moved (a:=a) i.val)
  have run := join_ends padRun (chain_ends hk (fun i => Header.wire (a+1) (s i)) x y z
    (join_ends headRun nativeRun) cropRun)
  have eqn (i : {t : XorInput W // pred t.shape}) : z i =
      laneFlat (a+1) W (s i) (PhysicalWalshNode.xor a (axes a ha) (s i) i.val.row) :=
    actual_output a W ha (s i) i.val.positive i.val.row
  simp only [eqn] at run
  exact run

end PhysicalWalshCompileInterior

end NearSquareRoot
end Computability
end OAI
