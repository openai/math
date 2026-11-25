import OAI.Computability.BorderVNP.CellDirectoryWire
import OAI.Computability.BorderVNP.PackedWordCircuit

/-! # Public word programs for sparse record packets

The static shape includes the tags, list lengths, and fixed port strides.
Variable fields are binary word expressions. Compiling the shape produces
the actual flat word sequence read by the packet parser.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankPacket

open Word CellSparse ParseBatchSort VPVNP.VerifierNetwork

/-- Three computed operands of a sparse port. -/
structure PortCode (I : Type*) where
  /-- First bit of the port in the cell-local bank. -/
  base : WidthExpr I
  /-- Increment between the starts of consecutive copies. -/
  copyStride : WidthExpr I
  /-- Increment between adjacent lanes of a copy. -/
  laneStride : WidthExpr I

/-- The packet's two scalar operands and two ports of a compact feeder route. -/
structure RouteCode (I : Type*) where
  /-- Histogram letter served by this route. -/
  term : WidthExpr I
  /-- Number of one-copy lanes on this feeder. -/
  lanes : WidthExpr I
  /-- Port of the gathered exterior bundle. -/
  original : PortCode I
  /-- Port indexed by occurrence in the chosen subsequence. -/
  compact : PortCode I

/-- The four sparse record shapes with public arithmetic operands. -/
inductive RecordCode (I : Type*) where
  | zero (copies width : WidthExpr I) (p : PortCode I)
  | equal (copies width : WidthExpr I) (src dst : PortCode I)
  | box (id base copies stride : WidthExpr I)
  | profile (copies : WidthExpr I) (selector : PortCode I) (width : WidthExpr I)
      (hist : List (WidthExpr I)) (routes : List (RouteCode I))

variable {I : Type*} (x : I → ℕ)

/-- Read three computed words as a port in the owning cell's bank. -/
def PortCode.read (p : PortCode I) : Port := ⟨p.base.eval x,p.copyStride.eval x,p.laneStride.eval x⟩

/-- Read the compact routing rule assembled from its public words. -/
def RouteCode.read (r : RouteCode I) : Route :=
  ⟨r.term.eval x,r.lanes.eval x,r.original.read x,r.compact.read x⟩

/-- Actual record produced by a static row shape at these operand values. -/
def RecordCode.read : RecordCode I → Record
  | .zero n w p => .zero (n.eval x) (w.eval x) (p.read x)
  | .equal n w s t => .equal (n.eval x) (w.eval x) (s.read x) (t.read x)
  | .box i b n d => .box (i.eval x) (b.eval x) (n.eval x) (d.eval x)
  | .profile n s w h rs => .profile (n.eval x) (s.read x) (w.eval x) (h.map (WidthExpr.eval x)) (rs.map (RouteCode.read x))

private def portWords (p : PortCode I) := [p.base,p.copyStride,p.laneStride]

private def routeWords (r : RouteCode I) := [r.term,r.lanes] ++ portWords r.original ++ portWords r.compact

/-- The exact tagged wire representation before evaluation of the public operands. -/
def RecordCode.words : RecordCode I → List (WidthExpr I)
  | .zero n w p => [.const 0,n,w] ++ portWords p
  | .equal n w s t => [.const 1,n,w] ++ portWords s ++ portWords t
  | .box i b n d => [.const 2,i,b,n,d]
  | .profile n s w h rs =>
      [.const 3,n] ++ portWords s ++ [w] ++ (.const h.length :: h) ++
        (.const rs.length :: rs.flatMap routeWords)

private theorem routeWords_eval (r : RouteCode I) :
    (routeWords r).map (WidthExpr.eval x) = Packet.route (r.read x) := rfl

/-- The arithmetic word list serializes exactly one real typed packet record. -/
theorem RecordCode.words_eval (r : RecordCode I) :
    r.words.map (WidthExpr.eval x) = Packet.record (r.read x) := by
  cases r with
  | zero | equal | box => rfl
  | profile n s w h rs =>
    simp only [words,read,Packet.record,Packet.vector,Packet.fieldList,List.map_append,
      List.map_cons,List.map_nil,WidthExpr.eval,List.length_map,List.map_flatMap,List.flatMap_map]
    congr 2

/-- The static, flattened expressions for a length-prefixed record list. -/
def tape (rows : List (RecordCode I)) : List (WidthExpr I) :=
  .const rows.length :: rows.flatMap RecordCode.words

/-- Executing the flat tape gives the exact record-count word and payload of the typed packet. -/
theorem tape_eval (rows : List (RecordCode I)) :
    (tape rows).map (WidthExpr.eval x) = Packet.fieldList Packet.record (rows.map (RecordCode.read x)) := by
  simp only [tape,Packet.fieldList,List.map_cons,List.length_map,List.map_flatMap,List.flatMap_map,
    WidthExpr.eval]
  congr 1
  apply List.flatMap_congr
  intro r _
  exact r.words_eval x

variable [Fintype I]

/-- A gate list emits every word of every typed site packet. The input frame,
which can compute addresses shared by many records, is charged only once. -/
theorem exists_tapeFrame {S σ : Type*} [Fintype S] [Fintype σ] (rows : S → List (RecordCode I)) (w : ℕ)
    (source : Frame σ (S × I × Fin w)) :
    let O := Σ s : S, Fin (tape (rows s)).length
    ∃ f : Frame σ (O × Fin w),
      f.size ≤ source.size + 1 + (∑ z : O, (tape (rows z.1))[z.2].nodes) * (100*(w+1)^2) ∧
      ∀ x (z : O),
        let fields := fun i => value (fun j => source.eval x (z.1,i,j))
        (tape (rows z.1))[z.2].Fits w fields →
        value (fun j => f.eval x (z,j)) = (Packet.fieldList Packet.record
          ((rows z.1).map (RecordCode.read fields)))[z.2.val]?.getD 0 := by
  classical
  intro O
  let leaf (z : O) := ((tape (rows z.1))[z.2].frame w).subst
    (Frame.initial (fun i : I × Fin w => (z.1,i)))
  obtain ⟨joint,hs,he⟩ := Crossing.exists_parallelFrames leaf
  let pins (i : O × Fin w) : Σ _ : O, Fin w := ⟨i.1,i.2⟩
  refine ⟨(joint.select pins).subst source, ?_, ?_⟩
  · have hl (z : O) : (leaf z).size ≤ (tape (rows z.1))[z.2].nodes * (100*(w+1)^2) := by
      simp only [leaf,Frame.subst_size,Frame.initial_size,zero_add]
      exact (tape (rows z.1))[z.2].frame_size w
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun t _ => hl t)
    rw [← Finset.sum_mul] at hsum
    simp only [Frame.subst_size,Frame.select_size]
    exact (Nat.add_le_add_left (hs.trans (Nat.add_le_add_left hsum 1)) _).trans_eq (by omega)
  · intro x z fields hfit
    let input := fun p : I × Fin w => source.eval x (z.1,p)
    have hv : (fun j => ((joint.select pins).subst source).eval x (z,j)) =
        ((tape (rows z.1))[z.2].frame w).eval input := by
      funext j
      simp [pins,he,leaf,input]
      congr 1
      funext k
      simp
    rw [hv,(tape (rows z.1))[z.2].frame_value w input hfit, ← tape_eval fields (rows z.1)]
    simp [fields,input]

end Packing.BankPacket

end BorderVNP
end Computability
end OAI
