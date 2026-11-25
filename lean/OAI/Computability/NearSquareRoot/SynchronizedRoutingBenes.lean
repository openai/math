import OAI.Computability.NearSquareRoot.SynchronizedPhysicalRouting
import OAI.Computability.NearSquareRoot.CRTTableWordEquiv

/-! # Beneš input tables for the routed Walsh stages -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.RoutingTable

open IntegerMultiplication Code

/-- Binary fields in the most-significant-first order read by the Beneš compiler. -/
def binaryRows (d : Tally) (rows : List Row) : Benes.RawTable :=
  rows.map (fun t => (CRTTable.wordField (d,t.1),CRTTable.wordField (d,t.2)))

theorem binaryRows_poly : Poly (fun x : Tally × List Row => binaryRows x.1 x.2) := by
  have h (get : Row → Tally) (H : Easy get) :
      Poly (fun p : Tally × Row => CRTTable.wordField (p.1,get p.2)) :=
    (Easy.fst.pair (Easy.snd.compose H)).compose CRTTable.wordField_easy |>.poly
  exact Poly.push [] default ((h _ Easy.fst).pair (h _ Easy.snd))

private theorem field_val {d : ℕ} (i : Fin (2^d)) :
    CRTTable.wordField (tally d,tally i.val) = List.ofFn (CRTTable.wordEquiv d i) := by
  rw [CRTTable.wordField_eq, CRTTable.ofFn_wordEquiv]
  simp [Bits.short,Nat.mod_eq_of_lt i.isLt]

/-- The order of rows is arbitrary once the list enumerates every source index exactly once. -/
theorem binaryRows_represents {n d : ℕ} {A : Type} (enum : Fin n ≃ A)
    (rank : A ≃ Fin (2^d)) (p : Equiv.Perm A) :
    let e := rank.trans (CRTTable.wordEquiv d)
    Benes.RawRepresents (e.symm.trans (p.trans e))
      (binaryRows (tally d) (List.ofFn fun z =>
        (tally (rank (enum z)).val,tally (rank (p (enum z))).val))) := by
  let e := rank.trans (CRTTable.wordEquiv d)
  refine ⟨List.ofFn (enum.trans e), List.nodup_ofFn.mpr (enum.trans e).injective,
    (fun x => List.mem_ofFn.mpr ((enum.trans e).surjective x)),?_⟩
  rw [binaryRows,List.map_ofFn,List.map_ofFn]
  apply congrArg List.ofFn
  funext z
  simp only [Function.comp_apply,field_val,Equiv.trans_apply]
  change (_,List.ofFn (e (p (enum z)))) = (_,List.ofFn (e (p (e.symm (e (enum z))))))
  rw [Equiv.symm_apply_apply]
  rfl

theorem binaryRows_swap_represents {n d : ℕ} {A : Type} (enum : Fin n ≃ A)
    (rank : A ≃ Fin (2^d)) (p : Equiv.Perm A) :
    let e := rank.trans (CRTTable.wordEquiv d)
    Benes.RawRepresents (e.symm.trans (p.symm.trans e))
      (binaryRows (tally d) ((List.ofFn fun z =>
        (tally (rank (enum z)).val,tally (rank (p (enum z))).val)).map Prod.swap)) := by
  have h := binaryRows_represents (enum.trans p) rank p.symm
  rw [List.map_ofFn]
  simpa only [Function.comp_def,Prod.swap_prod_mk,Equiv.trans_apply,Equiv.symm_apply_apply] using h

/-- Both directions of a physical routed slot, ready for the Beneš compiler. -/
def rawRouting (p : (Strides × Dimensions) × Tally) : Benes.RawTable × Benes.RawTable :=
  let t := physicalTables p.1.1 p.1.2
  (binaryRows p.2 t.1,binaryRows p.2 t.2)

private theorem both_with_parameter {X Y Z T : Type} [Codec X] [Codec Y] [Codec Z] [Codec T]
    (f : X → Y × Y) (g : Z × Y → T) (hf : Poly f) (hg : Poly g) :
    Poly (fun x : X × Z => (g (x.2,(f x.1).1),g (x.2,(f x.1).2))) := by
  have rows := (Easy.fst (X := X) (Y := Z)).poly.compose hf
  have width := (Easy.snd (X := X) (Y := Z)).poly
  exact ((width.pair rows.fstCompose).compose hg).pair ((width.pair rows.sndCompose).compose hg)

theorem rawRouting_poly : Poly rawRouting :=
  both_with_parameter (fun p : Strides × Dimensions => physicalTables p.1 p.2)
    (fun p : Tally × List Row => binaryRows p.1 p.2) physicalTables_poly binaryRows_poly

theorem rawRouting_machine :
    PolyTreeMachine size send (fun x => send (rawRouting x)) :=
  polyTreeMachine_of_BT (rawRouting_poly.on (Dom.base _)) (Dom.base _)

end ShortFourier.RoutingTable

namespace BoxFin

open SynchronizedBlocks ShortFourier IntegerMultiplication IntegerMultiplication.Code
variable {k L : ℕ} {box : List (ℕ × ℕ)} (hb : BoxShape.Valid k L box)
  [∀ i, NeZero (modulus box i)] (j : Fin (box.length/4))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
/-- The global compiler's two routed permutations have constructive Beneš raw tables
on every address bit of the block, including the idle and borrowed cells. -/
theorem rawRouting_benes (w : Fin (count j) → ℕ)
    (har : ∀ i, blockModulus j i ≤ 2^(w i))
    (hborrow : ∀ i, 2*2^(w i) ≤ 8*blockModulus j i)
    (he : Even (Fintype.card (BlockAddress (BoxAxis box) j))) (i : Fin (count j)) (b : Fin 15) :
    let a := blockModulus (box := box) j
    let c := blockPadding (box := box) j
    let d := RoutingTable.dimensions (BatchWord.fiberCount a c i) (a i) (c i) (2^w i) b
    let m := BatchWord.completeMatching a c w (blockSpectators hb j) har hborrow he i b
    let perm := m.symm.trans (numberedBits hb j).symm
    let e := (blockBitRank hb j).trans (CRTTable.wordEquiv (physicalWidth j))
    let t := RoutingTable.rawRouting ((routingStrides j i,d), tally (physicalWidth j))
    Benes.RawRepresents (e.symm.trans (perm.trans e)) t.1 ∧
      Benes.RawRepresents (e.symm.trans (perm.symm.trans e)) t.2 := by
  let a := blockModulus (box := box) j
  let c := blockPadding (box := box) j
  let m := BatchWord.completeMatching a c w (blockSpectators hb j) har hborrow he i b
  let enum := (BatchWord.interleave he).symm.trans m
  let perm := m.symm.trans (numberedBits hb j).symm
  have graph := physicalTables_graph hb j w har hborrow he i b
  dsimp only [RoutingTable.rawRouting]
  rw [graph]
  constructor
  · apply RoutingTable.binaryRows_represents (rank := blockBitRank hb j) (p := perm) (enum := enum)
  · apply RoutingTable.binaryRows_swap_represents (rank := blockBitRank hb j) (p := perm) (enum := enum)

end BoxFin

end NearSquareRoot
end Computability
end OAI
