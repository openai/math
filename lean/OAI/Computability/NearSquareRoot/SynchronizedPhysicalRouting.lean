import OAI.Computability.NearSquareRoot.SynchronizedNumberedBits
import OAI.Computability.NearSquareRoot.SynchronizedBatchRouteRead

/-! # Translating a completed borrowing route to original block address order

The two sides of an active/idle routing table have different layouts. One side
interleaves the bit and pair number. The other side is the axis-peeled borrowing
address. Each source/destination pair is translated to the original physical
block address before the tape compiler reads it.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.RoutingTable

open IntegerMultiplication Code Staff Strip

abbrev Strides := (Tally × Tally) × Tally
abbrev Row := Tally × Tally

def translated (s : Strides) (t : Row) : Row :=
  let p := s.1.1.length
  let m := s.1.2.length
  let lo := s.2.length
  (tally (FieldSplit.join p m (t.2.length/m) (t.2.length%m)),
    tally (FieldSplit.join lo 2 (t.1.length/2) (t.1.length%2)))

private def query (X : Type) [Codec X] : Regime X := ⟨Code.size,send,Dom.base _⟩

private theorem param {X : Type} [Codec X] (f : X → Tally) (F : Easy f) :
    Realizes (query X) (fun x => (f x).length) := by
  have h : (query X).Has id := (query X).self
  simpa only [Realizes, Function.comp_def, id_eq, recover_tally] using h.ez F

theorem translated_poly : Poly (fun x : Strides × Row => translated x.1 x.2) := by
  have P := param (fun x : Strides × Row => x.1.1.1) (by fun_prop)
  have M := param (fun x : Strides × Row => x.1.1.2) (by fun_prop)
  have L := param (fun x : Strides × Row => x.1.2) (by fun_prop)
  have S := param (fun x : Strides × Row => x.2.1) (by fun_prop)
  have T := param (fun x : Strides × Row => x.2.2) (by fun_prop)
  exact (Regime.Has.pair (FieldSplit.join_realizes P M (T.dividing M) (T.rem M))
    (FieldSplit.join_realizes L (.fix 2) (S.dividing (.fix 2)) (S.rem (.fix 2))))

def physicalTables (s : Strides) (d : Dimensions) : List Row × List Row :=
  let rows := (bothTables (prepareHeader d)).1.map (translated s)
  (rows,rows.map Prod.swap)

theorem physicalTables_poly : Poly (fun x : Strides × Dimensions => physicalTables x.1 x.2) := by
  have raw := (Easy.snd (X := Strides) (Y := Dimensions)).poly.compose (prepareHeader_poly.compose bothTables_poly)
  have rows := (Easy.fst.poly.pair raw.fstCompose).compose (Poly.push default default translated_poly)
  exact rows.pair (rows.compose (Poly.maps _ Easy.exchange.poly))

theorem physicalTables_machine :
    PolyTreeMachine size send (fun x : Strides × Dimensions => send (physicalTables x.1 x.2)) :=
  polyTreeMachine_of_BT (physicalTables_poly.on (Dom.base _)) (Dom.base _)

end ShortFourier.RoutingTable

namespace BoxFin

open SynchronizedBlocks ShortFourier IntegerMultiplication IntegerMultiplication.Code

variable {k L : ℕ} {box : List (ℕ × ℕ)} (hb : BoxShape.Valid k L box)
  [∀ i, NeZero (modulus box i)] (j : Fin (box.length/4))

abbrev blockModulus (i : Fin (count j)) := modulus box (axis j i)
abbrev blockPadding (i : Fin (count j)) := padding box (axis j i)

include hb in
omit [∀ i, NeZero (modulus box i)] in
private theorem radix_width (i : Fin (count j)) : blockFieldRadix box j i = blockModulus j i + blockPadding j i :=
  (Nat.add_sub_of_le (hb.axisBounds _ (List.get_mem box (axis j i))).2.2.2).symm

/-- Undo row-major peeling in the generated raw table. -/
theorem physicalRank_unpeel (i : Fin (count j)) (x : BlockAddress (BoxAxis box) j) :
    let p := CRT.«prefix» (blockFieldRadix box j) i
    let m := blockFieldRadix box j i
    let raw := (BatchWord.blockRank (blockModulus j) (blockPadding j) (blockSpectators hb j) i x).val
    FieldSplit.join p m (raw/m) (raw%m) = (blockAddressRank hb j x).val := by
  let addr := BatchWord.axisLayout (blockModulus j) (blockPadding j) (blockSpectators hb j) i
  let m := blockModulus j i + blockPadding j i
  let u := addr x
  let col := (finSumFinEquiv u.2).val
  have hc : col < m := (finSumFinEquiv u.2).isLt
  have hm : 0 < m := Nat.zero_lt_of_lt hc
  have hi := blockAxisLayout_inverse hb j i (addr x)
  change (blockAddressRank hb j (addr.symm (addr x))).val =
    FieldSplit.join _ (blockFieldRadix box j i) u.1.val col at hi
  rw [Equiv.symm_apply_apply] at hi
  dsimp only
  rw [radix_width hb j i] at hi ⊢
  change FieldSplit.join _ m ((col+m*u.1.val)/m) ((col+m*u.1.val)%m) = _
  rw [Nat.add_mul_div_left _ _ hm,Nat.div_eq_of_lt hc,Nat.zero_add,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hc]
  exact hi.symm

def routingStrides (i : Fin (count j)) : RoutingTable.Strides :=
  ((tally (CRT.«prefix» (blockFieldRadix box j) i), tally (blockFieldRadix box j i)),tally (lowRadix j))

theorem translated_row (i : Fin (count j)) (u : Fin 2) (s : Fin (Fintype.card (BlockAddress (BoxAxis box) j)/2))
    (x : BlockAddress (BoxAxis box) j) :
    RoutingTable.translated (routingStrides j i) (tally (2*s.val+u.val),
      tally ((BatchWord.blockRank (blockModulus j) (blockPadding j) (blockSpectators hb j) i) x).val) =
      (tally ((blockAddressRank hb j) x).val,
        tally ((blockAddressRank hb j) ((numberedBits hb j).symm (u,s))).val) := by
  unfold RoutingTable.translated routingStrides
  simp only [tally_length]
  rw [physicalRank_unpeel hb j i x, numberedBits_invert hb j u s]
  congr 2
  unfold FieldSplit.join
  rw [Nat.mul_add_div (by decide : 0 < 2), Nat.div_eq_of_lt u.isLt, Nat.add_zero, Nat.mul_add_mod_self_left,
    Nat.mod_eq_of_lt u.isLt]

/-- In packed block order the program emits the full graph of the decoded routing
permutation, in both directions. The enumeration ranges over every physical cell. -/
theorem physicalTables_graph (w : Fin (count j) → ℕ)
    (har : ∀ i, blockModulus j i ≤ 2^(w i))
    (hborrow : ∀ i, 2*2^(w i) ≤ 8*blockModulus j i)
    (he : Even (Fintype.card (BlockAddress (BoxAxis box) j))) (i : Fin (count j)) (b : Fin 15) :
    let a := blockModulus (box := box) j
    let c := blockPadding (box := box) j
    let d := RoutingTable.dimensions (BatchWord.fiberCount a c i) (a i) (c i) (2^w i) b
    let M := BatchWord.completeMatching a c w (blockSpectators hb j) har hborrow he i b
    let rank := blockAddressRank hb j
    let enumerate := (BatchWord.interleave he).symm.trans M
    let route := M.symm.trans (numberedBits hb j).symm
    let rows := List.ofFn (fun z => (tally (rank (enumerate z)).val,tally (rank (route (enumerate z))).val))
    RoutingTable.physicalTables (routingStrides j i) d = (rows,rows.map Prod.swap) := by
  let a := blockModulus (box := box) j
  let c := blockPadding (box := box) j
  let M := BatchWord.completeMatching a c w (blockSpectators hb j) har hborrow he i b
  let E := BatchWord.interleave he
  have H := BatchWord.routeTables_eq a c w (blockSpectators hb j) har hborrow he i b
  suffices Hrows :
      (BatchWord.routeTables a c w i b).1.map (RoutingTable.translated (routingStrides j i)) =
        List.ofFn (fun z => (tally ((blockAddressRank hb j) (M (E.symm z))).val,
          tally ((blockAddressRank hb j) ((numberedBits hb j).symm (E.symm z))).val)) by
    dsimp only [RoutingTable.physicalTables]
    apply congrArg (fun xs : List RoutingTable.Row => (xs,xs.map Prod.swap))
    rw [show (RoutingTable.bothTables (RoutingTable.prepareHeader _)).1 = (BatchWord.routeTables a c w i b).1 from rfl,Hrows]
    apply congrArg List.ofFn
    funext z
    simp only [Equiv.trans_apply,Equiv.symm_apply_apply]
    rfl
  rw [H,List.map_ofFn]
  apply congrArg List.ofFn
  funext z
  obtain ⟨⟨u,s⟩,rfl⟩ := E.surjective z
  simp only [Function.comp_apply,Equiv.symm_apply_apply]
  have hv : (E (u,s)).val = 2*s.val+u.val := Nat.add_comm ..
  rw [hv]
  change RoutingTable.translated _ (_,tally ((BatchWord.blockRank a c (blockSpectators hb j) i) (M (E.symm (E (u,s))))).val) = _
  rw [Equiv.symm_apply_apply]
  exact translated_row hb j i u s (M (u,s))

end BoxFin

end NearSquareRoot
end Computability
end OAI
