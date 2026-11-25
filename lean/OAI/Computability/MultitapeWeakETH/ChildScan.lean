import OAI.Computability.MultitapeWeakETH.TerminalBanks
import OAI.Computability.VPVNP.PairTraversalNativeLayer

/-! # Recovering a selected compressor node's ordered child list on tape -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid.ChildScan

open IntegerMultiplication Code Carry Staff Strip VPVNP Compression CompressorRecords BurstRAM
open PairSimulation LocalHistory TraversalRows TerminalWords
open private address address_poly address_eq from OAI.Computability.MultitapeWeakETH.TerminalColumns
open scoped Fin.CommRing
noncomputable section

private abbrev RowIndex := (Bits.Word × Bits.Word) × Tally
private abbrev reg : Regime RowIndex := ⟨size,send,Dom.base _⟩

private def start (q : RowIndex) := Bits.short q.1.1.length (Bits.value q.1.1 + q.2.length*Bits.value q.1.2)

private theorem start_poly : Poly start := by
  have base : Figure reg (fun q => Bits.value q.1.1) := ⟨_,(Easy.fst.compose Easy.fst).poly,fun _ => rfl⟩
  have stride : Figure reg (fun q => Bits.value q.1.2) := ⟨_,(Easy.fst.compose Easy.snd).poly,fun _ => rfl⟩
  have i : Realizes reg (fun q => q.2.length) := by
    change Poly (fun q : RowIndex => tally q.2.length)
    simpa only [recover_tally] using (Easy.snd (X:=Bits.Word × Bits.Word) (Y:=Tally)).poly
  have w : Realizes reg (fun q => q.1.1.length) := by
    change Poly (fun q : RowIndex => tally q.1.1.length)
    have e := (Easy.ruler (Easy.fst (X:=Bits.Word × Bits.Word) (Y:=Tally) |>.compose Easy.fst)).poly
    convert e using 1
    funext q
    rw [← recover_tally (ruler q.1.1),ruler_length]
  exact (base.added ((Figure.of_spoken i).multiplied stride)).write w

private theorem start_eq {w : ℕ} (base stride : Word w) (i : ℕ) :
    start ((wordBits base,wordBits stride),tally i) = wordBits (base+(i : Word w)*stride) := by
  apply Bits.word_inject
  · simp [start]
  · simp [start,value_native,Fin.val_add,Fin.val_mul,Fin.val_natCast,Nat.add_mod_mod,Nat.mod_mul_mod]

variable {A : Type} [Codec A] (read : A × Bits.Word → Bits.Word)

abbrev Query (A : Type) := ((A × Bits.Word) × Tally) × Tally

/-- The previous level's header publishes its count array, child array, and row stride.
The caller supplies one polynomial cap for both child counts and child ordinals. -/
def children (q : Query A) : List Tally :=
  let ctx := q.1.1.1
  let head := q.1.1.2
  let fetch (j : ℕ) := read (ctx,address (head,tally j))
  let cap := q.1.2
  let n := capped (read (ctx,address (fetch 24,q.2)),cap)
  scan read (((ctx,start ((fetch 25,fetch 26),q.2)),cap),n)

theorem children_poly [Inhabited A] (hr : Poly read) : Poly (children read) := by
  have ctx : Poly (fun q : Query A => q.1.1.1) := by fun_prop
  have head : Poly (fun q : Query A => q.1.1.2) := by fun_prop
  have cap : Poly (fun q : Query A => q.1.2) := by fun_prop
  have fetch (j : ℕ) := (ctx.pair ((head.pair (Code.Poly.const (tally j))).compose address_poly)).compose hr
  have size := ((ctx.pair (((fetch 24).pair Easy.snd.poly).compose address_poly)).compose hr).pair cap |>.compose capped_poly
  have st := ((((fetch 25).pair (fetch 26)).pair Easy.snd.poly).compose start_poly)
  exact (((ctx.pair st).pair cap).pair size).compose (scan_poly read hr)

variable {w : ℕ} (ctx : A) (m : Memory w) (rd : ∀ h : Word w, read (ctx,wordBits h)=wordBits (m h.val))

include rd
omit [Codec A] in
theorem children_eq (pub : Fin 6 → Word w) (head : Word w) (i cap : ℕ) (xs : List ℕ)
    (count : m (head+24).val=pub 3) (base : m (head+25).val=pub 5) (stride : m (head+26).val=pub 4)
    (len : xs.length ≤ cap) (idBound : ∀ x ∈ xs, x ≤ cap ∧ x < 2^w)
    (endRow : (rowAt pub (i : Word w)).val+xs.length ≤ 2^w)
    (stored : rowRepresents m (countAt pub (i : Word w)) (rowAt pub (i : Word w)) (xs.map (fun x : ℕ => (x : Word w)))) :
    children read (((ctx,wordBits head),tally cap),tally i) = xs.map tally := by
  let row := rowAt pub (i : Word w)
  have n : (m (countAt pub (i : Word w)).val).val = xs.length := stored.1.trans (List.length_map ..)
  simp only [children,address_eq,rd,Nat.cast_ofNat,count,base,stride,start_eq,capped,value_native,tally_length]
  change scan read (((ctx,wordBits row),tally cap),tally (min (m (countAt pub (i : Word w)).val).val cap)) = _
  rw [n,Nat.min_eq_left len,scan_eq read ctx m (fun a => (congrArg Bits.value (rd a)).trans (value_native _))]
  apply List.ext_getElem
  · simp
  · intro j hj hk
    have jlt : j<xs.length := by simpa using hk
    have ok := idBound xs[j] (List.getElem_mem jlt)
    have loc : (row + (j : Word w)).val = row.val+j := by
      rw [Fin.val_add,Fin.val_natCast,Nat.add_mod_mod,Nat.mod_eq_of_lt]; omega
    have datum := stored.2 ⟨j,by simpa using jlt⟩
    simp only [List.getElem_map] at datum
    change m (row.val+j) = (xs[j] : Word w) at datum
    simp only [List.getElem_ofFn,List.getElem_map,loc,datum,Fin.val_natCast,Nat.mod_eq_of_lt ok.2,Nat.min_eq_left ok.1]

end
end OAI.Computability.MultitapeWeakETH.NativeGrid.ChildScan
