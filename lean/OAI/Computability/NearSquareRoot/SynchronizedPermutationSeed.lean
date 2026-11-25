import OAI.Computability.NearSquareRoot.SynchronizedPermutationActiveIDs
import OAI.Computability.NearSquareRoot.SynchronizedPermutationPrepare

/-! # Building a physical switch-pass header from its directed Fourier row -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Benes.PackedBatchHeader
open IntegerMultiplication Code Staff Strip Carry ShortFourier.BatchWord Controlled

abbrev RowPass := PermDirectory.Query × (Bool × Tally) × Tally

private def scale : Regime Tally := ⟨Code.size,send,Dom.base _⟩

private theorem scale_value : Realizes scale (fun x : Tally => x.length) := by
  change Poly (fun x : Tally => tally x.length)
  simpa only [recover_tally] using (Poly.identity (X := Tally))

private theorem logarithm : Realizes scale (fun x : Tally => Nat.clog 2 (x.length+1)) :=
  (Figure.of_spoken (scale_value.plus (.fix 1))).short_log

theorem low_poly (D : ℕ) : Poly (fun x : Tally => tally (payloadBits D x.length)) :=
  (Realizes.fix D).times logarithm

theorem stride_poly : Poly (fun x : Tally => tally (guardWidth x.length)) :=
  (Realizes.fix 7).plus ((Realizes.fix 2).times logarithm)

/-- The pass header includes the row tables, the cutoffs used by the physical
program, and the ordered list of active block numbers. -/
def rowSeed (D : ℕ) (x : RowPass) : Seed :=
  let k := x.1.2.1
  ((x.2.1,(tally (payloadBits D k.length),tally (guardWidth k.length)),k),
    PermDirectory.directory x.1,FieldDirectory.activeRow (x.1,x.2.2,x.2.1.2))

theorem rowSeed_poly (D : ℕ) : Poly (rowSeed D) := by
  have k : Poly (fun x : RowPass => x.1.2.1) := by fun_prop
  have side : Poly (fun x : RowPass => x.2.1) := by fun_prop
  have dirs := (Easy.fst (X := PermDirectory.Query) (Y := (Bool × Tally) × Tally)).poly.compose
    PermDirectory.directory_poly
  have ids := (show Poly (fun x : RowPass => (x.1,x.2.2,x.2.1.2)) by fun_prop).compose
    FieldDirectory.activeRow_poly
  exact (side.pair (((k.compose (low_poly D)).pair (k.compose stride_poly)).pair k)).pair (dirs.pair ids)

theorem rowSeed_eq {k L : ℕ} (hb : BoxShape.Valid k L (CoprimeBox.box k)) (D : ℕ) (dir : Bool)
    (row : Tally) (side : Bool) (j β : ℕ) :
    rowSeed D ((dir,tally k,row),(side,tally j),tally β) =
      (((side,tally j),(tally (payloadBits D k),tally (guardWidth k)),tally k),
        PermDirectory.directory (dir,tally k,row),
        List.ofFn (fun q => tally (FieldDirectory.selectBlock k β j
          (BoxFin.physicalWidth (box := CoprimeBox.box k)) q).val)) := by
  simp only [rowSeed,tally_length,FieldDirectory.activeRow_eq hb dir row β j]


/-- Join an arbitrary Fourier row's generated switch tables with its own pass
parameters. The compiler emits both whole-address permutations and the switch plan. -/
def fullHeader (D : ℕ) (x : RowPass) : Staging := prepare (rowSeed D x)

@[fun_prop] theorem fullHeader_poly (D : ℕ) : Poly (fullHeader D) :=
  (rowSeed_poly D).compose prepare_poly

variable {k L : ℕ} (hb : BoxShape.Valid k L (CoprimeBox.box k)) (D : ℕ) (dir : Bool)
  (row : Tally) (side : Bool) (j β : ℕ)
  (tables : Fin ((CoprimeBox.box k).length/4) → RawTable)

include hb in
theorem fullHeader_eq
    (entries : ∀ q, (PermDirectory.directory (dir,tally k,row))[q.val]? =
      some (tally (BoxFin.physicalWidth (box := CoprimeBox.box k) q),tables q)) :
    let w := BoxFin.physicalWidth (box := CoprimeBox.box k)
    fullHeader D ((dir,tally k,row),(side,tally j),tally β) =
      prepare (seed w tables (FieldDirectory.selectBlock k β j w) side j k (guardWidth k) (payloadBits D k)) := by
  intro w
  rw [fullHeader,rowSeed_eq hb]
  apply congrArg prepare
  apply congrArg (fun dirs : Directory => (((side,tally j),(tally (payloadBits D k),tally (guardWidth k)),tally k),
    dirs,List.ofFn (fun q => tally (FieldDirectory.selectBlock k β j w q).val)))
  have len := congrArg List.length (PermHeader.rowWidths hb dir row)
  simp only [List.length_map,List.length_ofFn] at len
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using len
  · intro i hi _
    let q : Fin ((CoprimeBox.box k).length/4) := ⟨i,len ▸ hi⟩
    have e := entries q
    simpa only [List.getElem_ofFn] using (Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans e))

end Benes.PackedBatchHeader

end NearSquareRoot
end Computability
end OAI
