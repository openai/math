import OAI.Computability.NearSquareRoot.InterchangeROMTableEffective
import OAI.Computability.NearSquareRoot.InterchangeROMTableSeries
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPRMatrix

/-! # From a repair ROM slot to a physical matrix table

Each repair slot is a flat row-major blob. Both physical orders are explicit
lists of row numbers. Compiling the table is primitive recursive jointly in
the modulus, slot number, row pitch, both orders and every word on the ROM.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMTable

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open NearSquareRoot.InterchangeROMRepair

/-- Gather the ground residues in exactly the two supplied coordinate orders. -/
def gatherRows (p : ℕ) (outIdx inIdx : List ℕ) (f : Raw.Mat) : List (List ℕ) :=
  outIdx.map fun i => inIdx.map fun j => f i j % (p+1)

variable {X : Type} [Primcodable X]

theorem primrec_gatherRows {p : X → ℕ} {outIdx inIdx : X → List ℕ} {f : X → Raw.Mat}
    (hp : Primrec p) (ho : Primrec outIdx) (hi : Primrec inIdx) (hf : Raw.EntryPR f) :
    Primrec fun x => gatherRows (p x) (outIdx x) (inIdx x) (f x) := by
  apply Primrec.list_map ho
  change Primrec fun v : X × ℕ => (inIdx v.1).map fun j => f v.1 v.2 j % (p v.1+1)
  apply Primrec.list_map (hi.comp Primrec.fst)
  exact (Primrec.nat_mod.comp (hf.eval (Primrec.fst.comp Primrec.fst)
    (Primrec.snd.comp Primrec.fst) Primrec.snd)
    (Primrec.succ.comp (hp.comp (Primrec.fst.comp Primrec.fst)))).to₂

def slotTable (p pitch slot : ℕ) (tape : List (List ℕ)) (outIdx inIdx : List ℕ) :
    List (Tree × Tree) :=
  matrixTable (p+1) inIdx.length
    (gatherRows p outIdx inIdx (Raw.read pitch (tape.getD slot [])))

theorem primrec_spelled_slotTable {p pitch slot : X → ℕ} {tape : X → List (List ℕ)}
    {outIdx inIdx : X → List ℕ} (hp : Primrec p) (hc : Primrec pitch) (hs : Primrec slot)
    (ht : Primrec tape) (ho : Primrec outIdx) (hi : Primrec inIdx) :
    Primrec (fun x => spelledTable
      (slotTable (p x) (pitch x) (slot x) (tape x) (outIdx x) (inIdx x))) :=
  primrec_spelled_matrixTable (Primrec.succ.comp hp) (Primrec.list_length.comp hi)
    (primrec_gatherRows hp ho hi (Raw.primrec_read hc ((Primrec.list_getD []).comp ht hs)))

set_option maxHeartbeats 1200000 in
/-- The searched tape can be any computable family, including one found by a
terminating unbounded search. -/
theorem computable_spelled_slotTable {p pitch slot : X → ℕ} {tape : X → List (List ℕ)}
    {outIdx inIdx : X → List ℕ} (hp : Computable p) (hc : Computable pitch)
    (hs : Computable slot) (ht : Computable tape) (ho : Computable outIdx) (hi : Computable inIdx) :
    Computable (fun x => spelledTable
      (slotTable (p x) (pitch x) (slot x) (tape x) (outIdx x) (inIdx x))) := by
  let D := ℕ × ℕ × ℕ × List (List ℕ) × List ℕ × List ℕ
  have h : Primrec (fun v : D => spelledTable (slotTable v.1 v.2.1 v.2.2.1 v.2.2.2.1
      v.2.2.2.2.1 v.2.2.2.2.2)) :=
    primrec_spelled_slotTable Primrec.fst (Primrec.fst.comp .snd) (Primrec.fst.comp (Primrec.snd.comp .snd))
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp .snd)))
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp .snd))))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp .snd))))
  exact h.to_comp.comp (hp.pair (hc.pair (hs.pair (ht.pair (ho.pair hi)))))

theorem slotTable_correct {rows cols : ℕ} (p slot : ℕ) (tape : List (List ℕ))
    (input : Series (Fin cols)) (output : Series (Fin rows)) (x : Fin cols → ZMod (p+1)) :
    let t := slotTable p cols slot tape (output.tab Fin.val) (input.tab Fin.val)
    let M := Raw.interpret p rows cols (Raw.read cols (tape.getD slot []))
    let u := stripe input (fun j => numeral (x j).val)
    let v := stripe output (fun i => numeral (M.mulVec x i).val)
    RegisterLookup.read t u = v ∧ (u,v) ∈ t := by
  let M := Raw.interpret p rows cols (Raw.read cols (tape.getD slot []))
  have e : gatherRows p (output.tab Fin.val) (input.tab Fin.val) (Raw.read cols (tape.getD slot [])) =
      orderedCoefficients input output M := by
    simp only [gatherRows,Series.tab,List.map_map,orderedCoefficients,M,Raw.interpret,
      Function.comp_def,ZMod.val_natCast]
  simp only [slotTable,Series.card,e]
  exact ordered_correct input output M x

end InterchangeROMTable

end NearSquareRoot
end Computability
end OAI
