import OAI.Computability.VPVNP.LiveHeaderBits
import OAI.ThreeFlat.Diagonal.TraceInputSlots
import OAI.ThreeFlat.Diagonal.TraceSlotOrder
import OAI.ThreeFlat.Diagonal.TraceWordTests
import OAI.ThreeFlat.Routing.TypedWiring
import OAI.ThreeFlat.Diagonal.TraceCpuBits

namespace OAI
/-! # Bounded-fan-in serialization of one native probe record -/

noncomputable section
namespace Hierarchy.TaggedShorterChronoRow
open ThreeFlat Routing Diagonal TraceRows TraceBanks TraceWords TraceSlots
open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMSerialization
open scoped Classical BigOperators
variable {F : Type*} {w p r : ℕ}

abbrev In (w r : ℕ) := Fin ((5+r)*(w+1))
abbrev Out (w : ℕ) := Fin 7 × Fin (w+1)

def low (hw : 3≤w+1) (i : Fin 3) : Fin (w+1) := i.castLE hw

def wires (hw : 3≤w+1) (f : Fin 7) (j : Fin (w+1)) : Fin 6 → In w r ⊕ Out w :=
  ![.inl (finProdFinEquiv ((0 : Fin 5).castAdd r, low hw 0)),
    .inl (finProdFinEquiv ((0 : Fin 5).castAdd r, low hw 1)),
    .inl (finProdFinEquiv ((0 : Fin 5).castAdd r, low hw 2)),
    .inl (finProdFinEquiv ((3 : Fin 5).castAdd r,j)),.inl (finProdFinEquiv ((4 : Fin 5).castAdd r,j)),
    .inr (f,j)]

/-- The high tag bits are zero on canonical CPU rows. The low three
bits distinguish the two RAM operations from every other instruction. -/
def dataBit (hw : 3≤w+1) (time : Word (w+1)) (f : Fin 7) (j : Fin (w+1))
    (z : Fin 6 → Bool) : Bool :=
  if z 2 && !z 1 then
    ![false,z 3,bits (small (by omega : 2≤w+1) 1) j,bits time j,false,
      bits (small (by omega : 2≤w+1) (if z 0 then 2 else 1)) j,z 4] f
  else bits (fields (by omega) (none : Option (WordRecord (w+1))) f) j

def output (hw : 3≤w+1) (s : Option (WordRecord (w+1))) : Out w → Bool :=
  fun fj => bits (fields (by omega) s fj.1) fj.2

theorem data_at (hw : 3≤w+1) (hp : p≤2^(w+1)) (t : Word (w+1))
    (x : Row (w+1) (Snapshot w p r)) (y : Out w → Bool) (f : Fin 7) (j : Fin (w+1)) :
    dataBit hw t f j (Sum.elim ((rowFormat hw hp).encode x) y ∘ wires hw f j) =
      output hw (rowWordSlot t x) (f,j) := by
  have atPin (a : Fin 5) (b : Fin (w+1)) :
      (rowFormat hw hp).encode x (finProdFinEquiv (a.castAdd r,b))=bits (header hw hp x a) b := by
    rw [Format.encode,arrayBits_at,←Computability.VPVNP.LiveHeader.testBit_wordBits,rowFormat_header]; rfl
  have wireValues :
      Sum.elim ((rowFormat hw hp).encode x) y ∘ wires hw f j =
        ![bits (header hw hp x 0) (low hw 0),bits (header hw hp x 0) (low hw 1),
          bits (header hw hp x 0) (low hw 2),bits (header hw hp x 3) j,
          bits (header hw hp x 4) j,y (f,j)] := by
    funext k
    fin_cases k <;> first | exact atPin _ _ | rfl
  rw [wireValues]
  cases x with
  | pad => simp [dataBit,output,header,low,bits,rowWordSlot]
  | halt s out =>
    cases out <;> simp [dataBit,output,header,low,tagWord,bits,rowWordSlot,Nat.testBit_eq_decide_div_mod_eq]
  | move s e =>
    cases e with
    | choice b =>
      cases b <;> simp [dataBit,output,header,low,tagWord,bits,rowWordSlot,Nat.testBit_eq_decide_div_mod_eq]
    | tick => simp [dataBit,output,header,low,tagWord,bits,rowWordSlot,Nat.testBit_eq_decide_div_mod_eq]
    | read a v | write a v =>
      fin_cases f <;> simp [dataBit,output,header,low,tagWord,bits,rowWordSlot,fields,Nat.testBit_eq_decide_div_mod_eq]

def network [Zero F] [One F] (hw : 3≤w+1) (t : Word (w+1)) :
    BitNetwork F (Fintype.card (In w r ⊕ Out w)) :=
  TypedWiring.glue (fun fj : Out w => TypedWiring.localTable (P:=Fin 6)
    (fun z => if z 5=dataBit hw t fj.1 fj.2 z then (1:F) else 0))
    (fun fj k => (Sum.inl (wires hw fj.1 fj.2 k) : (In w r ⊕ Out w) ⊕ Empty))

theorem eval [CommSemiring F] (hw : 3≤w+1) (hp : p≤2^(w+1)) (t : Word (w+1))
    (x : Row (w+1) (Snapshot w p r)) (y : Out w → Bool) :
    TypedWiring.value (network (F:=F) hw t) (Sum.elim ((rowFormat hw hp).encode x) y) =
      if y=output hw (rowWordSlot t x) then 1 else 0 := by
  rw [network,TypedWiring.glue_value]
  simp only [Fintype.sum_unique,Sum.elim_inl,TypedWiring.localTable_value,Fintype.prod_boole]
  congr 1
  apply propext
  rw [funext_iff]
  apply forall_congr'
  intro ⟨f,j⟩
  rw [show (fun k => Sum.elim ((rowFormat hw hp).encode x) y (wires hw f j k)) =
    Sum.elim ((rowFormat hw hp).encode x) y ∘ wires hw f j from rfl,data_at]
  rfl

theorem size [Zero F] [One F] (hw : 3≤w+1) (t : Word (w+1)) :
    (network (F:=F) (r:=r) hw t).cells+(network (F:=F) (r:=r) hw t).internal ≤ 20000*(w+1) := by
  simp only [network,TypedWiring.glue_cells,TypedWiring.glue_internal,TypedWiring.localTable,
    TableCompiler.localTableNetwork_cells,TableCompiler.localTableNetwork_internal,
    Fintype.card_fin,Fintype.card_empty,zero_add,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,Out,Fintype.card_prod]
  change (7*(w+1))*512+(7*(w+1))*448 ≤ 20000*(w+1)
  omega

end Hierarchy.TaggedShorterChronoRow

end
end OAI
