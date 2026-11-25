import OAI.Hierarchy.DescentTerminalLeafDigits
import OAI.Hierarchy.DescentTerminalShelfControl
import OAI.ThreeFlat.Routing.CallBatches

namespace OAI
/-! # One lookup and one update for a whole short lane of local header fields -/
namespace Hierarchy.DescentTerminalPackedLeaves
open DescentTerminalLeafDigits DescentTerminalPrintedFields DescentTerminalRowBooks
open DescentTerminalChronologicalBooks Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.Routing
open scoped Classical BigOperators
noncomputable section
variable {q t V H N A w pool b lanes : ℕ}
local notation "C" => Control q t H N A w V
local notation "Events" => tokenCount q t V H N A w
local notation "dict" => dictionary (q:=q) (t:=t) (V:=V) (H:=H) (N:=N) (A:=A) (w:=w)
abbrev Active (c : C) := {j : Coord V H N A // (digit (emit c) j).val≠0}
def numbered (c : C) : Active c ≃ Fin (Fintype.card (Active c)) :=
  ordinal ((Function.Embedding.subtype _).trans ((fieldsOrder V H N A).toEmbedding.trans Fin.valEmbedding))
def cluster (c : C) := List.ofFn (fun i : Fin (Fintype.card (Active c))=>
  let z:=(numbered c).symm i
  (eventOrder (token (emit c) z.val z.property)).succ)
def list (z : Option C) := (z.map cluster).getD []
def count (z : Option C) (s : ℕ) := poolBatchCount (list z).length s

def piece (room : Events+1 ≤ 2^b) (z : Option C) (i : ℕ) : Fin lanes→Fin (2^b) :=
  fun j=>((((list z)[i*lanes+j.val]?).getD 0).castLE room)

def serialize (z : Fin lanes→Fin (2^b)) : Fin (2^(b*lanes)) := (finFunctionFinEquiv z).cast (pow_mul ..).symm
def unpack (a : Fin (2^(b*lanes))) : Fin lanes→Fin (2^b) := finFunctionFinEquiv.symm (a.cast (pow_mul ..))
theorem unpack_serial (z : Fin lanes→Fin (2^b)) : unpack (serialize z)=z := by simp [unpack,serialize]

def table (b lanes q t V H N A w : ℕ) := List.ofFn (fun k : Fin (2^(b*lanes))=>
  ∑j : Fin lanes,((dictionary (q:=q) (t:=t) (V:=V) (H:=H) (N:=N) (A:=A) (w:=w))[(unpack k j).val]?).getD 0)
private theorem key_room (j : Fin (Events+1)) : j.val<(dict).length := by
  simpa only [dictionary,List.length_ofFn] using j.isLt

def amount (z : Option C) (i : ℕ) (lanes : ℕ) := ∑j : Fin lanes,let key:=((list z)[i*lanes+j.val]?).getD 0
  dict[key.val]'(key_room key)

theorem read (room : Events+1 ≤ 2^b) (c : Option C) (k : ℕ) :
    (table b lanes q t V H N A w)[(serialize (piece (lanes:=lanes) room c k)).val]'
      (by simpa only [table,List.length_ofFn] using (serialize (piece (lanes:=lanes) room c k)).isLt)=amount c k lanes := by
  simp only [table,List.getElem_ofFn,Fin.eta,unpack_serial,amount,piece,Fin.val_castLE]
  apply Finset.sum_congr rfl
  intro j _
  simp [List.getElem?_eq_getElem (key_room (((list c)[k*lanes+j.val]?).getD 0))]

theorem list_total (c : Option C) :
    (∑j : Fin (list c).length,dict[((list c).get j).val]'(key_room ((list c).get j)))=DescentTerminalLeafFold.code c := by
  cases c with
  | none=>simp [list,DescentTerminalLeafFold.code]
  | some c=>
    let getWeight (key : Fin (Events+1)) := dict[key.val]'(key_room key)
    let data := list (some c)
    change (∑ j : Fin data.length,getWeight (data.get j))=_
    rw [←List.sum_ofFn,List.ofFn_comp' data.get getWeight,List.ofFn_get]
    simp only [data,list,Option.map_some,Option.getD_some,cluster,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
    rw [DescentTerminalLeafFold.code,Option.map_some,Option.getD_some,sparse_digits,←(numbered c).symm.sum_comp]
    apply Finset.sum_congr rfl
    intro i _
    exact dictionary_token _

theorem block_sum (lp : 0<lanes) (c : Option C) : (∑i : Fin (count c lanes),amount c i.val lanes)=DescentTerminalLeafFold.code c := by
  let data:=list c
  let weight (j : ℕ) := (dict[(((list c)[j]?).getD 0).val]?).getD 0
  have room : data.length ≤ count c lanes*lanes := by
    simpa only [data,count,Nat.mul_comm lanes] using
      CallPool.count_le_batches_mul (list c).length lanes lp
  have small (j : Fin data.length) : weight j.val=dict[(data.get j).val]'(key_room (data.get j)) := by
    have index : (list c)[j.val]?=some (data.get j) :=
      List.getElem?_eq_getElem j.isLt
    unfold weight
    rw [index]
    exact congrArg (fun x : Option ℕ=>x.getD 0) (List.getElem?_eq_getElem (key_room (data.get j)))
  have none (j : ℕ) (off : data.length ≤ j) : weight j=0 := by
    simp [weight,show (list c)[j]?=none by exact List.getElem?_eq_none off,dictionary]
  have capacity : (∑k : Fin (count c lanes*lanes),weight k.val)=∑k : Fin data.length,weight k.val := by
    simp_rw [Fin.sum_univ_eq_sum_range]
    symm
    exact Finset.sum_subset (Finset.range_mono room) fun j _ h=>none j (by simpa using h)
  calc
    _ = ∑i : Fin (count c lanes),∑j : Fin lanes,weight (finProdFinEquiv (i,j)).val := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      have addr : (finProdFinEquiv (i,j)).val=i.val*lanes+j.val:=by change j.val+lanes*i.val=_;ring
      simp [weight,addr,List.getElem?_eq_getElem (key_room (((list c)[i.val*lanes+j.val]?).getD 0))]
    _ = ∑k : Fin (count c lanes*lanes),weight k.val :=
      (Fintype.sum_prod_type (fun a : Fin (count c lanes)×Fin lanes=>weight (finProdFinEquiv a).val)).symm.trans
        (finProdFinEquiv.sum_comp (fun k=>weight k.val))
    _ = _ :=capacity.trans ((Finset.sum_congr rfl fun k _=>small k).trans (list_total c))

theorem clock_price (profile : Fin pool→Option C) (lp : 0<lanes) {h bitsPer : ℕ} (paid : h ≤ bitsPer*lanes) :
    (∑i,count (profile i) lanes)*h ≤ bitsPer*(∑i,(list (profile i)).length)+pool*h := by
  have localBound (z : Option C) : count z lanes*h ≤ bitsPer*(list z).length+h := by
    by_cases empty:count z lanes=0
    · simp [empty]
    · let full:=count z lanes-1
      have length : full*lanes ≤ (list z).length := by
        have cover : count z lanes*lanes ≤ (list z).length+lanes-1 :=
          Nat.div_mul_le_self _ _
        have eq : count z lanes=full+1 := by dsimp [full];omega
        rw [eq,Nat.add_mul,Nat.one_mul] at cover
        omega
      have first:=Nat.mul_le_mul_left full paid
      have last:=Nat.mul_le_mul_left bitsPer length
      have eq : count z lanes=full+1:=by dsimp [full];omega
      rw [eq,Nat.add_mul,Nat.one_mul]
      calc
        _ ≤ full*(bitsPer*lanes)+h:=Nat.add_le_add_right first h
        _ = bitsPer*(full*lanes)+h:=by ring
        _ ≤ _:=Nat.add_le_add_right last h
  calc
    _ = ∑i : Fin pool,count (profile i) lanes*h := Finset.sum_mul ..
    _ ≤ ∑i : Fin pool,(bitsPer*(list (profile i)).length+h) := Finset.sum_le_sum fun i _=>localBound _
    _ = _ := by simp [Finset.sum_add_distrib,Finset.mul_sum]

end
end Hierarchy.DescentTerminalPackedLeaves

end OAI
