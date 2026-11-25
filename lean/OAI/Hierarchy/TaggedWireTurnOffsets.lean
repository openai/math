import OAI.Hierarchy.TaggedWireWordTurns
import OAI.Hierarchy.TaggedWireNativeSlot
import OAI.Hierarchy.TaggedWireChordRouter
import OAI.Computability.VPVNP.LiveHeaderBits

namespace OAI
/-! # Literal original occurrence offsets of every bit on a routed word -/

noncomputable section
namespace Hierarchy.WireTelescope.NativeSlot
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph AdaptiveProbe
open TaggedShorterCommonScan
open scoped Classical

variable {I : Type} [Fintype I] {d n : ℕ} (route : I→List (Fin d)) (bits : I→ℕ)
    (ord : Fin n≃Σi,Fin (route i).length)

def start (i : I) (j : Fin (route i).length) : ℕ :=
  let row:=ord.symm ⟨i,j⟩
  earlier (edge route ord) (amount (route:=route) (bits:=bits) (rows:=ord)) row.val (edge route ord row)

theorem allocation_value (i : I) (j : Fin (route i).length) (k : Fin (bits i)) :
    (allocation route bits ord ⟨⟨i,k⟩,j⟩).2.val=start route bits ord i j+k.val := by
  let q := positions route bits ord ⟨⟨i,k⟩,j⟩
  let e := Equiv.sigmaCongrLeft (β:=fun t : (Σi,Fin (route i).length)=>Fin (bits t.1)) ord
  have same := congrArg (fun z : (Σ t : (Σi,Fin (route i).length),Fin (bits t.1))=>z.2.val)
    (e.apply_symm_apply ⟨⟨i,j⟩,k⟩)
  have value : q.2.val=k.val := same
  change earlier (edge route ord) (amount (route:=route) (bits:=bits) (rows:=ord)) q.1.val
    (edge route ord q.1)+q.2.val=_
  rw [value]
  rfl

theorem start_room (i : I) (j : Fin (route i).length) (positive : 0<bits i) :
    start route bits ord i j+bits i≤routeLoad route bits ((route i).get j) := by
  let k : Fin (bits i):=⟨bits i-1,by omega⟩
  let chosen := allocation route bits ord ⟨⟨i,k⟩,j⟩
  have loc : chosen.1=(route i).get j:=allocation_edge route bits ord _
  have val : chosen.2.val=start route bits ord i j+k.val:=allocation_value route bits ord i j k
  have room : start route bits ord i j+(bits i-1) < routeLoad route bits ((route i).get j) := calc
    _ = chosen.2.val := val.symm
    _ < routeLoad route bits chosen.1 := chosen.2.isLt
    _ = _ := congrArg (routeLoad route bits) loc
  omega
end Hierarchy.WireTelescope.NativeSlot

namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph AdaptiveProbe
open scoped Classical

variable {S n m h : ℕ} (old : Fin n→Chord S) (edge : Fin m→Chord S)
  (route : Fin n→List (Fin m)) (bits : Fin n→ℕ) (ord : Fin h≃Σi,Fin (route i).length)
local notation "idx" => NativeSlot.allocation route bits ord
local notation "mass" => routeLoad route bits

theorem turn_start_bit (i : Fin n) (k : Fin (bits i)) (side : Bool) (s : Fin S)
    (atSite : (rowGraph old).vertex i side=s) (x : BitState (bitGraph (rowGraph old) bits) s)
    (y : BitState (bitGraph (rowGraph edge) mass) s) :
    readTurn (rowGraph edge) (rowGraph old) route bits idx ⟨i,k⟩ s (x,y) (.inl side)=
      x ⟨(⟨i,k⟩,side),by cases side <;>exact atSite⟩ := by
  simp only [readTurn,dite_eq_left (show (bitGraph (rowGraph old) bits).vertex ⟨i,k⟩ side=s by
    cases side <;>exact atSite)]

theorem turn_paid_bit (i : Fin n) (j : Fin (route i).length) (k : Fin (bits i)) (side : Bool) (s : Fin S)
    (atSite : (rowGraph edge).vertex ((route i).get j) side=s)
    (x : BitState (bitGraph (rowGraph old) bits) s) (word : ∀t,Fin (2^mass t)) :
    readTurn (rowGraph edge) (rowGraph old) route bits idx ⟨i,k⟩ s
      (x,(bitGraph (rowGraph edge) mass).atVertex (wordBitsEquiv mass word) s) (.inr (j.val,side)) =
      (word ((route i).get j)).val.testBit (NativeSlot.start route bits ord i j+k.val) := by
  let key := idx ⟨⟨i,k⟩,j⟩
  have atKey : key.1=(route i).get j:=NativeSlot.allocation_edge route bits ord _
  have number : key.2.val=NativeSlot.start route bits ord i j+k.val:=NativeSlot.allocation_value route bits ord i j k
  have within : j.val<(placedRoute route bits idx ⟨i,k⟩).length := by simp [placedRoute]
  have get : (placedRoute route bits idx ⟨i,k⟩).get ⟨j.val,within⟩=key := by simp [placedRoute,key]
  have site : (bitGraph (rowGraph edge) mass).vertex key side=s := by cases side <;> simpa [bitGraph,PortGraph.vertex,atKey] using atSite
  simp only [readTurn,dite_eq_left within,get,dite_eq_left site]
  change Computability.VPVNP.RAMSerialization.wordBits (mass key.1) (word key.1) key.2=_
  rw [←Computability.VPVNP.LiveHeader.testBit_wordBits,number,atKey]

end Hierarchy.WireTelescope

end
end OAI
