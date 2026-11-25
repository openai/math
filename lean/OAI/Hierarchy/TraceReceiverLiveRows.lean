import OAI.Hierarchy.TraceReceiverGatherSafe

namespace OAI
/-! # From the issued S12 and map rows to a sequentially executable gather -/
noncomputable section
namespace Hierarchy.TraceFactorReceiver.Gather
open ThreeFlat RAM HistoryJoinScan HistoryCompiledRows Diagonal.HistoryContraction
open Computability.VPVNP.BurstRAM PrivateRAM BitNetwork.Ordered
open scoped Fin.CommRing BigOperators Classical

variable {F : Type*} {W n p : ℕ} {arity : Fin n→ℕ}
variable (nets : ∀ i,BitNetwork F (arity i)) (wires : ∀ i,Fin (arity i)→Fin p)
variable (tag : ((Fin 3→Bool)→F)→ℕ) (ctrl : Word W) (base commands : ℕ) (m : Memory W)
set_option quotPrecheck false
local notation "cells" => (fun i => (nets i).cells)
local notation "spans" => (List.ofFn (rootSpan base cells))
local notation "wire" => (fun i a => (BitSource.pin (wires i a) : BitSource 0 p))

/-- These are word equalities at the return from the three writer loops.
Their witnesses are the actual five-word task expansion and saved S14 map.
They refer only to the initial RAM of the gather. -/
structure IssuedRoot (i : Fin n) (head : Header ℕ) (mapping : ℕ→ℕ) : Prop where
  dest : head.dest=(rootSpan base cells i).dest
  cmd : fetch ((commands+7*i.val:ℕ):Word W) m=head.words
  sizes : head.oldPins=arity i ∧ head.newPins=p ∧
    head.offset=0+∑ j : Fin i.val,(nets (Fin.castLE i.isLt.le j)).internal
  target : ∀ j,mapping j.val=BitLayout.sourceAddress (resolve nets wire i (.pin j))
  sourceSpace : head.source+4*(nets i).cells≤2^W
  mapSpace : head.pins+head.oldPins≤2^W
  pinSpace : 2+head.oldPins<2^W
  wordSpace : ∀ row col,metadata tag (nets i) row col<2^W
  row : Records tag (nets i) head.source m
  pin : ∀ j,j<head.oldPins→m (head.pins+j)=(mapping j:Word W)
  commandQuiet : ∀ j : Fin 6,Untouched ctrl ((spans).take i.val)
    ((((commands+7*i.val:ℕ):Word W)+(j.val:Word W)).val)
  rowQuiet : ∀ (r : Fin (nets i).cells) (c : Fin 4),Untouched ctrl ((spans).take i.val)
    (head.source+(4*r.val+c.val))
  pinQuiet : ∀ j,j<head.oldPins→Untouched ctrl ((spans).take i.val) (head.pins+j)
  cmdAway : ∀ j : Fin 6,let x:=(((commands+7*i.val:ℕ):Word W)+Fin.ofNat _ j.val).val
    x<head.dest ∨ head.dest+4*(nets i).cells≤x
  sourceAway : head.source+4*(nets i).cells≤head.dest ∨ head.dest+4*(nets i).cells≤head.source
  mapAway : head.pins+head.oldPins≤head.dest ∨ head.dest+4*(nets i).cells≤head.pins

variable {nets wires tag ctrl base commands m}

theorem issued_read {i : Fin n} {head : Header ℕ} {mapping : ℕ→ℕ}
    (r : IssuedRoot nets wires tag ctrl base commands m i head mapping)
    (start : m ctrl.val=(commands:Word W))
    (off : ∀ a∈spans,ctrl.val<a.dest ∨ a.stop≤ctrl.val) :
    RootReads nets wire tag ctrl (finish ctrl ((spans).take i.val) m) i head mapping := by
  have len : ((spans).take i.val).length=i.val:=by simp []
  apply root_at_prefix nets wire tag ctrl _ m head mapping i ((commands+7*i.val:ℕ):Word W)
  · rw [start,len,Nat.cast_add]
  · intro s hs
    exact off s (List.mem_of_mem_take hs)
  · exact r.cmd
  · exact r.sizes
  · exact r.target
  · exact r.sourceSpace
  · exact r.mapSpace
  · exact r.pinSpace
  · exact r.wordSpace
  · exact r.row
  · exact r.pin
  · exact r.commandQuiet
  · exact r.rowQuiet
  · exact r.pinQuiet

theorem issued_locations (start : m ctrl.val=(commands:Word W))
    (above : ctrl.val<base ∨ base+4*(∑ i,cells i)≤ctrl.val)
    (off : ∀ (s : Span),s∈spans→ctrl.val< s.dest ∨ s.stop≤ctrl.val)
    (data : ∀ i : Fin n,∃ head mapping,IssuedRoot nets wires tag ctrl base commands m i head mapping) :
    Locations nets wire tag ctrl m base spans := by
  apply canonical_locations nets wire tag ctrl base m above
  intro i
  obtain ⟨h,f,r⟩:=data i
  exact ⟨h,f,r.dest,issued_read r start off⟩

theorem issued_safe (start : m ctrl.val=(commands:Word W))
    (off : ∀ (s : Span),s∈spans→ctrl.val< s.dest ∨ s.stop≤ctrl.val)
    (data : ∀ i : Fin n,∃ head mapping,IssuedRoot nets wires tag ctrl base commands m i head mapping) :
    safe ctrl spans m := by
  apply safe_of_rows
  intro i
  let j : Fin n:=⟨i.val,by simpa using i.isLt⟩
  obtain ⟨h,f,r⟩:=data j
  have found : (spans).get i=rootSpan base cells j:=by simp [j,List.get_eq_getElem]
  let prev:=finish ctrl ((spans).take i.val) m
  have selected : RootReads nets wire tag ctrl prev j h f := issued_read r start off
  have cursor : prev ctrl.val=((commands+7*i.val:ℕ):Word W):=by
    rw [show prev ctrl.val=m ctrl.val+((7*((spans).take i.val).length:ℕ):Word W) from
      cursor_after ctrl _ m (fun s hs=>off s (List.mem_of_mem_take hs)),start,
      show ((spans).take i.val).length=i.val from by rw [List.length_take,Nat.min_eq_left i.isLt.le],Nat.cast_add]
  have sep : Separate (prev ctrl.val) h.dest (h.dest+4*(nets j).cells) prev:=by
    apply separate_ranges h (prev ctrl.val) prev (nets j).cells selected.header
    · rw [cursor]
      exact r.cmdAway
    · exact r.sourceAway
    · exact r.mapAway
    · exact r.sourceSpace
    · exact r.mapSpace
    · exact r.pinSpace
  refine ⟨off _ (List.get_mem ..),?_⟩
  rw [found]
  change Separate (prev ctrl.val) (base+4*Tree.before cells j)
    (base+4*Tree.before cells j+4*(nets j).cells) prev
  have dst : h.dest=base+4*Tree.before cells j:=r.dest
  rw [←dst]
  exact sep

end Hierarchy.TraceFactorReceiver.Gather
end

end OAI
