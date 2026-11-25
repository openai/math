import OAI.Hierarchy.DescentDonorChipLookup
import OAI.Hierarchy.DescentSignedCableCodec
import OAI.Hierarchy.DescentRawCableRoster

namespace OAI
/-! # Reconstruct each old wire width from its true local signed source records -/
namespace Hierarchy.DescentSharedCableNames.Stage
open DescentSIMDLookup DescentSixParty DescentSignedCableCodec
open scoped Classical BigOperators
noncomputable section

variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
    (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (names : Host J V k↪ℕ)

theorem outgoing_identify_home {e f : Positive A} (same : home A (W.graph.src e.val)=home A (W.graph.src f.val))
    (ticket : outgoing A native S ready e=outgoing A native S ready f) : e=f := by
  let h:=home A (W.graph.src f.val)
  have move {x : Host J V k} (p : Positive A) (here : home A (W.graph.src p.val)=x) :
      outgoing A native S ready p=outgoingAt A native S ready x p here := by cases here;rfl
  rw [move e same,move f (rfl : home A (W.graph.src f.val)=h)] at ticket
  rcases lt_trichotomy (native e.val) (native f.val) with l|z|r
  · have lt_:=positive_before A native S ready h e f same rfl l
    exact (lt_.ne ticket).elim
  · exact Subtype.ext (native.injective z)
  · have lt_:=positive_before A native S ready h f e rfl same r
    exact (lt_.ne ticket.symm).elim

def grainPort (e : Positive A) (j : Fin (A.grainCount e.val)) :
    let h:=home A (W.graph.src e.val)
    A.CellPorts h.1.1 h.1.2 h.2 := .inl ⟨⟨e.val,rfl,rfl⟩,j⟩

def grainSlot (e : Positive A) : Fin (A.grainCount e.val) ↪ Fin (2*A.cap) :=
  let h:=home A (W.graph.src e.val)
  {toFun:=fun j=>signed A native S ready h.1 h.2 (grainPort A e j)
   inj':=by
    intro l r eqn
    have pr:=(signed A native S ready h.1 h.2).injective eqn
    exact Fin.ext (congrArg (fun q=>(recover A h q).2.val) pr)}

theorem source_grains (e : Positive A) :
    let h:=home A (W.graph.src e.val)
    sourceGrains (fun j=>DescentSignedCableCodec.encode (signedPanel A native S ready names h j)) (outgoing A native S ready e)=A.grainCount e.val := by
  classical
  intro h
  let addr:=signed A native S ready h.1 h.2
  let number:=outgoing A native S ready e
  let inputs:=signedPanel A native S ready names h
  have select : Finset.univ.filter (fun j=>atSource number (inputs j)=true)=Finset.univ.map (grainSlot A native S ready e) := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_map,Finset.mem_univ,true_and]
    constructor
    · intro found
      by_cases hit:∃q,addr q=j
      · obtain ⟨q,rfl⟩:=hit
        rw [show inputs (addr q)=some (live A native S ready names h q) from signed_read A native S ready names h q] at found
        cases q with
        | inr p=> simp [atSource,live,signedBit] at found
        | inl p=>
          obtain ⟨⟨f,near⟩,bit⟩:=p
          let old : Positive A:=⟨f,Nat.zero_lt_of_lt bit.isLt⟩
          have isOld : outgoing A native S ready old=number := by simpa [atSource,live,signedBit,recover,old] using found
          have same : home A (W.graph.src f)=h := Prod.ext near.1 near.2
          have eqn:=congrArg Subtype.val (outgoing_identify_home A native S ready (e:=old) (f:=e) same isOld)
          change f=e.val at eqn
          subst f
          exact ⟨bit,rfl⟩
      · have empty:=signed_empty A native S ready names h j (not_exists.mp hit)
        simp [inputs,empty,atSource] at found
    · rintro ⟨t,rfl⟩
      have given:=signed_read A native S ready names h (grainPort A e t)
      change atSource number (signedPanel A native S ready names h (addr (grainPort A e t)))=true
      rw [given]
      simp [atSource,live,signedBit,grainPort,recover,number]
  simp only [sourceGrains,DescentSignedCableCodec.decode_encode]
  change (Finset.univ.filter (fun j=>atSource number (inputs j)=true)).card=A.grainCount e.val
  rw [select]
  simp

/-- Test presence on every source slot, including unsampled and ghost slots.
The first grain determines the source ticket even on an unmarked tether. -/
theorem source_live (h : Host J V k) (t : Fin A.cap) :
    0<sourceGrains (fun j=>DescentSignedCableCodec.encode (signedPanel A native S ready names h j)) t ↔
      ∃e : Positive A,home A (W.graph.src e.val)=h ∧ outgoing A native S ready e=t := by
  classical
  let addr:=signed A native S ready h.1 h.2
  constructor
  · intro pos
    change 0<(Finset.univ.filter _).card at pos
    obtain ⟨j,hj⟩:=Finset.card_pos.mp pos
    have f:= (Finset.mem_filter.mp hj).2
    rw [DescentSignedCableCodec.decode_encode] at f
    by_cases hit:∃q,addr q=j
    · obtain ⟨q,rfl⟩:=hit
      rw [signed_read] at f
      cases q with
      | inr q=>simp [atSource,live,signedBit] at f
      | inl q=>
        obtain ⟨⟨e,at_⟩,bit⟩:=q
        refine ⟨⟨e,Nat.zero_lt_of_lt bit.isLt⟩,Prod.ext at_.1 at_.2,?_⟩
        simpa [atSource,live,recover,signedBit] using f
    · rw [signed_empty A native S ready names h j (not_exists.mp hit)] at f
      contradiction
  · rintro ⟨e,rfl,rfl⟩
    rw [source_grains]
    exact e.property

end
end Hierarchy.DescentSharedCableNames.Stage

end OAI
