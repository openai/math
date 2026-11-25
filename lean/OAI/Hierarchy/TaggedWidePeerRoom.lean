import OAI.Hierarchy.TaggedWidePeerOrder

namespace OAI
/-! # Every true parallel row contributes once to a shared half-chord aperture -/
noncomputable section
namespace Hierarchy.ProtocolRAM.SiteControls
open LinearAlgebra.SpectralBooks ChordGraph
open WireTelescope NamedAperture Tagged PassiveWindow AdaptiveProbe
open scoped BigOperators Classical
variable {S N D cap : ℕ} (ends : Fin N→Chord S) (qty : Fin N→ℕ) (s : Fin S)
  (fits : ∀i,qty i≤cap) (slot : EndsAt ends qty s ↪ Fin D) {t : Widths S} (shape : installedWidths ends qty=t)

theorem seat_value (a : (EndsAt ends qty s)) : (carried ends qty s fits slot shape).owner (slot a)=some (byRow ends qty s a) ∧
    (carried ends qty s fits slot shape).width (slot a)=qty a.val.val.1 ∧ (carried ends qty s fits slot shape).base (slot a)=prefixAt ends qty a.val.val.1 := by
  cases shape
  refine ⟨?_,?_,?_⟩
  · change Function.extend slot (fun x => some (byRow ends qty s x)) (fun _ => none) (slot a)=_
    rw [slot.injective.extend_apply]
  · change Function.extend slot (fun x => qty x.val.val.1) (fun _ => 0) (slot a)=_
    rw [slot.injective.extend_apply]
  · change Function.extend slot (fun x => prefixAt ends qty x.val.val.1) (fun _ => 0) (slot a)=_
    rw [slot.injective.extend_apply]

theorem seat_vacant (q : Fin D) (vac : q∉Set.range slot) :
    (carried ends qty s fits slot shape).owner q=none ∧ (carried ends qty s fits slot shape).width q=0 ∧ (carried ends qty s fits slot shape).base q=0 := by
  cases shape
  refine ⟨?_,?_,?_⟩
  · change Function.extend slot (fun x => some (byRow ends qty s x)) (fun _ => none) q=none
    exact Function.extend_apply' _ _ _ vac
  · change Function.extend slot (fun x => qty x.val.val.1) (fun _ => 0) q=0
    exact Function.extend_apply' _ _ _ vac
  · change Function.extend slot (fun x => prefixAt ends qty x.val.val.1) (fun _ => 0) q=0
    exact Function.extend_apply' _ _ _ vac

theorem seat_owned (q : Fin D) : ((carried ends qty s fits slot shape).owner q).isSome=true ↔ 0<(carried ends qty s fits slot shape).width q := by
  by_cases used:q∈Set.range slot
  · obtain ⟨a,rfl⟩:=used
    obtain ⟨ha,hw,_⟩:=seat_value ends qty s fits slot shape a
    simp [ha,hw,a.property]
  · obtain ⟨ha,hw,_⟩:=seat_vacant ends qty s fits slot shape q used
    simp [ha,hw]

theorem size_sum (q : Fin D) :
    (∑i : Fin D,(ChordAperture.sizeAt (carried ends qty s fits slot shape) i q).val)=ChordAperture.room (carried ends qty s fits slot shape) q := by
  by_cases used:q∈Set.range slot
  · obtain ⟨a,rfl⟩:=used
    let emb:=cohort ends qty s slot a
    let cons := {i : Fin N // 0<qty i ∧ key ends i=key ends a.val.val.1}
    let sz:=fun i:Fin D=>(ChordAperture.sizeAt (carried ends qty s fits slot shape) i (slot a)).val
    have own:=(seat_value ends qty s fits slot shape a).1
    have hit (i : cons) : sz (emb i)=qty i.val := by
      have eq:ends i.val=ends a.val.val.1 := (Fintype.equivFin (Chord S)).injective i.property.2
      let z:(EndsAt ends qty s):=⟨⟨(i.val,a.val.val.2),by cases hb : a.val.val.2 <;> simpa only [hb,rowGraph,PortGraph.vertex,eq] using a.val.property⟩,i.property.1⟩
      obtain ⟨hz,quantity,_⟩:=seat_value ends qty s fits slot shape z
      have same : byRow ends qty s z=byRow ends qty s a := Subtype.ext (Prod.ext eq rfl)
      have code : ChordAperture.code (carried ends qty s fits slot shape) (slot z) (slot a) := ⟨_,hz.trans (congrArg some same),own⟩
      change (ChordAperture.sizeAt (carried ends qty s fits slot shape) (slot z) (slot a)).val=qty i.val
      simpa only [ChordAperture.sizeAt,ite_eq_left code] using quantity
    have blank (i : Fin D) (vac:i∉Set.range emb) : sz i=0 := by
      have no:¬ChordAperture.code (carried ends qty s fits slot shape) i (slot a) := by
        rintro ⟨p,iOwn,aOwn⟩
        by_cases used:i∈Set.range slot
        · obtain ⟨b,rfl⟩:=used
          have eq:=congrArg Subtype.val (Option.some.inj
            (((seat_value ends qty s fits slot shape b).1.symm.trans iOwn).trans (aOwn.symm.trans own)))
          have pair : ends b.val.val.1=ends a.val.val.1 := congrArg Prod.fst eq
          have side : b.val.val.2=a.val.val.2 := congrArg (fun p : Chord S × Bool=>p.2) eq
          let r:cons:=⟨b.val.val.1,b.property,congrArg (Fintype.equivFin _) pair⟩
          exact vac ⟨r,congrArg slot (Subtype.ext (Subtype.ext (Prod.ext rfl side.symm)))⟩
        · rw [(seat_vacant ends qty s fits slot shape i used).1] at iOwn
          contradiction
      simp [sz,ChordAperture.sizeAt,no]
    calc
      _ = ∑j∈Finset.univ.map emb,sz j := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro j _ nj
        exact blank j (by simpa only [Finset.mem_map,Finset.mem_univ,true_and,Set.mem_range] using nj)
      _ = ∑i : cons,qty i.val := by rw [Finset.sum_map];exact Finset.sum_congr rfl (fun i _=>hit i)
      _ = NativeSlot.mass (key ends) qty (key ends a.val.val.1) := by
        unfold NativeSlot.mass
        apply Finset.sum_bij_ne_zero (fun i _ _=>i.val)
        · simp
        · intro i _ _ j _ _ h;exact Subtype.ext h
        · intro j _ nz
          by_cases on:key ends j=key ends a.val.val.1
          · have pos:0<qty j:=by simpa [on,Nat.pos_iff_ne_zero] using nz
            exact ⟨⟨j,pos,on⟩,Finset.mem_univ _,Nat.ne_of_gt pos,rfl⟩
          · simp [on] at nz
        · intro i _ _;simp [i.property.2]
      _ = _ := by
        rw [ChordAperture.room,own,Option.elim_some,←shape]
        exact measured ends qty _
  · have no := (seat_vacant ends qty s fits slot shape q used).1
    simp [ChordAperture.sizeAt,ChordAperture.code,ChordAperture.room,no]

end Hierarchy.ProtocolRAM.SiteControls

end
end OAI
