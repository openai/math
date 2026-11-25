import OAI.ThreeFlat.RAM.HistoryPartyGather
import OAI.ThreeFlat.Diagonal.HistogramPartyPointers
import OAI.ThreeFlat.RAM.ContractionMemory

namespace OAI
/-! # Addresses obtained from the selected per-bit gather tables -/

namespace ThreeFlat.RAM.HistoryPartyGather

open Diagonal LinearAlgebra.SpectralBooks Computability.VPVNP.MotifSelector Diagonal.MotifOuterTerms Diagonal.MotifBinaryPacking Diagonal.HistogramTileNetwork
open BitLayout
open scoped BigOperators Classical

noncomputable section

variable {J E S H : Type*} [Fintype J] [Nonempty J] [Fintype E] [Fintype S]
  [Fintype H] [DecidableEq H] [Nonempty H] {k e n d r h p : ℕ}

variable (D : PortGraph J E) (G : Supply J S) (j : J) (base w : E → ℕ)
  (B : Header (D.Port j) H (fun a => base a.1.1) k n)
  (portsAt : Fin e ≃ (ports G).Port j) (sw : H → S → ℕ) (v : Histogram H r)
  (old : (a : D.Port j) → Fin (w a.1.1) → BitSource h p)
  (fresh : (a : (ports G).Port j) → Fin (histWidth sw v a.1.1+r*k) → BitSource h p)

/-- These tables are ephemeral. Only sites selected for this tick allocate the
lists containing a separate physical address for every input or output bit. -/
structure Image (T : Layout) (mem : ℕ → ℕ) : Prop where
  copies : T.copies=r
  selectorBits : T.selectorBits=k
  ports : T.ports=e
  headerBits : T.headerBits=B.arity
  tileBits : T.tileBits=d
  anchor : T.anchor=(portsAt.symm (anchorPort G j)).val
  outputWidth (u : Fin e) : mem (T.supplyRows+2*u.val+1)=histWidth sw v (portsAt u).1.1
  outputBit (u : Fin e) (b : Fin (histWidth sw v (portsAt u).1.1+r*k)) :
    mem (mem (T.supplyRows+2*u.val)+b.val)=sourceAddress (fresh (portsAt u) b)
  inputWidth (u : Fin n) : mem (T.demandRows+3*u.val+1)=w (B.ports u).1.1
  tileWidth (u : Fin n) : mem (T.demandRows+3*u.val+2)=base (B.ports u).1.1
  inputBase (u : Fin n) : mem (T.demandRows+3*u.val)≠0
  inputBit (u : Fin n) (b : Fin (w (B.ports u).1.1)) :
    mem (mem (T.demandRows+3*u.val)+b.val)=sourceAddress (old (B.ports u) b)
  demandPort (u : Fin n) (b : Fin (base (B.ports u).1.1)) :
    mem (T.headerTable+2*(finSigmaFinEquiv (n:=fun u : Fin n=>base (B.ports u).1.1) ⟨u,b⟩).val)=u.val
  demandDigit (u : Fin n) (b : Fin (base (B.ports u).1.1)) :
    mem (T.headerTable+2*(finSigmaFinEquiv (n:=fun u : Fin n=>base (B.ports u).1.1) ⟨u,b⟩).val+1)=b.val

private theorem digits {a b : ℕ} (i : Fin a) (j : Fin b) :
    (finProdFinEquiv (i,j)).val/b=i.val ∧ (finProdFinEquiv (i,j)).val%b=j.val := by
  have hb := Nat.zero_lt_of_lt j.isLt
  change (j.val+b*i.val)/b=i.val ∧ (j.val+b*i.val)%b=j.val
  simp [Nat.add_mul_div_left _ _ hb,Nat.div_eq_of_lt j.isLt,Nat.mod_eq_of_lt j.isLt]

omit [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [DecidableEq H] [Nonempty H] in
theorem gather_eq {T : Layout} {mem : ℕ → ℕ}
    (I : Image (d:=d) D G j base w B portsAt sw v old fresh T mem)
    (x : Fin (r*(e*k)+(r*B.arity+e*(r*d)))) :
    gather T mem x.val = sourceAddress (partyPointer D G j base w B portsAt sw v old fresh x) := by
  let sel := r*(e*k)
  refine Fin.addCases (fun z => ?_) (fun rest => ?_) x
  · obtain ⟨⟨i,q⟩,rfl⟩ := finProdFinEquiv.surjective z
    obtain ⟨⟨u,b⟩,rfl⟩ := finProdFinEquiv.surjective q
    let v₀ := finProdFinEquiv (u,b)
    let zz := finProdFinEquiv (i,v₀)
    have hu := digits u b
    have hi : zz.val/(e*k) = i.val := (digits i v₀).1
    have offset : zz.val/k%e=u.val ∧ zz.val%k=b.val := by
      have hp := Nat.zero_lt_of_lt b.isLt
      have he := Nat.zero_lt_of_lt u.isLt
      have repr : zz.val=b.val+k*(u.val+e*i.val) := by dsimp [zz,v₀,finProdFinEquiv]; ring
      rw [repr]
      simp [Nat.add_mul_div_left _ _ hp,Nat.div_eq_of_lt b.isLt,Nat.mod_eq_of_lt b.isLt,Nat.mod_eq_of_lt u.isLt]
    rw [partyPointer_select]
    change gather T mem zz.val = _
    simp only [gather,I.copies,I.selectorBits,I.ports,ite_eq_left zz.isLt,offset.1,offset.2,hi,
      Nat.add_zero,I.outputWidth]
    exact I.outputBit u ⟨_,by have bd := Nat.mul_le_mul_left k i.isLt; rw [Nat.mul_succ] at bd; have br := b.isLt; rw [Nat.mul_comm r k]; omega⟩
  · refine Fin.addCases (fun z => ?_) (fun z => ?_) rest
    · obtain ⟨⟨i,q⟩,rfl⟩ := finProdFinEquiv.surjective z
      have mid (q : Fin B.arity) : gather T mem (sel+(finProdFinEquiv (i,q)).val) =
          if q.val<k then
            mem (mem (T.supplyRows+2*T.anchor)+(mem (T.supplyRows+2*T.anchor+1)+(k*i.val+q.val)))
          else let index := T.headerTable+2*(q.val-k)
               let row := T.demandRows+3*mem index
               let bit := mem (row+2)*i.val+mem (index+1)
               if mem row=0 then 0 else if bit < mem (row+1) then mem (mem row+bit) else 0 := by
        have h := digits i q
        simp only [gather,I.copies,I.ports,I.selectorBits,I.headerBits,sel,Nat.not_lt_of_ge
          (Nat.le_add_right _ _),ite_false,Nat.add_sub_cancel_left,(finProdFinEquiv (i,q)).isLt,
          ite_true,h.1,h.2,Nat.add_zero]
      refine Fin.addCases (fun b => ?_) (fun bit => ?_) q
      · refine Eq.trans ?_ (congrArg sourceAddress
          (partyPointer_head D G j base w B portsAt sw v old fresh (d:=d) i b)).symm
        change gather T mem (sel+(finProdFinEquiv (i,b.castAdd _)).val) = _
        refine (mid (b.castAdd (∑ u, base (B.ports u).1.1))).trans ?_
        simp only [Fin.val_castAdd,b.isLt,ite_true,I.anchor,I.outputWidth]
        have lookup (u : Fin e) (a : (ports G).Port j) (same : portsAt u = a)
            (f : Fin (histWidth sw v a.1.1+r*k)) :
            mem (mem (T.supplyRows+2*u.val)+f.val) = sourceAddress (fresh a f) := by
          subst a
          exact I.outputBit u f
        rw [Equiv.apply_symm_apply]
        exact lookup (portsAt.symm (anchorPort G j)) (anchorPort G j)
          (portsAt.apply_symm_apply _) ⟨histWidth sw v (anchorPort G j).1.1 + (k*i.val+b.val),by
            have bound := Nat.mul_le_mul_left k i.isLt
            rw [Nat.mul_succ] at bound
            have br := b.isLt
            rw [Nat.mul_comm r k]
            omega⟩
      · obtain ⟨⟨u,b⟩,rfl⟩ := (finSigmaFinEquiv (n:=fun u : Fin n=>base (B.ports u).1.1)).surjective bit
        refine Eq.trans ?_ (congrArg sourceAddress
          (partyPointer_old D G j base w B portsAt sw v old fresh (d:=d) i u b)).symm
        change gather T mem (sel+(finProdFinEquiv (i,Fin.natAdd k (finSigmaFinEquiv (n:=fun u : Fin n=>base (B.ports u).1.1) ⟨u,b⟩))).val) = _
        refine (mid (Fin.natAdd k (finSigmaFinEquiv (n:=fun u : Fin n=>base (B.ports u).1.1) ⟨u,b⟩))).trans ?_
        simp only [Fin.val_natAdd,Nat.not_lt_of_ge (Nat.le_add_right _ _),ite_false,
          Nat.add_sub_cancel_left,I.demandPort,I.demandDigit,I.tileWidth,I.inputWidth,I.inputBase]
        split <;> rename_i live
        · exact I.inputBit u ⟨_,live⟩
        · rfl
    · obtain ⟨⟨u,b⟩,rfl⟩ := finProdFinEquiv.surjective z
      rw [partyPointer_output]
      have hb := digits u b
      simp only [gather,Fin.val_natAdd,I.copies,I.ports,I.selectorBits,I.headerBits,I.tileBits,
        Nat.not_lt_of_ge (Nat.le_add_right _ _),ite_false,Nat.add_sub_cancel_left,hb.1,hb.2,
        I.outputWidth,Nat.add_zero]
      split <;> rename_i live
      · exact I.outputBit u ⟨b.val,by omega⟩
      · rfl

set_option Elab.async false

omit [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [DecidableEq H] [Nonempty H] in
/-- Bounds on the actual header page and source apertures justify every
selected memory access of the heterogeneous gather at a live output pin. -/
theorem gather_addresses_fit {T : Layout} {mem : ℕ → ℕ}
    (I : Image (d:=d) D G j base w B portsAt sw v old fresh T mem) (W : ℕ)
    (head : T.headerTable+2*(∑ u : Fin n,base (B.ports u).1.1)≤2^W)
    (outRows : T.supplyRows+2*e≤2^W) (inRows : T.demandRows+3*n≤2^W)
    (outs : ∀ u : Fin e,mem (T.supplyRows+2*u.val)+(histWidth sw v (portsAt u).1.1+r*k)≤2^W)
    (ins : ∀ u : Fin n,mem (T.demandRows+3*u.val)+w (B.ports u).1.1≤2^W)
    (digit : ∀ u : Fin n,base (B.ports u).1.1*r≤2^W)
    (x : Fin (r*(e*k)+(r*B.arity+e*(r*d)))) : AddressesFit W T mem x.val := by
  let sel : ℕ := r*(e*k)
  have out (u : Fin e) : T.supplyRows+2*u.val+1<2^W := by have h := u.isLt;omega
  have inp (u : Fin n) : T.demandRows+3*u.val+2<2^W := by have h := u.isLt;omega
  have selector (u : Fin e) (i : Fin r) (b : Fin k) :
      mem (T.supplyRows+2*u.val)+(mem (T.supplyRows+2*u.val+1)+(k*i.val+b.val))<2^W := by
    rw [I.outputWidth]
    have stop:=Nat.mul_le_mul_left k i.isLt
    rw [Nat.mul_succ,Nat.mul_comm k r] at stop
    have edge:=b.isLt
    have cap:=outs u
    omega
  refine Fin.addCases (fun z => ?_) (fun rest => ?_) x
  · obtain ⟨⟨i,q⟩,rfl⟩:=finProdFinEquiv.surjective z
    obtain ⟨⟨u,b⟩,rfl⟩:=finProdFinEquiv.surjective q
    let qq:=finProdFinEquiv (u,b)
    let zz:=finProdFinEquiv (i,qq)
    have hi : zz.val/(e*k) = i.val := (digits i qq).1
    have offset : zz.val/k%e=u.val ∧ zz.val%k=b.val := by
      have hp:=Nat.zero_lt_of_lt b.isLt
      have he:=Nat.zero_lt_of_lt u.isLt
      have repr : zz.val=b.val+k*(u.val+e*i.val) := by dsimp [zz,qq,finProdFinEquiv];ring
      rw [repr]
      simp [Nat.add_mul_div_left _ _ hp,Nat.div_eq_of_lt b.isLt,Nat.mod_eq_of_lt b.isLt,Nat.mod_eq_of_lt u.isLt]
    change AddressesFit W T mem zz.val
    simpa only [AddressesFit,I.copies,I.ports,I.selectorBits,ite_eq_left zz.isLt,offset.1,offset.2,hi] using
      (show T.supplyRows+2*u.val+1<2^W ∧ _ from ⟨out u,selector u i b⟩)
  · refine Fin.addCases (fun z => ?_) (fun z => ?_) rest
    · obtain ⟨⟨i,q⟩,rfl⟩:=finProdFinEquiv.surjective z
      change AddressesFit W T mem (sel+(finProdFinEquiv (i,q)).val)
      have hq := digits i q
      simp only [AddressesFit,I.copies,I.ports,I.selectorBits,I.headerBits,sel,
        Nat.not_lt_of_ge (Nat.le_add_right _ _),ite_false,Nat.add_sub_cancel_left,
        (finProdFinEquiv (i,q)).isLt,ite_true,hq.1,hq.2]
      refine Fin.addCases (fun b => ?_) (fun t => ?_) q
      · simpa only [Fin.val_castAdd,b.isLt,ite_true,I.anchor] using
          (show T.supplyRows+2*(portsAt.symm (anchorPort G j)).val+1<2^W ∧ _ from
            ⟨out _,selector (portsAt.symm (anchorPort G j)) i b⟩)
      · obtain ⟨⟨u,b⟩,rfl⟩:=(finSigmaFinEquiv (n:= fun u : Fin n=>base (B.ports u).1.1)).surjective t
        let hd:=(finSigmaFinEquiv (n:= fun u : Fin n=>base (B.ports u).1.1) ⟨u,b⟩).val
        have hv : hd<∑ a,base (B.ports a).1.1 := (finSigmaFinEquiv (n:= fun u : Fin n=>base (B.ports u).1.1) ⟨u,b⟩).isLt
        have rowRoom:=inp u
        have raw:=Nat.mul_le_mul_left (base (B.ports u).1.1) i.isLt
        rw [Nat.mul_succ] at raw
        have br:=b.isLt
        have endBit:=digit u
        have endRow:=ins u
        simp only [Fin.val_natAdd,Nat.not_lt_of_ge (Nat.le_add_right _ _),ite_false,
          Nat.add_sub_cancel_left,I.demandPort,I.demandDigit,I.tileWidth,I.inputWidth]
        exact ⟨by change T.headerTable+2*hd+1<2^W;omega,rowRoom,by omega,fun _ live=>by omega⟩
    · obtain ⟨⟨u,b⟩,rfl⟩:=finProdFinEquiv.surjective z
      have hb := digits u b
      simp only [AddressesFit,Fin.val_natAdd,I.copies,I.ports,I.selectorBits,I.headerBits,I.tileBits,
        Nat.not_lt_of_ge (Nat.le_add_right _ _),ite_false,Nat.add_sub_cancel_left,hb.1,hb.2,I.outputWidth]
      exact ⟨out u,fun live=>by have h := outs u;omega⟩

alias Image.addressesFit := gather_addresses_fit

end


end ThreeFlat.RAM.HistoryPartyGather

end OAI
