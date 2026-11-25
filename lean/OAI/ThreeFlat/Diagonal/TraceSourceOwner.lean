import OAI.ThreeFlat.Diagonal.TraceSourceDigits
import OAI.ThreeFlat.Diagonal.TraceUniformLayout
import OAI.ThreeFlat.RAM.ContractionMemory

namespace OAI
/-! # Arithmetic owner rows agree with the trace's physical wire layout -/

namespace ThreeFlat.Diagonal.TraceSourceOwner

open Computability.VPVNP TracePhysical TraceUniformRow LaneCursor
variable {w p r k S f d n lane low : ℕ}

theorem physical_shared (fit : S+f ≤ 2^(1+d)) (a : TracePhysical.Shared w r f d) :
    (locate (shape w p r k S f d n) (sharedOrdinal w r f d a).val).1 =
      (TracePhysical.sharedOwner fit a).val := by
  let s := shape w p r k S f d n
  rcases a with ⟨t,j⟩ | (⟨l,v,b,j⟩ | ⟨v,j⟩)
  · have eq := locate_cpu s t.isLt j.isLt
    simpa [s,shape,cpuOrdinal,TracePhysical.sharedOwner,Nat.mul_comm,Nat.add_comm] using congrArg Prod.fst eq
  · let bit := b.val*s.edge+j.val
    have hb : bit<s.track := pack_lt j.isLt b.isLt
    have h := congrArg Prod.fst (locate_sort s l.isLt v.isLt hb)
    have addr : (sharedOrdinal w r f d (.inr (.inl (l,v,b,j)))).val =
        s.ticks*s.cpu+(l.val*(s.rows*s.track)+(v.val*s.track+bit)) := by
      rw [sortOrdinal]
      dsimp [bit,s,shape,Shape.track]
      ring
    rw [addr]
    exact h
  · have h := congrArg Prod.fst (locate_edge s v.isLt j.isLt)
    have addr : (sharedOrdinal w r f d (.inr (.inr (v,j)))).val =
        s.ticks*s.cpu+(s.layers*(s.rows*s.track)+(v.val*s.edge+j.val)) := by
      rw [boundaryOrdinal]
      dsimp [s,shape,Shape.track]
      ring
    rw [addr]
    exact h

theorem baseCount_eq (s : Shape) (e : ℕ) :
    (s.ticks*s.cpu+(s.layers*(s.rows*s.track)+(s.rows-1)*s.edge))+e =
      s.ticks*s.cpu+(s.layers*(s.rows*s.track)+((s.rows-1)*s.edge+e)) := by omega

theorem shared_card (w p r k S f d n : ℕ) :
    let s := shape w p r k S f d n
    Fintype.card (TracePhysical.Shared w r f d) =
      s.ticks*s.cpu+(s.layers*(s.rows*s.track)+(s.rows-1)*s.edge) :=
  (TracePhysical.sharedCount_card ..).symm

theorem uniform_hidden (fit : S+f ≤ 2^(1+d)) (a : Fin (SharedCount w p r k d f)) :
    (locate (shape w p r k S f d n) a.val).1 = (TraceUniformRow.hiddenOwner fit a).val := by
  refine Fin.addCases ?_ ?_ a
  · intro i
    obtain ⟨z,rfl⟩ := (sharedOrdinal w r f d).surjective i
    simpa [TraceUniformRow.hiddenOwner,TracePhysical.hiddenOwner] using
      (physical_shared (p:=p) (k:=k) (n:=n) fit z)
  · intro i
    obtain ⟨⟨v,j⟩,rfl⟩ := (finProdFinEquiv (m := 2^d) (n := (1+6*p+k)*w)).surjective i
    let s := shape w p r k S f d n
    have h := congrArg Prod.fst (locate_copy s v.isLt j.isLt)
    simp only [TraceUniformRow.hiddenOwner,Fin.addCases_right,Equiv.symm_apply_apply,Fin.val_natAdd]
    change (locate s (Fintype.card _ + (j.val+s.copy*v.val))).1 = v.val
    rw [shared_card w p r k S f d n]
    rw [show (s.ticks*s.cpu+(s.layers*(s.rows*s.track)+(s.rows-1)*s.edge))+
      (j.val+s.copy*v.val) = s.ticks*s.cpu+(s.layers*(s.rows*s.track)+((s.rows-1)*s.edge+(v.val*s.copy+j.val))) by ring]
    exact h

theorem block_hidden (fit : S+f ≤ 2^(1+(lane+low)))
    (i : Fin (SharedCount w p r k (lane+low) f + (2^lane*2^low)*n)) :
    (locate (shape w p r k S f (lane+low) n) i.val).1 =
      (TraceCircuit.blockHiddenRow (TracePhysical.laneRow ∘ TraceUniformRow.hiddenOwner fit) i).val := by
  refine Fin.addCases ?_ ?_ i
  · intro a
    simpa [TraceCircuit.blockHiddenRow,TracePhysical.laneRow] using
      (uniform_hidden (n:=n) fit a)
  · intro i
    obtain ⟨⟨v,j⟩,rfl⟩ := (finProdFinEquiv (m := 2^lane*2^low) (n := n)).surjective i
    let s := shape w p r k S f (lane+low) n
    have h := congrArg Prod.fst (locate_gate (v:=v.val) s j.isLt)
    simp only [TraceCircuit.blockHiddenRow,Fin.addCases_right,Equiv.symm_apply_apply,Fin.val_natAdd]
    change (locate s ((Fintype.card _+s.rows*s.copy)+(j.val+n*v.val))).1 = v.val
    rw [shared_card w p r k S f (lane+low) n]
    rw [show ((s.ticks*s.cpu+(s.layers*(s.rows*s.track)+(s.rows-1)*s.edge))+s.rows*s.copy)+(j.val+n*v.val) =
      s.ticks*s.cpu+(s.layers*(s.rows*s.track)+((s.rows-1)*s.edge+(s.rows*s.copy+(v.val*s.gates+j.val)))) by
        change _ = s.ticks*s.cpu+(s.layers*(s.rows*s.track)+((s.rows-1)*s.edge+(s.rows*s.copy+(v.val*n+j.val))))
        ring]
    exact h

theorem source_owner (fit : S+f ≤ 2^(1+(lane+low))) (v : Row lane low)
    (z : BitSource (SharedCount w p r k (lane+low) f+(2^lane*2^low)*n) (S*w)) :
    ownerNat w p r k S f (lane+low) n v.val (RAM.BitLayout.sourceAddress z) =
      (sourceRow (TraceCircuit.blockHiddenRow (TracePhysical.laneRow ∘ TraceUniformRow.hiddenOwner fit))
        (TracePhysical.laneRow ∘ TracePhysical.headerOwner fit) v z).val := by
  cases z with
  | constant b => cases b <;> simp [ownerNat,appendAt,RAM.BitLayout.sourceAddress,sourceRow]
  | hidden i =>
    simpa only [ownerNat,RAM.BitLayout.sourceAddress,RAM.BitLayout.hiddenBase,Nat.add_assoc,appendAt_right,
      sourceRow] using block_hidden fit i
  | pin j =>
    obtain ⟨⟨a,b⟩,rfl⟩ := (finProdFinEquiv (m := S) (n := w)).surjective j
    simp only [ownerNat,RAM.BitLayout.sourceAddress,appendAt_right,appendAt_left _ _ (finProdFinEquiv (a,b)).isLt,
      sourceRow,Function.comp_apply,TracePhysical.headerOwner,Equiv.symm_apply_apply,TracePhysical.laneRow]
    change (b.val+w*a.val)/w/2 = a.val/2
    rw [Nat.add_comm,Nat.mul_comm w,pack_div b.isLt]

end ThreeFlat.Diagonal.TraceSourceOwner

end OAI
