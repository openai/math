import OAI.Hierarchy.DescentTerminalShortSort
import OAI.Hierarchy.DescentTerminalPositiveBank

namespace OAI
/-! # Static bank of stable row sorts with its actual homogeneous sockets -/

namespace Hierarchy.DescentTerminalHost.SortBank
open Catalyst CatalystSubstitution Tagged ThreeFlat Routing SortNetwork Spill CallPool
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] {V E H : Type} [Fintype V] [Fintype E] [Fintype H]
variable {n s w d m L : ℕ}
abbrev Aux (n w L : ℕ) := Fin L×TerminalSort.Hole n w
abbrev Ports (n w : ℕ) := SortRelation.Ends n w ⊕ TerminalSort.Hole n w
abbrev BatchRead (n w L : ℕ) (V : Type) := Fin L→SortRelation.Ends n w→V ⊕ Bool

def wires (source : BatchRead n w L V) (i : Fin L) : Ports n w→(V ⊕ Aux n w L) ⊕ Bool :=
  Sum.elim (fun j=>(source i j).map Sum.inl id) (fun j=>Sum.inl (Sum.inr (i,j)))

def shell (digit : Fin d→Fin w) (source : BatchRead n w L V) :=
  WideHost.localFamily (A:=fun _ : Fin L=>Ports n w) (fun _=>SortRelation.shell F digit) (wires source)

def inside (source : BatchRead n w L V) (v : V→Bool) (i : Fin L) : Records n w :=
  SortedBlock.unwrap (fun j=>Sum.elim v id (source i (.inl j)))

def output (source : BatchRead n w L V) (v : V→Bool) (i : Fin L) : SortRelation.Data n w→Bool :=
  fun j=>Sum.elim v id (source i (.inr j))

def Accepts (digit : Fin d→Fin w) (source : BatchRead n w L V) (v : V→Bool) : Prop :=
  ∀i,output source v i=pack (TerminalSort.sorted digit (inside source v i))

theorem shell_eval (digit : Fin d→Fin w) (source : BatchRead n w L V)
    (v : V→Bool) (a : Aux n w L→Bool) :
    TypedWiring.value (shell (F:=F) digit source) (Sum.elim v a) =
    ∏i,TypedWiring.value (SortRelation.shell F digit)
      (Sum.elim (Sum.elim (pack (inside source v i)) (output source v i)) (fun j=>a (i,j))) := by
  rw [shell,WideHost.localFamily_eval]
  apply Finset.prod_congr rfl
  intro i _
  apply congrArg (TypedWiring.value _)
  funext u
  rcases u with (j|j)|j
  · simp only [inside,SortedBlock.pack_unwrap,Sum.elim_inl,Function.comp_apply,wires]
    cases source i (.inl j) <;> rfl
  · simp only [output,Sum.elim_inr,Sum.elim_inl,Function.comp_apply,wires]
    cases source i (.inr j) <;> rfl
  · rfl

theorem shell_price (digit : Fin d→Fin w) (source : BatchRead n w L V) :
    (shell (F:=F) digit source).cells+(shell (F:=F) digit source).internal ≤
    L*(2^n*((n+n+w)+(n+d+1)+(n+d+2)*176+28*w)+28*pins n (n+w)) := by
  rw [shell,WideHost.localFamily_size]
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using
    TerminalSort.shells_price (F:=F) (L:=L) (n:=n) digit

variable (field : Fin m→ℕ) (cover : (∑j,field j)=n+w) (room : ∀j,field j≤n+s)

def sockets (t : Fin (m*poolBatchCount L (2^s))) (j : Fin (pins (n+s) (n+s))) :
    (E ⊕ (H ⊕ Aux n w L)) ⊕ Bool :=
  (TerminalSort.read field cover room (finProdFinEquiv.symm t) j).map (fun z=>Sum.inr (Sum.inr z)) id

omit [Fintype E] [Fintype H] in
theorem sockets_eval (x : E→Bool) (a : H→Bool) (z : Aux n w L→Bool) :
    (∏i,coeff F (n+s) (n+s) (Sum.elim (Sum.elim x (Sum.elim a z)) id ∘ sockets field cover room i)) =
    ∏t : TerminalSort.Socket n s m L,coeff F (n+s) (n+s) (Sum.elim z id ∘ TerminalSort.read field cover room t) := by
  rw [←finProdFinEquiv.prod_comp]
  apply Finset.prod_congr rfl
  intro t _
  apply congrArg (coeff F _ _)
  funext j
  simp only [sockets,Equiv.symm_apply_apply,Function.comp_apply]
  cases TerminalSort.read field cover room t j <;> rfl

theorem close [Nonempty (Fin m)] (digit : Fin d→Fin w) (source : BatchRead n w L (E ⊕ H))
    (x : E→Bool) (a : H→Bool) :
    (∑z : Aux n w L→Bool,
      (∏i,coeff F (n+s) (n+s) (Sum.elim (Sum.elim x (Sum.elim a z)) id ∘ sockets field cover room i))*
      TypedWiring.value (shell (F:=F) digit source) (Sum.elim (Sum.elim x a) z)) =
      if Accepts digit source (Sum.elim x a) then 1 else 0 := by
  let v:=Sum.elim x a
  let curry := Equiv.curry (Fin L) (TerminalSort.Hole n w) Bool
  rw [←curry.symm.sum_comp]
  simp_rw [sockets_eval field cover room,shell_eval]
  simp_rw [mul_comm (∏ _ : TerminalSort.Socket n s m L,_)]
  have sorted := TerminalSort.sorts (F:=F) field cover room digit (inside source v) (output source v)
  refine Eq.trans ?_ (sorted.trans ?_)
  · apply Finset.sum_congr (congrArg (@Finset.univ (Fin L → TerminalSort.Hole n w → Bool))
      (Subsingleton.elim _ _))
    intro z _
    rfl
  · let ok := Accepts digit source v
    have same (p q : Decidable ok) : @ite F ok p 1 0 = @ite F ok q 1 0 := by
      rw [Subsingleton.elim p q]
    exact same _ _

variable {k p : ℕ}
def host (width : Fin k→ℕ) (Y : Approximation F k (pins (n+s) (n+s))) (digit : Fin d→Fin w)
    (verify : BitNetwork F (Fintype.card (Catalyst.Port p width ⊕ H))) (source : BatchRead n w L (Catalyst.Port p width ⊕ H)) :=
  DescentTerminalHost.host width (CollapseOracle.tagCall _ Y) (m*poolBatchCount L (2^s))
    (localCut verify (shell digit source)) (sockets field cover room)

theorem host_value [Nonempty (Fin m)] (width : Fin k→ℕ) (Y : Approximation F k (pins (n+s) (n+s)))
    (digit : Fin d→Fin w) (verify : BitNetwork F (Fintype.card (Catalyst.Port p width ⊕ H)))
    (source : BatchRead n w L (Catalyst.Port p width ⊕ H)) (x : Catalyst.Port p width→Bool) :
    exactValue _ (host field cover room width Y digit verify source) x =
      ∑a : H→Bool,TypedWiring.value verify (Sum.elim x a)*
        (if Accepts digit source (Sum.elim x a) then 1 else 0) := by
  refine (exact_host (H:=H ⊕ Aux n w L) width (CollapseOracle.tagCall (n+s) Y)
    (m*poolBatchCount L (2^s)) (localCut verify (shell digit source))
    (sockets field cover room) x).trans ?_
  let weight (a : H ⊕ Aux n w L → Bool) : F :=
    (∏ i,coeff F (n+s) (n+s) (Sum.elim (Sum.elim x a) id ∘ sockets field cover room i)) *
      TypedWiring.value (localCut verify (shell digit source)) (Sum.elim x a)
  trans ∑a,weight a
  · refine Finset.sum_congr ?_ (fun _ _ => rfl)
    exact congrArg (fun i : Fintype (H ⊕ Aux n w L → Bool) => @Finset.univ _ i)
      (Subsingleton.elim _ _)
  rw [←(Equiv.sumArrowEquivProdArrow H (Aux n w L) Bool).symm.sum_comp weight,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [←close field cover room digit source x a,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  change (∏ i,coeff F (n+s) (n+s) (Sum.elim (Sum.elim x (Sum.elim a z)) id ∘
    sockets field cover room i))*TypedWiring.value (localCut verify (shell digit source))
    (Sum.elim x (Sum.elim a z))=_
  rw [localCut_value]
  ring

theorem host_price (width : Fin k→ℕ) (Y : Approximation F k (pins (n+s) (n+s)))
    (digit : Fin d→Fin w) (verify : BitNetwork F (Fintype.card (Catalyst.Port p width ⊕ H)))
    (source : BatchRead n w L (Catalyst.Port p width ⊕ H)) :
    hostSize (host field cover room width Y digit verify source) ≤
      verify.cells+verify.internal+
      L*(2^n*((n+n+w)+(n+d+1)+(n+d+2)*176+28*w)+28*pins n (n+w))+
      29*((m*poolBatchCount L (2^s))*pins (n+s) (n+s))+
      (Fintype.card H+L*pins n (n+w))+Fintype.card (Catalyst.Port p width) := by
  refine (DescentTerminalHost.host_price (H:=H ⊕ Aux n w L) width (CollapseOracle.tagCall (n+s) Y)
    (m*poolBatchCount L (2^s)) (localCut verify (shell digit source))
    (sockets field cover room)).le.trans ?_
  have hiddenCount : Fintype.card (H ⊕ Aux n w L)=Fintype.card H+L*pins n (n+w) := by
    simp only [Aux,TerminalSort.Hole,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  rw [localCut_size,hiddenCount]
  dsimp only [CollapseOracle.tagCall]
  have sh:=shell_price (F:=F) digit source
  omega

end
end Hierarchy.DescentTerminalHost.SortBank

end OAI
