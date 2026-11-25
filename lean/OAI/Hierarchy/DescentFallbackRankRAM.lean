import OAI.Hierarchy.DescentApertureExpressions
import OAI.Hierarchy.DescentFallbackShapeTable
import OAI.Hierarchy.ProtocolRAMCheapCode
import OAI.Hierarchy.DescentPairedKeyComparison

namespace OAI
/-! # Executable degree-aperture scan for the installed fallback book -/

namespace Hierarchy.DescentFallbackRankRAM
open DescentFallbackLeafScan DescentFallbackShapeTable DescentContacts DescentPairedKeyComparison
open ThreeFlat.RAM DescriptorExpr Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {w Y Δ cap H k D g f : ℕ} {V : Type} [Fintype V] [DecidableEq V]

/-- The encoded shape zero denotes an empty candidate. A genuine shape
number is incremented, so a legal shape whose paired name is zero survives. -/
def pass (host shape : Expr) (target : Option (Expr×Expr)) :=
  match target with
  | none=>Expr.lit 1
  | some (v,z)=>earlier host (.op .sub shape (.lit 1)) v z (.lit 1) (.lit 0)

def testSlot (peers : Fin Δ→Expr) (shapes : Fin Δ×Fin cap→Expr) (limit : ℕ)
    (target : Option (Expr×Expr)) (j : Fin Δ×Fin cap) : Expr :=
  let v:=peers j.1
  let z:=shapes j
  .branch .eq v (.lit limit) (.lit 0)
    (unlessSeen v (.branch .eq z (.lit 0) (.lit 0) (pass v z target)) ((prior j.1).map peers))

def measure (peers : Fin Δ→Expr) (shapes : Fin Δ×Fin cap→Expr) (limit : ℕ) (target : Option (Expr×Expr)) : Expr :=
  foldSum ((Finset.univ : Finset (Fin Δ×Fin cap)).toList.map (testSlot peers shapes limit target))

variable (roster : V→Fin Δ→Option V) (vertex : V↪Fin H) (hub : V→Bool)
variable (source : V×Endpoint Y) (m : Memory w) (r : Word w)
variable (peers : Fin Δ→Expr) (shapes : Fin Δ×Fin cap→Expr)

def hostDigit (z : Option V) := z.elim H (fun v=>(vertex v).val)

omit [Fintype V] [DecidableEq V] in
theorem hostDigit_inj : Function.Injective (hostDigit vertex) := by
  rintro (_|a) (_|b) eqn
  · rfl
  · change H=(vertex b).val at eqn
    have := (vertex b).isLt;omega
  · change (vertex a).val=H at eqn
    have := (vertex a).isLt;omega
  · exact congrArg some (vertex.injective (Fin.ext eqn))

omit [Fintype V] in
/-- Per-slot expression output, using the true old neighbor aperture and
possibly duplicated old neighbor IDs. -/
theorem slot_eval (wide : H<2^w)
    (peerRead : ∀j,(peers j).eval m r=(hostDigit vertex (roster source.1 j):Word w))
    (shapeRead : ∀j v,roster source.1 j.1=some v→
      ((shapes j).eval m r).val=encode (localSlot (localShape k D g f source.2 (hub v)) j.2))
    (target : Option (Expr×Expr)) (keep : V×Endpoint Y→Bool)
    (selects : ∀j (v : V) (z : Endpoint Y),roster source.1 j.1=some v →
      localSlot (localShape k D g f source.2 (hub v)) j.2=some z →
      (pass (peers j.1) (shapes j) target).eval m r=((keep (v,z)).toNat:Word w))
    (i : Fin Δ×Fin cap) :
    (testSlot peers shapes H target i).eval m r=
      (((candidate (k:=k) (D:=D) (g:=g) (f:=f) hub roster source i).any keep).toNat:Word w) := by
  have digitBound (j) : hostDigit vertex (roster source.1 j)<2^w := by
    cases h:roster source.1 j with
    | none=>exact wide
    | some v=>exact (vertex v).isLt.trans wide
  have dup : (∃x∈(prior i.1).map peers,x.eval m r=(peers i.1).eval m r) ↔
      ∃j : Fin Δ,j < i.1 ∧ roster source.1 j=roster source.1 i.1 := by
    simp only [List.mem_map,exists_exists_and_eq_and,prior,Finset.mem_toList,Finset.mem_filter,Finset.mem_univ,true_and]
    apply exists_congr
    intro j
    rw [peerRead,peerRead]
    have h (s t : ℕ) (hs : s<2^w) (ht : t<2^w) : ((s:Word w)=(t:Word w)) ↔ s=t := by
      rw [Fin.ext_iff,Fin.val_cast_of_lt hs,Fin.val_cast_of_lt ht]
    rw [h _ _ (digitBound _) (digitBound _),(hostDigit_inj vertex).eq_iff]
  unfold testSlot
  simp only [Expr.eval,Comparison.test,beq_iff_eq,unlessSeen_eval,dup]
  cases peerEq : roster source.1 i.1 with
  | none=>
    have no : first roster source.1 i.1=none := by simp [first,peerEq]
    simp [peerRead,peerEq,hostDigit,candidate,no]
  | some v=>
    have valid : (peers i.1).eval m r≠(H:Word w) := by
      intro eqn
      rw [peerRead, peerEq] at eqn
      change ((vertex v).val : Word w) = (H : Word w) at eqn
      have same := congrArg Fin.val eqn
      rw [Fin.val_cast_of_lt ((vertex v).isLt.trans wide), Fin.val_cast_of_lt wide] at same
      exact (vertex v).isLt.ne same
    rw [ite_eq_right valid]
    by_cases repeated : ∃ j : Fin Δ, j < i.1 ∧ roster source.1 j = some v
    · have absent : first roster source.1 i.1 = none := by
        rw [first, peerEq, ite_eq_left repeated]
      rw [ite_eq_left repeated]
      simp [candidate, absent]
    · rw [ite_eq_right repeated]
      have one : first roster source.1 i.1 = some v := by
        rw [first, peerEq, ite_eq_right repeated]
      have read:=shapeRead i v peerEq
      cases shapeEq : localSlot (localShape k D g f source.2 (hub v)) i.2 with
      | none=>simp only [shapeEq,encode,Option.elim_none] at read
              have zero : (shapes i).eval m r=0 := Fin.ext read
              simp [zero,candidate,one,shapeEq]
      | some z=>
        have nz : (shapes i).eval m r ≠ ((0 : ℕ) : Word w) := by
          intro eqn
          simp [eqn,shapeEq,encode] at read
        rw [ite_eq_right nz,selects i v z peerEq shapeEq]
        simp [candidate,one,shapeEq]

theorem pass_all (v z : Expr) : (pass v z none).eval m r=(1:Word w) := rfl

omit [Fintype V] [DecidableEq V] in
theorem pass_before (src word dest target : Expr) (v u : V) (x y : Endpoint Y)
    (srcRead : (src.eval m r).val=(vertex v).val)
    (shapeRead : (word.eval m r).val=shapeNumber x+1)
    (dstRead : (dest.eval m r).val=(vertex u).val)
    (targetRead : (target.eval m r).val=shapeNumber y) :
    (pass src word (some (dest,target))).eval m r=
      ((decide (DescentRosterOrder.endpoint (vertex.trans Fin.valEmbedding) (v,x) <
        DescentRosterOrder.endpoint (vertex.trans Fin.valEmbedding) (u,y))).toNat:Word w) := by
  have fit : shapeNumber x+1<2^w := shapeRead ▸ (word.eval m r).isLt
  have n : word.eval m r=((shapeNumber x+1:ℕ):Word w) :=
    Fin.ext (shapeRead.trans (Fin.val_cast_of_lt fit).symm)
  have sub : ((Expr.op .sub word (.lit 1)).eval m r).val=shapeNumber x := by
    change (word.eval m r-(1:Word w)).val=_
    rw [n,Nat.cast_add,Nat.cast_one,add_sub_cancel_right,Fin.val_cast_of_lt (by omega)]
  rw [pass,earlier_eval,srcRead,dstRead,sub,targetRead,endpoint_read,endpoint_read]
  change (if Nat.pair (vertex v).val (shapeNumber x)<Nat.pair (vertex u).val (shapeNumber y)
    then (1:Word w) else 0)=
      ((decide (Nat.pair (vertex v).val (shapeNumber x)<Nat.pair (vertex u).val (shapeNumber y))).toNat:Word w)
  by_cases before : Nat.pair (vertex v).val (shapeNumber x) < Nat.pair (vertex u).val (shapeNumber y)
  · simp [before]
  · simp [before]

omit [Fintype V] in
theorem count_eval (target : Option (Expr×Expr)) (keep : V×Endpoint Y→Bool)
    (localRead : ∀i : Fin Δ×Fin cap,(testSlot peers shapes H target i).eval m r=
      (((candidate (k:=k) (D:=D) (g:=g) (f:=f) hub roster source i).any keep).toNat:Word w)) :
    (measure peers shapes H target).eval m r=
      ((Finset.univ.filter (fun i : Fin Δ×Fin cap=>(candidate (k:=k) (D:=D) (g:=g) (f:=f) hub roster source i).any keep)).card:Word w) := by
  rw [measure,foldSum_eval,List.map_map]
  simp only [Function.comp_def,localRead]
  rw [Finset.sum_map_toList]
  simp [Bool.toNat,Finset.sum_boole]

omit [Fintype V] in
theorem all_slots (wide : H<2^w)
    (peerRead : ∀j,(peers j).eval m r=(hostDigit vertex (roster source.1 j):Word w))
    (shapeRead : ∀j v,roster source.1 j.1=some v→
      ((shapes j).eval m r).val=encode (localSlot (localShape k D g f source.2 (hub v)) j.2)) :
    (measure peers shapes H none).eval m r=
      ((Finset.univ.filter (fun j : Fin Δ×Fin cap=>
        (candidate (k:=k) (D:=D) (g:=g) (f:=f) hub roster source j).isSome)).card:Word w) := by
  have val:=count_eval roster hub source m r peers shapes (H:=H) none (fun _=>true)
    (slot_eval roster vertex hub source m r peers shapes wide peerRead shapeRead none (fun _=>true)
      (by intros;rfl))
  have any (o : Option (V×Endpoint Y)) : o.any (fun _=>true)=o.isSome := by cases o <;> rfl
  simpa only [any] using val

omit [Fintype V] in
theorem earlier_slots (dst shape : Expr) (y : V×Endpoint Y) (wide : H<2^w)
    (peerRead : ∀j,(peers j).eval m r=(hostDigit vertex (roster source.1 j):Word w))
    (shapeRead : ∀j v,roster source.1 j.1=some v→
      ((shapes j).eval m r).val=encode (localSlot (localShape k D g f source.2 (hub v)) j.2))
    (dstRead : (dst.eval m r).val=(vertex y.1).val) (targetRead : (shape.eval m r).val=shapeNumber y.2) :
    (measure peers shapes H (some (dst,shape))).eval m r=
      ((Finset.univ.filter (fun j : Fin Δ×Fin cap=>
        ((candidate (k:=k) (D:=D) (g:=g) (f:=f) hub roster source j).any fun x=>
          decide (DescentRosterOrder.endpoint (vertex.trans Fin.valEmbedding) x <
            DescentRosterOrder.endpoint (vertex.trans Fin.valEmbedding) y)))).card:Word w) := by
  apply count_eval
  apply slot_eval roster vertex hub source m r peers shapes wide peerRead shapeRead
  intro j v z hit localEq
  apply pass_before vertex m r _ _ _ _ v y.1 z y.2 _ _ dstRead targetRead
  · rw [peerRead, hit]
    change ((vertex v).val : Word w).val = (vertex v).val
    exact Fin.val_cast_of_lt ((vertex v).isLt.trans wide)
  · simpa [localEq,encode] using shapeRead j v hit

end
end Hierarchy.DescentFallbackRankRAM

end OAI
