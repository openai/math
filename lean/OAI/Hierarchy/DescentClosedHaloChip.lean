import OAI.Hierarchy.DescentApertureExpressions

namespace OAI
/-! A single numerical halo lookup compares every old port once for membership
and once for rank. The possible repeated self-loop is explicitly skipped. -/
namespace Hierarchy.DescentClosedHaloChip
open DescentFallbackRankRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {D H w out : ℕ}

def existsWord (src : Fin D→Expr) (z : Expr) : List (Fin D)→Expr
  | []=>.lit 0
  | i::is=>.branch .eq (src i) z (.lit 1) (existsWord src z is)

def less (x y : Expr) : Expr:=.branch .lt x y (.lit 1) (.lit 0)
def bit (src : Fin D→Expr) (v z : Expr) (i : Fin D) : Expr:=.branch .eq (src i) v (.lit 0) (less (src i) z)
def total (src : Fin D→Expr) (v z : Expr) : Expr:=
  .op .add (less v z) (foldSum ((Finset.univ : Finset (Fin D)).toList.map (bit src v z)))
def chip (src : Fin D→Expr) (v z shape : Expr) : Expr:=
  let found:=Expr.branch .eq v z (.lit 1) (existsWord src z (List.finRange D))
  .branch .eq found (.lit 1) (.op .add (.op .add shape (.lit 1)) (total src v z)) (.lit 0)

def weight (p : Fin D→Option (Fin H)) (v z : Fin H) : ℕ:=
  (if v<z then 1 else 0)+∑i,if (p i).any (fun a=>decide (a≠v ∧ a<z)) then 1 else 0

def value (p : Fin D→Option (Fin H)) (v z : Fin H) (shape : ℕ) : ℕ:=
  if z=v ∨ ∃i,p i=some z then shape+1+weight p v z else 0

theorem find_fits {src : Fin D→Expr} {z : Expr} (s : ∀i,(src i).Fits w out) (t : z.Fits w out) :
    ∀l,(existsWord src z l).Fits w out
  | []=>trivial
  | i::xs=>⟨s i,t,trivial,find_fits s t xs⟩

private theorem sum_fits (l : List Expr) (h : ∀e∈l,e.Fits w out) : (foldSum l).Fits w out:=by
  induction l with
  | nil=>trivial
  | cons e l ih=>exact ⟨h e (.head _),ih (fun f hf=>h f (.tail _ hf))⟩

theorem total_fits {src : Fin D→Expr} {v z : Expr} (s : ∀i,(src i).Fits w out)
    (root : v.Fits w out) (t : z.Fits w out) : (total src v z).Fits w out:=by
  refine ⟨⟨root,t,trivial,trivial⟩,sum_fits _ ?_⟩
  intro e he
  obtain ⟨i,_,rfl⟩:=List.mem_map.mp he
  exact ⟨s i,root,trivial,⟨s i,t,trivial,trivial⟩⟩

theorem fits {src : Fin D→Expr} {v z shape : Expr} (s : ∀i,(src i).Fits w out)
    (root : v.Fits w out) (t : z.Fits w out) (q : shape.Fits w out) : (chip src v z shape).Fits w out:=by
  refine ⟨⟨root,t,trivial,find_fits s t _⟩,trivial,⟨⟨q,trivial⟩,⟨⟨root,t,trivial,trivial⟩,sum_fits _ ?_⟩⟩,trivial⟩
  intro e he
  obtain ⟨i,_,rfl⟩:=List.mem_map.mp he
  exact ⟨s i,root,trivial,⟨s i,t,trivial,trivial⟩⟩

private theorem eqWord {x y : ℕ} (hx : x<2^w) (hy : y<2^w) :
    Comparison.eq.test (x:Word w) (y:Word w)=decide (x=y) := by
  by_cases same : x=y
  · simp [Comparison.test,same]
  · have neq : (x:Word w)≠(y:Word w):=fun h=>same (by
      simpa [Fin.val_cast_of_lt hx,Fin.val_cast_of_lt hy] using congrArg Fin.val h)
    simp [Comparison.test,same,neq]
private theorem ltWord {x y : ℕ} (hx : x<2^w) (hy : y<2^w) :
    Comparison.lt.test (x:Word w) (y:Word w)=decide (x<y) := by
  simp [Comparison.test,Fin.lt_def,Fin.val_cast_of_lt hx,Fin.val_cast_of_lt hy]

private theorem eqPort (p : Fin D→Option (Fin H)) (host : H<2^w) (i : Fin D) (a : Fin H) : Comparison.eq.test (((p i).elim H Fin.val : ℕ) : Word w) (a.val:Word w)=decide (p i=some a):=by
    cases hit : p i with
    | none=>simp [eqWord host (a.isLt.trans host),Nat.ne_of_gt a.isLt]
    | some b=>simp [eqWord (b.isLt.trans host) (a.isLt.trans host),Fin.ext_iff]

theorem find_eval (p : Fin D→Option (Fin H)) (z : Fin H) (src : Fin D→Expr) (query : Expr)
    (m : Memory w) (r : Word w) (host : H<2^w) (s : ∀i,(src i).eval m r=(((p i).elim H Fin.val : ℕ) : Word w))
    (there : query.eval m r=(z.val:Word w)) (l : List (Fin D)) : (existsWord src query l).eval m r=if ∃i∈l,p i=some z then 1 else 0:=by
    induction l with
    | nil=>simp [existsWord,Expr.eval]
    | cons i l ih=>
      change (if Comparison.eq.test ((src i).eval m r) (query.eval m r) then (1:Word w)
        else (existsWord src query l).eval m r)=_
      rw [s i,there,eqPort p host i z,ih]
      by_cases found : p i=some z <;> simp [found]

theorem total_eval (p : Fin D→Option (Fin H)) (v z : Fin H) (src : Fin D→Expr) (root query : Expr)
    (m : Memory w) (r : Word w) (host : H<2^w) (s : ∀i,(src i).eval m r=(((p i).elim H Fin.val : ℕ) : Word w))
    (here : root.eval m r=(v.val:Word w)) (there : query.eval m r=(z.val:Word w)) :
    (total src root query).eval m r=(weight p v z:Word w) := by
  have h₁:=v.isLt.trans host
  have h₂:=z.isLt.trans host
  have bits (i : Fin D) : (bit src root query i).eval m r=
      ((if (p i).any (fun a=>decide (a≠v ∧ a<z)) then 1 else 0:ℕ):Word w):=by
    simp only [bit,less,Expr.eval,s,here,there,eqPort p host]
    cases h : p i with
    | none=>simp [ltWord host h₂,Nat.not_lt_of_ge z.isLt.le]
    | some x=>
      by_cases same : x=v
      · subst x;simp
      · have cmp : Comparison.lt.test (x.val:Word w) (z.val:Word w)=decide (x<z) :=
          ltWord (x.isLt.trans host) h₂
        by_cases early : x<z <;> simp [same,cmp,early]
  have rootCmp : Comparison.lt.test (v.val:Word w) (z.val:Word w)=decide (v<z) :=
    ltWord h₁ h₂
  simp only [total,Expr.eval,less,here,there,rootCmp,foldSum_eval,List.map_map,Function.comp_def,bits,Finset.sum_map_toList,
    RowOp.opcode,BinaryOp.eval,weight,Nat.cast_add,Nat.cast_sum]
  by_cases before : v<z <;> simp [before]

theorem eval (p : Fin D→Option (Fin H)) (v z : Fin H) (k : ℕ) (src : Fin D→Expr) (root query shape : Expr)
    (m : Memory w) (r : Word w) (host : H<2^w) (s : ∀i,(src i).eval m r=(((p i).elim H Fin.val : ℕ) : Word w))
    (here : root.eval m r=(v.val:Word w)) (there : query.eval m r=(z.val:Word w))
    (payload : shape.eval m r=(k:Word w)) :
    (chip src root query shape).eval m r=(value p v z k:Word w) := by
  have h₁:=v.isLt.trans host
  have h₂:=z.isLt.trans host
  have wide : 1<2^w:=by have pos:=Nat.zero_lt_of_lt v.isLt;omega
  have find : (existsWord src query (List.finRange D)).eval m r =
      if ∃ i,p i=some z then (1:Word w) else 0 := by
    simpa only [List.mem_finRange,true_and] using
      find_eval p z src query m r host s there (List.finRange D)
  have sum := total_eval p v z src root query m r host s here there
  have sep : (0:Word w)≠1:=fun h=>by
    have b:=congrArg Fin.val h
    change (0:ℕ)%2^w=1%2^w at b
    simp [Nat.mod_eq_of_lt wide] at b
  have selfTest : Comparison.eq.test (v.val:Word w) (z.val:Word w)=decide (z=v) := by
    rw [eqWord h₁ h₂]
    by_cases same : z=v
    · subst z; simp
    · have distinct : v.val≠z.val := fun h=>same (Fin.ext h).symm
      simp [same,distinct]
  let flag := Expr.branch .eq root query (.lit 1) (existsWord src query (List.finRange D))
  have flagValue : flag.eval m r = if z=v ∨ ∃ i,p i=some z then (1:Word w) else 0 := by
    change (if Comparison.eq.test (root.eval m r) (query.eval m r) then (1:Word w)
      else (existsWord src query (List.finRange D)).eval m r)=_
    rw [here,there,selfTest,find]
    by_cases same : z=v <;> simp [same]
  change (if Comparison.eq.test (flag.eval m r) (1:Word w) then
    (shape.eval m r+1)+(total src root query).eval m r else 0)=_
  rw [flagValue,payload,sum]
  by_cases hit : z=v ∨ ∃ i,p i=some z
  · simp [hit,value,Comparison.test,Nat.cast_add]
  · simp [hit,value,Comparison.test,sep]

end
end Hierarchy.DescentClosedHaloChip

end OAI
