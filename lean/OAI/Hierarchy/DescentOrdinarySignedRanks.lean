import OAI.Hierarchy.DescentIncidentMeasuredOrder
import OAI.Hierarchy.DescentResetWindowRanksRAM

namespace OAI
/-! The three weighted ordinary rank queries share a fixed native comparator
and the original sparse, receiver-relative donor roster. -/
namespace Hierarchy.DescentOrdinarySignedRanks
open DescentSharedCableNames DescentParallelBase DescentResetSignedScan DescentSIMDLookup
open scoped Classical BigOperators
noncomputable section
variable {U E : Type} [DecidableEq U] [Fintype E] {N q k L K H G X : ℕ} {B : Ends U N}
variable (C : Blocks B E) (Z : Incidence.Census C q k L K) (P : ∀h,Local C h→ℕ)

def resident {ξ : Type*} (address : ξ↪Fin K) (j : Fin K) : Option ξ:=
  if has:∃e,address e=j then some has.choose else none
theorem resident_at {ξ : Type*} (address : ξ↪Fin K) (e : ξ) : resident address (address e)=some e:=by
  have has:∃u,address u=address e:=⟨e,rfl⟩
  simp [resident]
theorem resident_miss {ξ : Type*} (address : ξ↪Fin K) (j : Fin K) (miss:∀e,address e≠j) :
    resident address j=none:=by simp [resident,not_exists.mpr miss]

theorem sum_resident {ξ : Type*} [Fintype ξ] (a : ξ↪Fin K) (f : Option ξ→ℕ) (off : f none=0):
    (∑j,f (resident a j))=∑e,f (some e) :=by
  let active:=Finset.univ.map a
  have keep : ∑j:Fin K,f (resident a j)=∑j∈active,f (resident a j):=by
    apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro j _ outside
    have missing : ∀e,a e≠j:=fun e eqn=>outside (Finset.mem_map.mpr ⟨e,Finset.mem_univ _,eqn⟩)
    rw [resident_miss a j missing,off]
  rw [keep]
  simp [active,resident_at]

def parent (h:U) (e : Local C h) : Parent:=⟨P h e,(Z.source h e).val,(Z.ticket h e).val,(Z.mass h e).val⟩

def value (fit : ∀h,(B.incident h).card≤L) (h : U) (e : Local C h) (peer : Bool) :=
  if peer then B.serial (C.src e.val) (C.dst e.val) (C.order ⟨e.val,⟨0,e.property.1⟩⟩)
  else Incidence.pos C fit h e

omit [Fintype E] in
theorem value_lt (fit : ∀h,(B.incident h).card≤L) (h : U) (e : Local C h) (peer : Bool) :
    value C fit h e peer<L :=by
  cases peer with
  | false=>exact (B.position fit h (Incidence.candidate C h e ⟨0,e.property.1⟩)).isLt
  | true=>
    apply B.serial_lt fit (C.src e.val) (C.dst e.val)
    simp [Ends.parallel,C.atSource,C.atTarget]

theorem weighted (fit : ∀h,(B.incident h).card≤L)
    (peerEq : ∀h (e f : Local C h),P h e=P h f ↔ other C h e=other C h f)
    (h : U) (e : Local C h) (peer : Bool) :
    (∑j : Fin K,contribution peer (some (parent C Z P h e))
      ((resident (Z.addr h) j).map (parent C Z P h)))=value C fit h e peer :=by
  let pass (t : E):=if peer then C.parallel (C.src e.val) (C.dst e.val) t else (C.src t=h ∨ C.dst t=h)
  let term (t : E):=if pass t ∧ C.first t<C.first e.val then C.count t else 0
  have reduceSum:=sum_resident (Z.addr h) (fun v=>contribution peer (some (parent C Z P h e)) (v.map (parent C Z P h))) rfl
  rw [reduceSum]
  have compare (t : Local C h) : precedes (parent C Z P h t) (parent C Z P h e) ↔ C.first t.val<C.first e.val:=by
    simpa only [precedes,parent,Fin.lt_def,Fin.ext_iff] using (Z.chronology h t e).symm
  have row (t : Local C h):contribution peer (some (parent C Z P h e)) (some (parent C Z P h t))=term t.val:=by
    simp only [contribution,compare]
    simp only [parent, Z.weight]
    cases peer with
    | false=>simp [term,pass,t.property.2]
    | true=>
      simp only [term,pass,ite_true,true_implies]
      rw [other_parallel C h e t,←peerEq h t e]
      simp [and_comm]
  have convert : (∑t : Local C h,contribution peer (some (parent C Z P h e)) ((some t).map (parent C Z P h)))=
      ∑t:Local C h,term t.val:=Finset.sum_congr rfl (fun t _=>row t)
  rw [convert]
  have padding : (∑t:Local C h,term t.val)=∑t:E,term t :=by
    let live: E→Prop:=fun t=>0<C.count t ∧ (C.src t=h ∨ C.dst t=h)
    change (∑t:{u:E//live u},term t.val)=_
    rw [←Finset.sum_subtype (Finset.univ.filter live) (by simp) term]
    apply Finset.sum_subset (Finset.subset_univ _) ?_
    intro t _ absent
    by_cases valid:pass t
    · have present : C.src t=h ∨ C.dst t=h :=by
        cases peer with
        | false=>exact valid
        | true=>
          have ends:=e.property.2
          change C.parallel (C.src e.val) (C.dst e.val) t at valid
          unfold Blocks.parallel at valid
          rcases valid with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;> rw [hs, ht] <;> tauto
      have empty : C.count t=0:=by
        by_contra! positive
        exact absent (Finset.mem_filter.mpr ⟨Finset.mem_univ _,Nat.pos_of_ne_zero positive,present⟩)
      simp [term,empty]
    · simp [term,valid]
  rw [padding]
  cases peer with
  | false=>exact (Incidence.initial C h fit e).symm
  | true=>exact (C.first_serial e.val e.property.1).symm

/-- Query 2 observes the same parent at its true source. The other two compare
the local incident parents, counting all or only the common parallel class. -/
def point (h : U) (e : Local C h) (axis : Fin 3) : Σh,Local C h :=
  if axis.val=2 then ⟨C.src e.val,⟨e.val,e.property.1,Or.inl rfl⟩⟩ else ⟨h,e⟩

variable (home : Fin X→Fin H→Fin G→Option U)
def request (x : Fin X) (axis : Fin 3) (j : Fin K) (v : Fin H) (g : Fin G) : Option (Σh,Local C h):=
  (home x v g).bind (fun h=>(resident (Z.addr h) j).map (fun e=>point C h e axis))
def query (x : Fin X) (axis : Fin 3) (j : Fin K) (v : Fin H) (g : Fin G):=
  (request C Z home x axis j v g).map (fun z=>parent C Z P z.1 z.2)
def items (x : Fin X) (axis : Fin 3) (j i : Fin K) (v : Fin H) (g : Fin G):=
  (request C Z home x axis j v g).bind (fun pair=>(resident (Z.addr pair.1) i).map (parent C Z P pair.1))
def result (fit : ∀h,(B.incident h).card≤L) (x : Fin X) (axis : Fin 3) (j : Fin K) (v : Fin H) (g : Fin G):=
  (request C Z home x axis j v g).elim 0 (fun pair=>value C fit pair.1 pair.2 (Ranks.parallelQuery axis))

theorem physical (fit : ∀h,(B.incident h).card≤L)
    (peerEq : ∀h (e f : Local C h),P h e=P h f ↔ other C h e=other C h f)
    (x : Fin X) (axis : Fin 3) (j : Fin K) (v : Fin H) (g : Fin G):
    (∑i,contribution (Ranks.parallelQuery axis) (query C Z P home x axis j v g) (items C Z P home x axis j i v g))=
      result C Z home fit x axis j v g :=by
  cases h:request C Z home x axis j v g with
  | none=>simp [query,items,result,h,contribution]
  | some e=>simpa [query,items,result,h] using weighted C Z P fit peerEq e.1 e.2 (Ranks.parallelQuery axis)

omit [Fintype E] in
theorem result_small {b : ℕ} (fit : ∀h,(B.incident h).card≤L) (digits : L<2^b)
    (x : Fin X) (axis : Fin 3) (j : Fin K) (v : Fin H) (g : Fin G):
    result C Z home fit x axis j v g<2^b :=by
  cases h:request C Z home x axis j v g with
  | none=>simp [result,h]
  | some e=>simpa only [result,h,Option.elim_some] using (value_lt C fit e.1 e.2 (Ranks.parallelQuery axis)).trans digits

end
end Hierarchy.DescentOrdinarySignedRanks

end OAI
