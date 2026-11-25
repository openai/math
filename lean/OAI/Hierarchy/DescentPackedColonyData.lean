import OAI.Hierarchy.DescentPackedSplitContribution

namespace OAI
/-! # Local dictionaries for descending real split layers in the packed common host -/
namespace Hierarchy.DescentPackedColony
open DescentSIMDLookup DescentColonies DescentColonies.PackedSplit DescentGL
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {H G k b : ℕ}

abbrev width (k : ℕ) := 1+k*2^k
abbrev Panel (k : ℕ) := Cell (width k)
abbrev Counts (k b : ℕ) := Cell (b*2^k)

def counts (b : ℕ) (f : Block k→ℕ) : Counts k b := encode b (2^k) (fun i=>(f i:Cell b))
def flags (f : Flags k) : Panel k := present (encodeFlags f)

def cache (rows : Scan.Buffer (Fin H) k) (v : Fin H) := flags (actualFlags rows v)

def atDepth (p : Panel k) (d : ℕ) (x : Block k) : Bool :=
  if p=0 then false else if h:d<k then decodeFlags (strip p) ⟨d,h⟩ x else false

def reach (d z : ℕ) (p : Panel k) (x : Block k) : Bool :=
  decide (∃y : Block k,group d y=group d x ∧ atDepth p z y=true)

def paintIn (a μ : Bits k) (p : Counts k b) (x : Block k) :=
  multiplierLoad (fun _ : Unit=>fun z=>( (encode b (2^k)).symm p z).val) a μ () x

def ownFlag (a μ : Bits k) (cap d : ℕ) (prior : Panel k) (wt : Counts k b) : Flags k :=
  fun level x=>if level.val=d then
    decide (cap<(Scan.readWeights (fun _ : Unit=>paintIn a μ wt) d () x).sum) || reach d (d+1) prior x
    else atDepth prior level.val x

def baseUpdate (a μ : Bits k) (cap d : ℕ) (prior : Panel k) (wt : Counts k b) : Panel k :=
  if prior=0 then 0 else flags (ownFlag a μ cap d prior wt)

def mergeFlags (D d : ℕ) (f : Flags k) (p : Panel k) : Flags k :=
  fun level x=>if level.val=d then f level x || reach d (d+D) p x else f level x

def merge (D d : ℕ) (current p : Panel k) : Panel k :=
  if current=0 then 0 else flags (mergeFlags D d (decodeFlags (strip current)) p)

@[simp] theorem base_zero (a μ : Bits k) (cap d : ℕ) : baseUpdate (b:=b) a μ cap d 0 0=0 := by simp [baseUpdate]
@[simp] theorem merge_zero (D d : ℕ) : merge (k:=k) D d 0 0=0 := by simp [merge]

@[simp] theorem merge_live (D d : ℕ) (f : Flags k) (p : Panel k) :
    merge D d (flags f) p=flags (mergeFlags D d f p) := by simp [merge,flags]

theorem paintIn_read (a μ : Bits k) (W : Fin H→Block k→ℕ) (v : Fin H) (room : ∀x,W v x<2^b)
    (x : Block k) : paintIn a μ (counts b (W v)) x=multiplierLoad W a μ v x := by
  simp only [paintIn,counts,Equiv.symm_apply_apply,multiplierLoad]
  cases preimageWord a μ x with
  | none=>rfl
  | some y=>exact Fin.val_cast_of_lt (room _)

private theorem beyond (inc : Fin H→List (Fin H)) (W : Fin H→Block k→ℕ) (D cap : ℕ)
    (s : ℕ) (sh : s≤k) (v : Fin H) (z : ℕ) (hz : k≤z) (x : Block k) :
    Scan.lookup (Scan.build inc W D cap s) z v x=false := by
  induction s with
  | zero=>rfl
  | succ s ih=>rw [Scan.lookup_build_succ,ite_eq_right (by omega),ih (by omega)]

theorem cache_at (inc : Fin H→List (Fin H)) (W : Fin H→Block k→ℕ) (D cap s : ℕ) (sh : s≤k)
    (v : Fin H) (z : ℕ) (x : Block k) :
    atDepth (cache (Scan.build inc W D cap s) v) z x=Scan.lookup (Scan.build inc W D cap s) z v x := by
  by_cases hz : z<k
  · simp [cache,flags,atDepth,hz,actualFlags]
  · rw [beyond inc W D cap s sh v z (by omega) x]
    simp [atDepth,hz]

def incoming (peers : Fin H→List (Option (Fin H))) (v : Fin H) := (peers v).filterMap id

def receive (source : Fin H→Panel k) (q : Option (Fin H)) : Panel k := q.elim 0 source

theorem fold_merge (D d : ℕ) (xs : List (Panel k)) (f : Flags k) :
    xs.foldl (merge D d) (flags f)=flags (fun level x=>if level.val=d then
      f level x || xs.any (fun p=>reach d (d+D) p x) else f level x) := by
  induction xs generalizing f with
  | nil=>simp
  | cons p xs ih=>
    simp only [List.foldl_cons,merge_live,ih,List.any_cons]
    apply congrArg flags
    funext level x
    by_cases hit : level.val=d <;> simp [mergeFlags,hit,Bool.or_assoc]

theorem reach_zero (d z : ℕ) (x : Block k) : reach d z (0:Panel k) x=false := by
  simp [reach,atDepth]

private theorem any_peer (xs : List (Option (Fin H))) (source : Fin H→Panel k) (d z : ℕ) (x : Block k) :
    ((xs.map (receive source)).any (fun p=>reach d z p x)=true) ↔
      ∃v∈xs.filterMap id,∃y,group d y=group d x ∧ atDepth (source v) z y=true := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨p,hp,hit⟩
    obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hp
    cases q with
    | none=>simp [receive,reach_zero] at hit
    | some u=>
      refine ⟨u,List.mem_filterMap.mpr ⟨some u,hq,rfl⟩,?_⟩
      apply of_decide_eq_true
      exact hit
  · rintro ⟨u,hu,hit⟩
    obtain ⟨q,hq,eq⟩:=List.mem_filterMap.mp hu
    change q=some u at eq
    subst q
    refine ⟨_,List.mem_map.mpr ⟨some u,hq,rfl⟩,?_⟩
    exact decide_eq_true hit

/-- The concrete floor-by-floor update uses the genuine old split cache from
the current site, then each pre-stage incoming slot. -/
theorem advance (peers : Fin H→List (Option (Fin H))) (W : Fin H→Block k→ℕ) (D cap : ℕ)
    (a μ : Bits k) (s : ℕ) (sh : s<k) (v : Fin H) (room : ∀x,W v x<2^b) :
    let rows:=Scan.build (incoming peers) (multiplierLoad W a μ) D cap s
    let source:=cache rows
    let d:=k-(s+1)
    ((peers v).map (receive source)).foldl (merge D d)
      (baseUpdate a μ cap d (source v) (counts b (W v)))=
      cache (Scan.build (incoming peers) (multiplierLoad W a μ) D cap (s+1)) v := by
  dsimp only
  let src:=cache (Scan.build (incoming peers) (multiplierLoad W a μ) D cap s)
  let d:=k-(s+1)
  have live : src v≠0 := present_ne_zero _
  change ((peers v).map (receive src)).foldl (merge D d) (baseUpdate a μ cap d (src v) _)=_
  rw [baseUpdate,ite_eq_right live,fold_merge]
  apply congrArg flags
  funext level x
  change _=Scan.lookup (Scan.build (incoming peers) (multiplierLoad W a μ) D cap (s+1)) level.val v x
  rw [Scan.lookup_build_succ]
  by_cases hit : level.val=d
  · simp only [show k-(s+1)=d from rfl,hit,eq_self,ite_true,ownFlag]
    apply Bool.eq_iff_iff.mpr
    rw [Scan.rowValue_spec]
    have weights : Scan.readWeights (fun _ : Unit=>paintIn a μ (counts b (W v))) d () x=
        Scan.readWeights (multiplierLoad W a μ) d v x := by
      simp [Scan.readWeights,paintIn_read a μ W v room]
    simp only [Bool.or_eq_true,decide_eq_true_eq,weights,Scan.weight_sum]
    rw [any_peer (peers v) src d (d+D) x]
    simp only [reach,decide_eq_true_eq,src,cache_at _ _ _ _ _ sh.le,incoming]
    exact or_assoc
  · simp only [show k-(s+1)=d from rfl,hit,ite_false,ownFlag]
    exact cache_at _ _ _ _ _ sh.le _ _ _


end
end Hierarchy.DescentPackedColony

end OAI
