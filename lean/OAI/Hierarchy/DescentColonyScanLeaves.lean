import OAI.Hierarchy.DescentColonyScan
import OAI.Hierarchy.DescentColonyLeaves

namespace OAI
/-! # Enumerating the original colony leaves from the cached split bits -/

namespace Hierarchy.DescentColonies.Scan
open scoped BigOperators Classical
variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- Scan increasing depths until the first unsplit interval. The second
component counts the actual number of buffered Boolean lookups. -/
def seek (get : ℕ → Bool) : ℕ → ℕ → ℕ × ℕ
  | 0,d => (d,0)
  | rem+1,d => if get d then let p := seek get rem (d+1); (p.1,p.2+1) else (d,1)

theorem seek_work (get : ℕ → Bool) (rem d : ℕ) : (seek get rem d).2≤rem := by
  induction rem generalizing d with
  | zero => rfl
  | succ rem ih =>
    simp only [seek]
    split
    · exact Nat.succ_le_succ (ih _)
    · omega

private theorem seek_first (get : ℕ → Bool) (rem d goal : ℕ) (lo : d≤goal) (hi : goal≤d+rem)
    (ones : ∀j,d≤j → j<goal → get j=true) (off : get goal=false) :
    (seek get rem d).1=goal := by
  induction rem generalizing d with
  | zero => simp [seek]; omega
  | succ rem ih =>
    by_cases atGoal : d=goal
    · subst d
      simp [seek,off]
    · simp only [seek,ones d le_rfl (by omega),ite_true]
      exact ih (d+1) (by omega) (by omega) (fun j hj before => ones j (by omega) before)

noncomputable def leafDepth (rows : Buffer V k) (v : V) (x : Block k) :=
  (seek (fun d => lookup rows d v x) k 0).1

omit [DecidableEq V] in
theorem leafDepth_le (rows : Buffer V k) (v : V) (x : Block k) : leafDepth rows v x ≤ k := by
  have walk (f : ℕ → Bool) (n d : ℕ) : (seek f n d).1 ≤ d+n := by
    induction n generalizing d with
    | zero => simp [seek]
    | succ n ih =>
      have next := ih (d+1)
      simp only [seek]
      split <;> simp only <;> omega
  simpa [leafDepth] using walk (fun d=>lookup rows d v x) k 0

omit [DecidableEq V] in
theorem leafDepth_eq (incoming : V → List V) (adj : V → V → Prop)
    (incoming_spec : ∀w v,w∈incoming v ↔ adj w v) (load : V → Block k → ℕ)
    {D : ℕ} (hD : 0<D) (a B : ℕ) (limit : ∀v x,load v x≤B) (v : V) (x : Block k) :
    leafDepth (build incoming load D (2^a*B) k) v x=depth load adj D a B limit v x := by
  have bound (z : V) (i : Block k) : load z i≤2^a*B :=
    (limit z i).trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
  have marks (d : ℕ) := lookup_split incoming adj incoming_spec load hD bound d v x
  apply seek_first _ _ _ _ (Nat.zero_le _) (by simpa using (depth_le load adj D a B limit v x).trans (Nat.sub_le _ _))
  · exact fun j _ before => (marks j).mpr (earlier_split load adj D a B limit v x before)
  · apply Bool.eq_false_iff.mpr
    intro bit
    have done : ¬Split load adj D (2^a*B) v (depth load adj D a B limit v x) x := by
      unfold depth
      exact Nat.find_spec (p:=fun j => ¬Split load adj D (2^a*B) v j x)
        ⟨k-a,fun h => (Nat.lt_irrefl _) (split_shallow load adj D a B limit h)⟩
    exact done ((marks _).mp bit)

noncomputable def siteKeys (rows : Buffer V k) (v : V) : Finset (ℕ × ℕ) :=
  Finset.univ.image (fun x : Block k => let d:=leafDepth rows v x; (d,group d x))

/-- A key lookup counts exactly the pairs inspected before the first match. -/
def containsKey (key : ℕ × ℕ) : List (ℕ × ℕ) → Bool × ℕ
  | [] => (false,0)
  | a::xs => if a=key then (true,1) else
      let found := containsKey key xs
      (found.1,found.2+1)

private theorem containsKey_spec (key : ℕ × ℕ) (xs : List (ℕ×ℕ)) :
    ((containsKey key xs).1=true ↔ key∈xs) ∧ (containsKey key xs).2≤xs.length := by
  induction xs with
  | nil => simp [containsKey]
  | cons a xs ih =>
    by_cases hit : a=key
    · simp [containsKey,hit]
    · simp [containsKey,hit,Ne.symm hit,ih.1,ih.2]

/-- Compute the number of distinct local keys and its actual comparison cost. -/
def uniqueIDs : List (ℕ × ℕ) → ℕ × ℕ
  | [] => (0,0)
  | a::xs =>
    let tail := uniqueIDs xs
    let seen := containsKey a xs
    (if seen.1 then tail.1 else tail.1+1,tail.2+seen.2)

private theorem uniqueIDs_spec (xs : List (ℕ×ℕ)) :
    (uniqueIDs xs).1=xs.toFinset.card ∧ (uniqueIDs xs).2≤xs.length^2 := by
  induction xs with
  | nil => simp [uniqueIDs]
  | cons a xs ih =>
    have found := containsKey_spec a xs
    constructor
    · by_cases yes : a∈xs
      · simp [uniqueIDs,found.1.mpr yes,ih.1,yes]
      · have absent := Bool.eq_false_iff.mpr (fun h=>yes (found.1.mp h))
        simp [uniqueIDs,absent,yes,ih.1]
    · change (uniqueIDs xs).2+(containsKey a xs).2≤(xs.length+1)^2
      nlinarith only [ih.2,found.2]

noncomputable def keyList (rows : Buffer V k) (v : V) :=
  List.ofFn (fun x : Block k => let d:=leafDepth rows v x; (d,group d x))

omit [DecidableEq V] in
private theorem keyList_set (rows : Buffer V k) (v : V) :
    (keyList rows v).toFinset=siteKeys rows v := by
  ext p
  simp [keyList,siteKeys,List.mem_ofFn]

/-- The score is summed locally over sites. Removing duplicates only compares
pairs of depth and interval IDs at the same position. -/
noncomputable def leafScore (incoming : V → List V) (load : V → Block k → ℕ) (D cap : ℕ) :=
  let rows := build incoming load D cap k
  ∑v,(uniqueIDs (keyList rows v)).1

omit [DecidableEq V] in
theorem leafScore_siteKeys (incoming : V → List V) (load : V → Block k → ℕ) (D cap : ℕ) :
    leafScore incoming load D cap = ∑v,(siteKeys (build incoming load D cap k) v).card := by
  simp only [leafScore,(uniqueIDs_spec _).1,keyList_set]

theorem leafScore_eq (incoming : V → List V) (adj : V → V → Prop)
    (incoming_spec : ∀w v,w∈incoming v ↔ adj w v) (load : V → Block k → ℕ)
    {D : ℕ} (hD : 0<D) (a B : ℕ) (limit : ∀v x,load v x≤B) :
    leafScore incoming load D (2^a*B)=(leaves load adj D a B limit).card := by
  classical
  let rows := build incoming load D (2^a*B) k
  let S := fun v => (siteKeys rows v).image (fun p => (v,p))
  have enumerate : leaves load adj D a B limit=Finset.univ.biUnion S := by
    unfold leaves
    apply congrArg (Finset.univ.biUnion ·)
    funext v
    simp only [S,siteKeys,Finset.image_image,Function.comp_def,rows,leafDepth_eq incoming adj incoming_spec load hD a B limit]
  have distinct : ((Finset.univ : Finset V) : Set V).PairwiseDisjoint S := by
    intro v _ w _ ne
    apply Finset.disjoint_left.mpr
    intro t member₁ member₂
    obtain ⟨x,_,px⟩ := Finset.mem_image.mp member₁
    obtain ⟨y,_,py⟩ := Finset.mem_image.mp member₂
    exact ne (congrArg Prod.fst (px.trans py.symm))
  rw [enumerate,Finset.card_biUnion distinct]
  simp only [leafScore,(uniqueIDs_spec _).1,keyList_set]
  apply Finset.sum_congr rfl
  intro v _
  apply Eq.symm
  apply Finset.card_image_of_injective
  exact fun _ _ he => congrArg Prod.snd he

/-- Here the scan considers each old block once at each site, makes at most
k buffered lookups to identify its leaf, and compares its ID to at most the
2^k local IDs to remove duplicates. -/
noncomputable def leafVisits (rows : Buffer V k) : ℕ :=
  ∑ v, ((∑ x : Block k, (seek (fun d=>lookup rows d v x) k 0).2) + (uniqueIDs (keyList rows v)).2)

omit [DecidableEq V] in
theorem leafVisits_bound (rows : Buffer V k) :
    leafVisits rows≤Fintype.card V*(2^k)*(k+2^k) := by
  unfold leafVisits
  have each (v : V) :
      (∑ x : Block k,(seek (fun d=>lookup rows d v x) k 0).2)+(uniqueIDs (keyList rows v)).2≤
        2^k*(k+2^k) := by
    have scans := Finset.sum_le_sum (s:=Finset.univ) (fun x _ => seek_work (fun d=>lookup rows d v x) k 0)
    have keys := (uniqueIDs_spec (keyList rows v)).2
    have len : (keyList rows v).length=2^k := List.length_ofFn
    rw [len] at keys
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,Block] at scans
    nlinarith only [scans,keys]
  simpa [Nat.mul_assoc] using Finset.sum_le_sum (s:=Finset.univ) (fun v _ => each v)

end Hierarchy.DescentColonies.Scan

end OAI
