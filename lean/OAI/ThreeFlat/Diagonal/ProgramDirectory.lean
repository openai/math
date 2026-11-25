import OAI.ThreeFlat.Diagonal.ProgramDirectoryData

namespace OAI
/-! # Branch-independent raw histogram lengths of the actual binary program -/

namespace ThreeFlat.Diagonal.PhysicalStage.Program

open NavigationDirectory CompressorPacking.Native.ShrinkStage
open scoped Classical
noncomputable section
variable {F : Type} [Field F]

theorem shrink_positions (s t r v : ℕ) :
    let d := 2^s
    let x : Dimensions := ⟨v,d,2*d+1,2^CompressorPacking.tagBits d,2^r,2^t⟩
    x.originalSites = v*2^(shrinkCharge s+r) ∧ x.outputSites*4 ≤ x.originalSites := by
  dsimp only [Dimensions.originalSites,Dimensions.originalLanes,Dimensions.outputSites,Dimensions.newBase]
  constructor
  · simp only [shrinkCharge,pow_add]
    ac_rfl
  · have hc : 4 ≤ 2^(2*2^s+1) := by
      have h : 2≤2*2^s+1 := by have := Nat.two_pow_pos s; omega
      exact Nat.pow_le_pow_right (by decide : 0<2) h
    have hd : 1≤2^s := Nat.two_pow_pos s
    calc
      _ ≤ v*(2^r*2^CompressorPacking.tagBits (2^s)*2^s*2^(2*2^s+1)) := by
        have h := Nat.mul_le_mul hd hc
        have m := Nat.mul_le_mul_left (v*(2^CompressorPacking.tagBits (2^s))*2^r) h
        simpa only [Nat.one_mul,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using m

theorem refresh_positions (s r v h pad : ℕ) :
    (RefreshStageLayout.counts v (2^s) (2^r) h pad).nodes=v*2^(s+r) ∧
      (v*2^s)*2^r=v*2^(s+r) := by simp [RefreshStageLayout.counts,pow_add,Nat.mul_assoc]

/-- The two per-stage allocation coefficients depend on the fixed degrees alone. -/
def shrinkAllocation (s t : ℕ) :=
  let d := 2^s
  2+22*(8*d+6*2^t+6)+(7+6*(8*d^2*2^(2*d+1))+8*2^t)+2

def allocationFactors : {s : ℕ} → Program F s → List ℕ
  | _, .done _ => []
  | _, .shrink s t _ _ p => shrinkAllocation s t :: allocationFactors p
  | _, .refresh _ _ h pad _ _ _ _ _ _ _ _ _ _ _ p => (21+h+15*(1+h+pad)) :: allocationFactors p

theorem allocation_words {s : ℕ} (P : Program F s) (K : ℕ) (bound : ∀ a∈P.allocationFactors,a≤K)
    (rem v : ℕ) :
    ((P.directory rem v).map Stage.heapWords).sum≤P.length*K*(1+v*2^(P.charge+rem)) := by
  induction P generalizing v with
  | done s => simp [directory,length]
  | shrink s t T small tail ih =>
    let d := 2^s
    let tag := 2^CompressorPacking.tagBits d
    let x : Dimensions := ⟨v,d,2*d+1,tag,2^(tail.charge+rem),2^t⟩
    have areas := shrink_positions s t (tail.charge+rem) v
    have orig : x.originalSites=v*2^(shrinkCharge s+tail.charge+rem) := by
      simpa only [Nat.add_assoc] using areas.1
    have decrease : x.outputSites≤x.originalSites := by have sub : x.outputSites*4≤x.originalSites := areas.2; omega
    have out : (v*tag)*2^(tail.charge+rem)≤x.originalSites := decrease
    have cap : shrinkAllocation s t≤K := bound _ List.mem_cons_self
    have h0 := shrink_heap_le x (Nat.two_pow_pos _) (Nat.two_pow_pos _) (Nat.two_pow_pos _) decrease
    have cell : (Stage.shrink x).heapWords≤K*(1+x.originalSites) := by
      apply h0.trans
      apply le_trans _ (Nat.mul_le_mul_right _ cap)
      let pre := 22*(8*d+6*2^t+6)
      let post := 7+6*x.localCapacity+8*2^t
      change 2+(pre+post+2)*x.originalSites ≤ (2+pre+post+2)*(1+x.originalSites)
      rw [Nat.mul_add, Nat.mul_one]
      exact Nat.add_le_add (by omega) (Nat.mul_le_mul_right _ (by omega))
    have tailBound := ih (fun a ha=>bound a (List.mem_cons_of_mem _ ha)) (v*tag)
    change (Stage.shrink x).heapWords+_ ≤ (tail.length+1)*K*(1+v*2^(shrinkCharge s+tail.charge+rem))
    rw [←orig,Nat.add_mul,Nat.one_mul,Nat.add_mul]
    exact (Nat.add_le_add cell (tailBound.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left out 1)))).trans_eq (Nat.add_comm ..)
  | refresh s t h pad c γ C T hm hh sym rows zero conn degree tail ih =>
    let n := v*2^s*2^(tail.charge+rem)
    have orig : n=v*2^(s+tail.charge+rem) := by simp only [n,pow_add]; ring
    have cap : 21+h+15*(1+h+pad)≤K := bound _ List.mem_cons_self
    have h0 := refresh_heap_le v (2^s) (2^(tail.charge+rem)) h pad (Nat.two_pow_pos _) (Nat.two_pow_pos _)
    have cell : (Stage.refresh v (2^s) (2^(tail.charge+rem)) h pad).heapWords ≤ K*(1+n) :=
      h0.trans (Nat.mul_le_mul cap (by omega))
    have tailBound := ih (fun a ha=>bound a (List.mem_cons_of_mem _ ha)) (v*2^s)
    change (Stage.refresh v (2^s) (2^(tail.charge+rem)) h pad).heapWords+_ ≤
      (tail.length+1)*K*(1+v*2^(s+tail.charge+rem))
    rw [←orig,Nat.add_mul,Nat.one_mul,Nat.add_mul]
    exact (Nat.add_le_add cell tailBound).trans_eq (Nat.add_comm ..)

theorem allocation_cast {s t : ℕ} (e : s=t) (P : Program F s) :
    allocationFactors (e ▸ P : Program F t)=P.allocationFactors := by cases e; rfl

end
end ThreeFlat.Diagonal.PhysicalStage.Program

namespace ThreeFlat.Diagonal.PhysicalStage.Block

variable {F : Type} [Field F]
noncomputable section

def shrinkAllocations (B : Block F) : ℕ→ℕ→List ℕ
  | 0,_ => []
  | n+1,i => Program.shrinkAllocation (B.exponent i) (B.exponent (i+1)) :: B.shrinkAllocations n (i+1)

def allocations (B : Block F) :=
  B.shrinkAllocations B.levels 0 ++ [21+B.h+15*(1+B.h+B.pad)]

theorem allocation_shrinkPrefix (B : Block F) (n i : ℕ) (P : Program F (B.exponent (i+n))) :
    (B.shrinkPrefix n i P).allocationFactors=B.shrinkAllocations n i++P.allocationFactors := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp only [shrinkPrefix,Program.allocationFactors,shrinkAllocations,
      ih,Program.allocation_cast,List.cons_append]

theorem allocation_prefix (B : Block F) (P : Program F (B.exponent 0)) :
    (B.prefix P).allocationFactors=B.allocations++P.allocationFactors := by
  simp only [Block.«prefix»,allocation_shrinkPrefix,Program.allocation_cast,Program.allocationFactors,allocations,
    List.append_assoc,List.singleton_append]

theorem allocation_bound (B : Block F) (n a : ℕ) (ha : a∈(B.repeat n).allocationFactors) :
    a≤B.allocations.sum := by
  have mem : a∈B.allocations := by
    induction n with
    | zero => simp [Block.«repeat»,Program.allocationFactors] at ha
    | succ n ih =>
      rw [Block.«repeat»,B.allocation_prefix,List.mem_append] at ha
      exact ha.elim id ih
  generalize B.allocations=l at *
  induction l with
  | nil => simp at mem
  | cons b bs ih =>
    rcases List.mem_cons.mp mem with h | h
    · subst b; simp
    · have := ih h; simp; omega

theorem heap_usage (B : Block F) (n rem v K : ℕ) (c : NavigationDirectory.Cursor) :
    (NavigationDirectory.finish K ((B.repeat n).directory rem v) c).heap ≤
      c.heap+(B.repeat n).length*B.allocations.sum*(1+v*2^((B.repeat n).charge+rem)) := by
  rw [NavigationDirectory.heap_finish]
  exact Nat.add_le_add_left ((B.repeat n).allocation_words B.allocations.sum (B.allocation_bound n) rem v) _

private theorem directory_reindex {a b : ℕ} (eq : a=b) (P : Program F a) (rem v : ℕ) :
    (eq ▸ P : Program F b).directory rem v=P.directory rem v := by cases eq;rfl

private def IssuedDegree (B : Block F) : NavigationDirectory.Stage→Prop
  | .shrink x => ∃ i : Fin B.levels,x.oldDegree=2^B.exponent i.val
  | .refresh _ m _ _ _ => m=2^B.exponent B.levels

private theorem degree_shrinkPrefix (B : Block F) (n i : ℕ) (P : Program F (B.exponent (i+n)))
    (limit : i+n≤B.levels) (rem : ℕ)
    (tail : ∀ v q,q∈P.directory rem v→IssuedDegree B q)
    (v : ℕ) (q : NavigationDirectory.Stage) (member : q∈(B.shrinkPrefix n i P).directory rem v) :
    IssuedDegree B q := by
  induction n generalizing i v with
  | zero => exact tail v q member
  | succ n ih =>
    simp only [shrinkPrefix,Program.directory,List.mem_cons] at member
    rcases member with head|rest
    · subst q
      exact ⟨⟨i,by omega⟩,rfl⟩
    · apply ih (i+1) _ (by omega) _ _ rest
      intro base stage h
      rw [directory_reindex] at h
      exact tail base stage h

/-- Each native stage record selects one of the fixed block's actual degree-indexed families. -/
theorem directory_family_degree (B : Block F) (n rem oldBase : ℕ) (q : NavigationDirectory.Stage)
    (member : q∈(B.repeat n).directory rem oldBase) :
    match q with
    | .shrink x => ∃ i : Fin B.levels,x.oldDegree=2^B.exponent i.val
    | .refresh _ m _ _ _ => m=2^B.exponent B.levels := by
  suffices deg : IssuedDegree B q by cases q <;> exact deg
  induction n generalizing oldBase q with
  | zero => simp [Block.«repeat»,Program.directory] at member
  | succ n ih =>
    simp only [Block.«repeat»,Block.«prefix»] at member
    apply degree_shrinkPrefix B B.levels 0 _ (by omega) rem _ oldBase q member
    intro v op h
    rw [directory_reindex] at h
    simp only [Program.directory,List.mem_cons] at h
    rcases h with head|rest
    · subst op;rfl
    · exact ih _ _ rest

end
end ThreeFlat.Diagonal.PhysicalStage.Block

end OAI
