import OAI.ThreeFlat.Diagonal.ProgramDirectory
import OAI.ThreeFlat.Diagonal.NavigationArchiveFields
import OAI.ThreeFlat.Diagonal.NavigationStageBounds

namespace OAI
/-! # Uniform physical loop limits for the repeated stage directory -/

namespace ThreeFlat.Diagonal.NavigationPass
open CompressorPacking CompressorPacking.Native PhysicalStage NavigationDirectory
open scoped BigOperators Classical
noncomputable section
variable {F : Type} [Field F]

def maxRows (f : Stage → ℕ) (initial : ℕ) : List Stage → ℕ :=
  List.foldr (fun x n=>max (f x) n) initial

/-- All three record-generator loop bounds are sensitive only to the local degree. -/
def extent (i : Fin 3) (s : Stage) := (![childArity s,stageHalves s,stageMotifs s] : Fin 3→ℕ) i

def Program.extents (i : Fin 3) : {s : ℕ}→ Program F s→List ℕ
  | _,.done _=>[]
  | _,.shrink s t _ _ p =>
    extent i (.shrink ⟨0,2^s,2*(2^s)+1,0,0,2^t⟩)::Program.extents i p
  | _,.refresh _ _ h pad _ _ _ _ _ _ _ _ _ _ _ p => extent i (.refresh 0 0 0 h pad)::Program.extents i p

private theorem extents_eq {s : ℕ} (p : Program F s) (r v : ℕ) (i : Fin 3) :
    (p.directory r v).map (extent i)=Program.extents i p := by
  induction p generalizing v with
  | done => rfl
  | shrink s t T h tail ih =>
    simp only [PhysicalStage.Program.directory,Program.extents,List.map_cons,ih]
    fin_cases i <;> rfl
  | refresh s t h pad c C H T a b sy row zero hc ht tail ih =>
    simp only [PhysicalStage.Program.directory,Program.extents,List.map_cons,ih]
    fin_cases i <;> rfl

private theorem extents_cast {s t : ℕ} (p : Program F s) (e : s=t) (i : Fin 3) :
    Program.extents i (e ▸ p : Program F t)=Program.extents i p := by cases e;rfl

private def shrinkExtents (B : Block F) (i : Fin 3) : ℕ→ℕ→List ℕ
  | 0,_=>[]
  | n+1,j =>
    let d := 2^B.exponent j
    extent i (.shrink ⟨0,d,2*d+1,0,0,2^B.exponent (j+1)⟩)::shrinkExtents B i n (j+1)

private theorem extents_shrink (B : Block F) (i : Fin 3) (n j : ℕ) (p : Program F (B.exponent (j+n))) :
    Program.extents i (B.shrinkPrefix n j p)=shrinkExtents B i n j++Program.extents i p := by
  induction n generalizing j with
  | zero => simp [Block.shrinkPrefix,shrinkExtents]
  | succ n ih =>
    simp only [Block.shrinkPrefix,Program.extents,shrinkExtents,ih,extents_cast,List.cons_append]

private theorem extents_prefix (B : Block F) (i : Fin 3) (p : Program F (B.exponent 0)) :
    Program.extents i (B.prefix p)=Program.extents i (B.prefix (.done _))++Program.extents i p := by
  simp only [Block.prefix,extents_shrink,extents_cast,Program.extents,List.append_assoc,List.nil_append,List.cons_append]

private theorem extent_mem (B : Block F) (n : ℕ) (i : Fin 3) :
    ∀ x∈Program.extents i (B.repeat n),x∈Program.extents i (B.prefix (.done _)) := by
  induction n with
  | zero => simp [Block.repeat,Program.extents]
  | succ n ih =>
    intro x hx
    rw [Block.repeat,extents_prefix,List.mem_append] at hx
    exact hx.elim id (ih x)

def directoryCap (B : Block F) :=
  2*2^(B.exponent 0)+(Finset.univ : Finset (Fin 3)).sum (fun i=>(Program.extents i (B.prefix (.done _))).sum)

theorem directory_cap (B : Block F) (n r v : ℕ) (i : Fin 3) (seed : ℕ) (h : seed≤2*2^(B.exponent 0)) :
    maxRows (extent i) seed ((B.repeat n).directory r v)≤directoryCap B := by
  have initial : seed≤directoryCap B := by unfold directoryCap;omega
  have bound (x : ℕ) (hx : x∈Program.extents i (B.prefix (.done _))) : x≤directoryCap B := by
    have member (ys : List ℕ) : ∀ n∈ys,n≤ys.sum := by
      induction ys with
      | nil => simp
      | cons a ys ih =>
        intro n mem
        simp only [List.mem_cons] at mem
        simp only [List.sum_cons]
        obtain rfl | hm := mem
        · omega
        · have := ih n hm;omega
    have z := member _ _ hx
    have v := Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
      (f:=fun j:Fin 3=>(Program.extents j (B.prefix (.done _))).sum)
    unfold directoryCap;omega
  let block := (B.repeat n).directory r v
  have all (s : Stage) (mem : s∈block) : extent i s≤directoryCap B := by
    have he := List.mem_map_of_mem (f:=extent i) mem
    rw [extents_eq] at he
    exact bound _ (extent_mem B n i _ he)
  change maxRows (extent i) seed block≤directoryCap B
  have bounded (xs : List Stage) (members : ∀x∈xs,extent i x≤directoryCap B) :
      maxRows (extent i) seed xs≤directoryCap B := by
    induction xs with
    | nil=>exact initial
    | cons hd tl ih=>
      exact max_le (members hd List.mem_cons_self) (ih fun x hx=>members x (List.mem_cons_of_mem hd hx))
  exact bounded block all

/-- Every actual stage lookup uses the same block-dependent finite cap. -/
theorem directory_member_cap (B : Block F) (n rem v : ℕ) (op : Stage)
    (hit : op ∈ (B.repeat n).directory rem v) :
    childArity op ≤ directoryCap B ∧ stageHalves op ≤ directoryCap B ∧ stageMotifs op ≤ directoryCap B := by
  have occurs (f : Stage → ℕ) (z : ℕ) (ops : List Stage) (h : op∈ops) : f op ≤ maxRows f z ops := by
    induction ops with
    | nil => simp at h
    | cons a as ih =>
      rcases List.mem_cons.mp h with rfl|tail
      · exact le_max_left ..
      · exact (ih tail).trans (le_max_right ..)
  have each (k : Fin 3) : extent k op≤directoryCap B := (occurs _ 0 _ hit).trans
    (directory_cap B n rem v k 0 (Nat.zero_le _))
  exact ⟨each 0,each 1,each 2⟩

end
end ThreeFlat.Diagonal.NavigationPass

end OAI
