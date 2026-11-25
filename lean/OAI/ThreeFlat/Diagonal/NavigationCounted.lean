import OAI.ThreeFlat.Diagonal.ProgramDirectory
import OAI.ThreeFlat.Diagonal.NavigationBody
import OAI.ThreeFlat.RAM.AdmissionPost
import OAI.ThreeFlat.RAM.CountedAdmission

namespace OAI
/-! # The counted navigation program visits the same rows as the chronological run -/
namespace ThreeFlat.Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure PhysicalStage
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {W : ℕ}

/-- Native procedures in the order of the actual typed stage constructors. -/
def nativeRows (current : Word W) (K : ℕ) : {s : ℕ}→ Program F s→List (Procedure W)
  | _,.done _=>[]
  | _,.shrink s t T _ p=>shrink current K s (2^t) T::nativeRows current K p
  | _,.refresh s _ h pad _ _ _ T _ _ sym rows zero _ _ p=>
    refresh current K s h pad T sym rows zero::nativeRows current K p

def rowProgram (xs : List (Procedure W)) := xs.foldr Procedure.seq skip

theorem compile_rows (cur : Word W) (K : ℕ) {s : ℕ} (P : Program F s) :
    compile cur K P=rowProgram (nativeRows cur K P) := by
  induction P with
  | done => rfl
  | shrink s t T hm tail ih => simp only [compile,nativeRows,rowProgram,List.foldr_cons] at ih ⊢;rw [ih]
  | refresh s t h pad c g C T a b sym row zero conn hh tail ih =>
    simp only [compile,nativeRows,rowProgram,List.foldr_cons] at ih ⊢;rw [ih]

private theorem nativeRows_cast (cur : Word W) (K : ℕ) {s t : ℕ} (P : Program F s) (eq : s=t) :
    nativeRows cur K (eq ▸ P : Program F t)=nativeRows cur K P := by cases eq;rfl

private def shrinkRows (cur : Word W) (K : ℕ) (B : Block F) : ℕ→ℕ→List (Procedure W)
  | 0,_=>[]
  | n+1,i=>shrink cur K (B.exponent i) (2^B.exponent (i+1)) B.shrink::shrinkRows cur K B n (i+1)

private theorem rows_shrinkPrefix (cur : Word W) (K : ℕ) (B : Block F) (n i : ℕ) (P : Program F (B.exponent (i+n))) :
    nativeRows cur K (B.shrinkPrefix n i P)=shrinkRows cur K B n i++nativeRows cur K P := by
  induction n generalizing i with
  | zero => simp [Block.shrinkPrefix,shrinkRows]
  | succ n ih =>
    simp only [Block.shrinkPrefix,nativeRows,shrinkRows,ih,nativeRows_cast,List.cons_append]

theorem rows_prefix (cur : Word W) (K : ℕ) (B : Block F) (P : Program F (B.exponent 0)) :
    nativeRows cur K (B.prefix P)=nativeRows cur K (B.prefix (.done _))++nativeRows cur K P := by
  simp only [Block.prefix,rows_shrinkPrefix,nativeRows_cast,nativeRows,List.append_assoc,List.nil_append,List.cons_append]

theorem rows_repeat (cur : Word W) (K : ℕ) (B : Block F) (n : ℕ) :
    nativeRows cur K (B.repeat n)=(List.replicate n (nativeRows cur K (B.prefix (.done _)))).flatten := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Block.repeat,rows_prefix,ih,List.replicate_succ,List.flatten_cons]

theorem nativeRows_length (cur : Word W) (K : ℕ) {s : ℕ} (P : Program F s) :
    (nativeRows cur K P).length=P.length := by
  induction P with
  | done => rfl
  | shrink s t T hm tail ih => simp only [nativeRows,PhysicalStage.Program.length,List.length_cons,ih]
  | refresh s t h pad c g C T a b sym row zero conn hh tail ih =>
    simp only [nativeRows,PhysicalStage.Program.length,List.length_cons,ih]

theorem repeated_length (cur : Word W) (K : ℕ) (B : Block F) (n : ℕ) :
    (nativeRows cur K (B.repeat n)).length=n*(nativeRows cur K (B.prefix (.done _))).length := by
  induction n with
  | zero => simp [Block.repeat, nativeRows]
  | succ n ih =>
    rw [Block.repeat,rows_prefix,List.length_append,ih,Nat.succ_mul,Nat.add_comm]

private theorem rowIndex_lt {n q l : ℕ} (hq : q < n) (j : Fin l) : q*l+j.val < n*l := by
  have cap := Nat.mul_le_mul_right l (show q+1 ≤ n from hq)
  rw [Nat.succ_mul] at cap
  exact (Nat.add_lt_add_left j.isLt _).trans_le cap

private theorem rowOfBlocks {α : Type*} (rows : List α) (j : Fin rows.length) (n q : ℕ)
    (hq : q < n) : (List.replicate n rows).flatten[q*rows.length+j.val]? = some (rows.get j) := by
  induction n generalizing q with
  | zero => omega
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons]
    cases q with
    | zero =>
      rw [Nat.zero_mul, Nat.zero_add, List.getElem?_append_left j.isLt, List.getElem?_eq_getElem j.isLt]; rfl
    | succ q =>
      rw [Nat.succ_mul, List.getElem?_append_right (by omega),
        show q*rows.length+rows.length+j.val-rows.length = q*rows.length+j.val by omega]
      exact ih q (by omega)

/-- The stage at public address (block, row) is exactly the same program in both lists. -/
theorem repeated_get (cur : Word W) (K : ℕ) (B : Block F) (n q : ℕ) (hq : q<n)
    (j : Fin (nativeRows cur K (B.prefix (.done _))).length) :
    let rows:=nativeRows cur K (B.prefix (.done _))
    (nativeRows cur K (B.repeat n))[q*rows.length+j.val]'(by
      rw [repeated_length]; exact rowIndex_lt hq j)=rows.get j := by
  let rows := nativeRows cur K (B.prefix (.done _))
  have hit : (nativeRows cur K (B.repeat n))[q*rows.length+j.val]? = some (rows.get j) := by
    rw [rows_repeat]
    exact rowOfBlocks rows j n q hq
  exact (List.getElem_of_getElem? hit).choose_spec

/-- Physical state at each row and successful parsing of the first chronological records
of the given raw tape. The loop only modifies the separate counter between passes. -/
structure CountedTimeline (field : FieldCode F W) (counter : Word W) (rows : List (Procedure W)) (n : ℕ) where
  resident : ℕ→Memory W→Prop
  good : ℕ→Prop
  cost : Fin rows.length→ℕ
  seen : ∀ i m,resident i m → good i
  shorten : ∀ i j,i ≤ j → good j → good i
  step : ∀ q,q<n→∀ j : Fin rows.length,∀ m,
    let i := q*rows.length+j.val
    resident i m →
    TickStageSpec.Admission field (rows.get j).block (rows.get j).publicData (fun x=>x=m)
      (fun _=>good (i+1)) (fun _ o=>resident (i+1) o ∧ o counter.val=m counter.val) (cost j)
  decrement : ∀ q,q<n→∀ m,resident (q*rows.length) m → (m counter.val).val=n-q →
    resident (q*rows.length) (writeMemory m counter (m counter.val-1))

namespace CountedTimeline
variable {field : FieldCode F W} {counter : Word W} {rows : List (Procedure W)} {n : ℕ}
variable (T : CountedTimeline field counter rows n)

def perRow : ℕ := ∑ j : Fin rows.length,T.cost j

private theorem segment (q : ℕ) (visiting : q<n) (xs : List (Procedure W)) (j : ℕ)
    (endAt : j+xs.length=rows.length)
    (target : ∀ k : Fin xs.length,xs.get k=rows.get ⟨j+k.val,by omega⟩) :
    let proc := rowProgram xs
    let i := q*rows.length+j
    let stop := q*rows.length+rows.length
    TickStageSpec.Admission field proc.block proc.publicData (T.resident i)
      (fun _=>T.good stop) (fun m o=>T.resident stop o ∧ o counter.val=m counter.val)
      (xs.length*T.perRow+1) := by
  induction xs generalizing j with
  | nil =>
    have e : j=rows.length := by simpa using endAt
    subst j
    let stop := q*rows.length+rows.length
    simp only [List.length_nil,Nat.zero_mul,Nat.zero_add]
    intro p r K M pc reg pub exit installed data state m entry resident
    have step := skip_spec M pc reg pub exit installed data state m entry trivial
    obtain ⟨t,ht,out,outMem,run,atExit,same⟩ := step
    subst outMem
    exact ⟨fun _=>⟨t,ht,out,m,atExit,⟨resident,rfl⟩,run⟩,
      fun bad=>(bad (T.seen stop m resident)).elim⟩
  | cons p xs ih =>
    let l := rows.length
    let i := q*l+j
    have h : j<rows.length := by simp only [List.length_cons] at endAt;omega
    let j' : Fin rows.length := ⟨j,h⟩
    have head : p=rows.get j' := by simpa [j'] using target ⟨0,by simp⟩
    have first : TickStageSpec.Admission field p.block p.publicData (T.resident i)
        (fun _=>T.good (i+1)) (fun m o=>T.resident (i+1) o ∧ o counter.val=m counter.val) T.perRow := by
      rw [head]
      intro N R K M pc reg pub exit installed data state m entry hm
      have size : T.cost j'≤T.perRow := Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ j')
      exact (TickStageSpec.Admission.mono (T.step q visiting j' m hm)
        (pre':=fun x=>x=m)
        (post':=fun _ o=>T.resident (i+1) o ∧ o counter.val=m counter.val) (fun _ e=>e) (fun _ _=>Iff.rfl) (fun _ _ _ _ z=>z) size)
        M pc reg pub exit installed data state m entry rfl
    have last : j+1+xs.length=rows.length := by simp only [List.length_cons] at endAt;omega
    have positions (k : Fin xs.length) : xs.get k=rows.get ⟨j+1+k.val,by omega⟩ := by
      have e := target k.succ
      simpa only [List.get_cons_succ',Fin.val_succ,Nat.add_assoc,Nat.add_comm 1 k.val] using e
    have a : q*rows.length+(j+1)=i+1 := by dsimp [i,l];omega
    let stop := q*rows.length+rows.length
    have tail : TickStageSpec.Admission field (rowProgram xs).block (rowProgram xs).publicData
        (T.resident (i+1)) (fun _=>T.good stop)
        (fun m o=>T.resident stop o ∧ o counter.val=m counter.val) (xs.length*T.perRow+1) := by
      rw [←a]
      exact ih (j+1) last positions
    have later : i+1≤q*rows.length+rows.length := by dsimp [i,l];omega
    apply TickStageSpec.Admission.mono (pre':=T.resident i) (good':=fun _=>T.good stop)
      (post':=fun m o=>T.resident stop o ∧ o counter.val=m counter.val)
      (t':=(xs.length+1)*T.perRow+1)
      (TickStageSpec.admission_seq field p (rowProgram xs) (good:=fun _=>T.good stop) first tail
        (fun _ _ hv=>T.shorten _ _ later hv) (fun _ _ _ _ hop=>⟨hop.1,Iff.rfl⟩))
      (fun _ x=>x) (fun _ _=>Iff.rfl)
    · intro m o _ _ ⟨mid,left,right⟩
      exact ⟨right.1,right.2.trans left.2⟩
    · simp only [Nat.add_mul,Nat.one_mul];omega

theorem block (q : ℕ) (hq : q<n) :
    TickStageSpec.Admission field (rowProgram rows).block (rowProgram rows).publicData
      (T.resident (q*rows.length)) (fun _=>T.good ((q+1)*rows.length))
      (fun m o=>T.resident ((q+1)*rows.length) o ∧ o counter.val=m counter.val)
      (rows.length*T.perRow+1) := by
  intro p r K
  simpa only [Nat.add_zero,Nat.add_mul,Nat.one_mul] using
    (T.segment q hq rows 0 (by simp) (fun k=>by congr 1;apply Fin.ext; simp)
      (p:=p) (r:=r) (K:=K))

end CountedTimeline

/-- The actual counted machine accepts exactly when every chronological record of the
unrolled run parses. On a successful return the final chronological graph and archive
are retained in the same resident relation as the stage witnesses. -/
theorem repeated_admission (field : FieldCode F W) (cur counter : Word W) (K : ℕ) (B : Block F) (n : ℕ)
    (T : CountedTimeline field counter (nativeRows cur K (B.prefix (.done _))) n) :
    let p := repeated cur counter K B
    let rows := nativeRows cur K (B.prefix (.done _))
    TickStageSpec.Admission field p.block p.publicData (fun m=>T.resident 0 m ∧ (m counter.val).val=n)
      (fun _=>T.good (n*rows.length)) (fun _ o=>T.resident (n*rows.length) o)
      (n*(7+(rows.length*T.perRow+1))+4) := by
  let rows := nativeRows cur K (B.prefix (.done _))
  let inv (z : ℕ) (m : Memory W) := z≤n ∧ T.resident ((n-z)*rows.length) m
  let full (_ : ℕ) (_ : Memory W) := T.good (n*rows.length)
  let head (z : ℕ) (_ : Memory W) := T.good ((n-z)*rows.length)
  let cost := rows.length*T.perRow+1
  have body (z : ℕ) (m : Memory W) (hi : inv (z+1) m) (hc : (m counter.val).val=z+1) :
      TickStageSpec.Admission field (rowProgram rows).block (rowProgram rows).publicData
        (fun x=>x=writeMemory m counter (m counter.val-1)) (fun _=>head z m)
        (fun _ o=>(o counter.val).val=z ∧ inv z o ∧ (full z o ↔ full (z+1) m)) cost := by
    have zn := hi.1
    let q := n-(z+1)
    have visiting : q<n := by dsimp [q];omega
    have still : n-q=z+1 := by dsimp [q];omega
    have next : q+1=n-z := by dsimp [q];omega
    have resident := T.decrement q visiting m hi.2 (hc.trans still.symm)
    have word : m counter.val≠0 := by intro eq;simp [eq] at hc
    have dec : (writeMemory m counter (m counter.val-1) counter.val).val=z := by
      have atCounter : writeMemory m counter (m counter.val-1) counter.val=m counter.val-1:=by simp [writeMemory]
      rw [atCounter,Fin.val_sub_one_of_ne_zero word,hc]; omega
    apply TickStageSpec.Admission.mono (T.block q visiting)
    · intro x eq;simpa only [eq] using resident
    · intro _ _
      change T.good ((n-z)*rows.length) ↔ T.good ((q+1)*rows.length)
      rw [next]
    · intro x o eq _ out
      refine ⟨?_,⟨by omega,?_⟩,Iff.rfl⟩
      · rw [out.2,eq];exact dec
      · simpa only [next] using out.1
    · exact le_rfl
  let machine := (rowProgram rows).counted counter
  have all : TickStageSpec.Admission field machine.block machine.publicData
      (fun m=>inv n m ∧ (m counter.val).val=n) (full n) (fun _ o=>inv 0 o)
      (n*(7+cost)+4) :=
    TickStageSpec.counted field (rowProgram rows) counter cost inv full head body
      (fun z _ _ hg=>T.shorten _ _ (Nat.mul_le_mul_right rows.length (Nat.sub_le n z)) hg)
      (fun m hm=>by simpa [full] using T.seen _ m hm.2) n
  let contract (code : Procedure W) : Prop :=TickStageSpec.Admission field code.block code.publicData
    (fun m=>T.resident 0 m ∧ (m counter.val).val=n) (full n)
    (fun _ o=>T.resident (n*rows.length) o) (n*(7+cost)+4)
  have machineEq : repeated cur counter K B=machine :=
    congrArg (fun code : Procedure W=>code.counted counter) (compile_rows cur K (B.prefix (.done _)))
  change contract (repeated cur counter K B)
  rw [machineEq]
  unfold contract
  apply TickStageSpec.Admission.mono all
  · intro m hm
    exact ⟨⟨le_rfl,by simpa using hm.1⟩,hm.2⟩
  · intro _ _;exact Iff.rfl
  · intro _ _ _ _ post
    simpa using post.2
  · exact le_rfl

end
end ThreeFlat.Diagonal.NavigationPass

end OAI
