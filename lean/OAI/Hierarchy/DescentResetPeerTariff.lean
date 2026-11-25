import OAI.Hierarchy.DescentResetPeerProgram

namespace OAI
/-! # Exact native row and ROM costs for the zero-width-inclusive peer observation -/
namespace Hierarchy.DescentResetPeerUnionRAM.Program
open DescentSIMDLookup DescentPackedColony DescentSortedRoster DescentFallbackRankRAM
open DescentPackedFlowBatch ProtocolRAM DescentStaticWordColumn
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
noncomputable section
variable {H S D E b M G : ℕ}

def columnWork (E G M U : ℕ) := 42+(E*chunks G M)*(U+8)
def sortWork (slots : ℕ) := 100*(slots+1)^3

private theorem or_work (xs : List Expr) (U : ℕ) (bound : ∀x∈xs,x.work ≤ U) :
    (anyWord xs).work ≤ 1+xs.length*(U+3) := by
  induction xs with
  | nil=>simp [anyWord,Expr.work]
  | cons x xs ih=>
    have hd:=bound x (by simp)
    have tl:=ih (fun e he=>bound e (List.mem_cons_of_mem _ he))
    change x.work+1+(anyWord xs).work+1+1 ≤ _
    rw [List.length_cons,Nat.succ_mul]
    omega

private theorem selector_work (start H S D : ℕ) (old : Bank) (j : Fin (Candidates.count S D)) :
    (Candidates.selector old start H S D j).work ≤ 38 := by
  unfold Candidates.selector
  split
  · dsimp only
    split <;> simp only [Expr.work] <;> decide
  · change 1 ≤ 38
    decide

private theorem column_work (start H S D b M G : ℕ) (old : Bank) (src : Fin E→Fin (chunks G M)→Expr)
    (U : ℕ) (bound : ∀e c,(src e c).work ≤ U) (j : ℕ) :
    ((operands start H S D b M G old src).column (H*S) j).work ≤ columnWork E G M U := by
  let q:=operands start H S D b M G old src
  by_cases live : j < Candidates.count S D
  · let d : Fin (Candidates.count S D):=⟨j,live⟩
    have total:=or_work (List.ofFn (q.evidence d)) (U+5) (by
      intro x hx
      obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hx
      exact Nat.add_le_add_right (bound (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) 5)
    rw [List.length_ofFn, show U+5+3=U+8 by omega] at total
    have x:=selector_work start H S D old d
    simp only [Inputs.column,dite_eq_left live]
    change (anyWord (List.ofFn (q.evidence d))).work+1+1+(Candidates.selector old start H S D d).work+1 ≤ _
    dsimp only [columnWork]
    omega
  · simp only [Inputs.column,dite_eq_right live,Expr.work,columnWork]
    omega

private theorem distinct_work (base H : ℕ) (j : Fin D) (e : Expr) (xs : List (Fin D)) :
    (unlessSeen (field base H j) e (xs.map (field base H))).work=e.work+16*xs.length := by
  induction xs with
  | nil=>simp [unlessSeen]
  | cons x xs ih=>
    change 7+7+1+(unlessSeen (field base H j) e (xs.map (field base H))).work+1=_
    rw [ih,List.length_cons]
    omega

private theorem sum_work (xs : List Expr) (U : ℕ) (bound : ∀e∈xs,e.work ≤ U) :
    (foldSum xs).work ≤ 1+xs.length*(U+1) := by
  induction xs with
  | nil=>simp [foldSum,Expr.work]
  | cons x xs ih=>
    have hd:=bound x (by simp)
    have tl:=ih (fun e he=>bound e (List.mem_cons_of_mem _ he))
    change x.work+(foldSum xs).work+1 ≤ _
    rw [List.length_cons,Nat.succ_mul]
    omega

private theorem count_work (base H : ℕ) (v : Fin D) :
    (calculate (D:=D) (field base H) (field base H v)).work ≤ 1+D*(18+16*D) := by
  have rb (j : Fin D) : (rankBit (field base H) (field base H v) j).work ≤ 17+16*D := by
    rw [rankBit,distinct_work]
    have le : (prior j).length ≤ D := by
      simpa [prior,Finset.length_toList] using (Finset.card_filter_le (s:=Finset.univ) (fun i : Fin D=>i < j))
    change 17+16*(prior j).length ≤ _
    omega
  have a:=sum_work ((Finset.univ : Finset (Fin D)).toList.map (rankBit (field base H) (field base H v)))
    (17+16*D) (by intro e h;obtain ⟨j,_,rfl⟩:=List.mem_map.mp h;exact rb j)
  simpa only [calculate,List.length_map,Finset.length_toList,Finset.card_univ,Fintype.card_fin,
    show 17+16*D+1=18+16*D by omega] using a

theorem select_work (base H D j : ℕ) : (select base H D j).work ≤ sortWork D := by
  let inc:=26+D*(18+16*D)
  have aux (xs : List (Fin D)) : (pick (field base H) (.lit j) H xs).work ≤ 1+xs.length*inc := by
    induction xs with
    | nil=>simp [pick,Expr.work]
    | cons x xs ih=>
      have prev:=count_work base H x
      change (7+1+((calculate (D:=D) (field base H) (field base H x)).work+1+1+1+1)+1+1)+1+7+
        (pick (field base H) (.lit j) H xs).work+1 ≤ _
      rw [List.length_cons,Nat.succ_mul]
      dsimp only [inc] at *
      omega
  refine (aux (List.finRange D)).trans ?_
  simp only [List.length_finRange,inc,sortWork]
  ring_nf
  omega

private theorem pass_names (w base rows pitch n : ℕ) (e : ℕ→Expr) (U : ℕ) (bound : ∀j < n,(e j).work ≤ U) :
    names (ProtocolRAM.program w (passes base rows pitch e 0 n)) ≤ 15+n*(11+4*U) := by
  have aux (start len : ℕ) (hi : start+len ≤ n) :
      names (ProtocolRAM.program w (passes base rows pitch e start len)) ≤ 15+len*(11+4*U) := by
    induction len generalizing start with
    | zero=>simp [passes,ProtocolRAM.program,names_scan,Expr.work]
    | succ len ih=>
      have h:=ih (start+1) (by omega)
      have hd:=bound start (by omega)
      simp only [passes,ProtocolRAM.program,names_seq,Pass.procedure,names_scan,Nat.succ_mul len (11+4*U)]
      omega
  exact aux 0 n (Nat.zero_add n).le

def timeBound (H S D E b M G U : ℕ) :=
  let slots:=Candidates.count S D
  let pitch:=H*S
  ((4+10*Candidates.length H S)+(4+10*Packed.words slots E b M))+
    ((4+slots*(4+pitch*(2*columnWork E G M U+4)))+
        (4+3*(4+pitch*(2*sortWork slots+4))))

def hardwareBound (H S D E b M G U : ℕ) :=
  let slots:=Candidates.count S D
  (15*(Candidates.length H S+1)+15*(Packed.words slots E b M+1))+
    ((15+slots*(11+4*columnWork E G M U))+(15+3*(11+4*sortWork slots)))

theorem prices (start H S D b M G w : ℕ) (old : Bank)
    (test : Fin (Candidates.count S D)→Fin E→Cell b→Bool) (src : Fin E→Fin (chunks G M)→Expr)
    (U : ℕ) (measured : ∀e c,(src e c).work ≤ U) :
    clock start H S D b M G old src ≤ timeBound H S D E b M G U ∧
    names (program w start H S D b M G old test src) ≤ hardwareBound H S D E b M G U := by
  let slots:=Candidates.count S D
  let pitch:=H*S
  let ptr:=scratchAt start H S D E b M
  let q:=operands start H S D b M G old src
  have first (j : ℕ) (_ : j < slots) := column_work start H S D b M G old src U measured j
  have second (j : ℕ) (_ : j < 3) := select_work ptr pitch slots j
  constructor
  · apply Nat.add_le_add_left
    exact Nat.add_le_add
      (tariff ptr pitch (stride pitch) slots (q.column pitch) _ first)
      (tariff (outBase ptr pitch slots) pitch pitch 3 (select ptr pitch slots) _ second)
  · unfold program machine
    simp only [names_seq,names_mount]
    apply Nat.add_le_add_left
    exact Nat.add_le_add
      (pass_names w ptr pitch (stride pitch) slots (q.column pitch) _ first)
      (pass_names w (outBase ptr pitch slots) pitch pitch 3 (select ptr pitch slots) _ second)

end
end Hierarchy.DescentResetPeerUnionRAM.Program

end OAI
