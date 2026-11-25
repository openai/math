import OAI.Hierarchy.DescentTerminalPointerGather

namespace OAI
/-! # The absolute preceding stage pages read by each terminal pointer pass -/
namespace Hierarchy.DescentTerminalPointerDigits
open DescentSIMDLookup ProtocolRAM DescentOperandStateBanks Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

namespace Gather
variable {blocks H N A cap L w b d origin : ℕ}

/-- A group of reads is either shared by all hosts or indexed by the physical
host within the current block. These are word locations from the prior runs. -/
inductive Address
  | shared (atWord : ℕ)
  | hosts (bank : Bank)

def Address.expr : Address→ Expr
  | .shared atWord=>.lookup ⟨atWord,0⟩ (.lit 0)
  | .hosts B=>.lookup B .row

def Address.atHost (a : Address) (h : Fin H) : ℕ :=
  match a with
  | .shared i=>i
  | .hosts B=>B.base+h.val

def Address.Fits (origin H w : ℕ) : Address→ Prop
  | .shared i=>(⟨i,0⟩ : Bank).Fits w origin
  | .hosts B=>B.Fits w origin ∧ H≤B.size

theorem Address.below (a:Address) (ok:a.Fits origin H w) (h:Fin H) : a.atHost h<origin := by
  cases a with
  | shared i =>
    change (⟨i,0⟩:Bank).Fits w origin at ok
    have end_:=ok.2.2
    change i+2^0≤origin at end_
    change i<origin
    omega
  | hosts bank =>
    exact (Nat.add_lt_add_left (h.isLt.trans_le ok.2) _).trans_le ok.1.2.2

theorem Address.room (a : Address) (ok : a.Fits origin H w) : a.expr.Fits w origin := by
  cases a with
  | shared i=>exact ⟨ok,trivial⟩
  | hosts B=>exact ⟨ok.1,trivial⟩

theorem Address.read (a : Address) (ok : a.Fits origin H w) (mem : Memory w) (h : Fin H) :
    a.expr.eval mem (h.val:Word w)=mem (a.atHost h) := by
  cases a with
  | shared i=>simp [expr,atHost,Expr.eval,Bank.read,Bank.size]
  | hosts B=>exact DescentPackedZip.bank_read B mem (h.isLt.trans_le ok.2) ok.1

structure Pages (blocks cap A : ℕ) where
  population : Fin blocks→ Bank
  matrix : ℕ
  frozen : Bank
  arity : Fin blocks→ Bank
  pointers : Fin 4→ Fin A→ Fin blocks→ Bank
  signed : Fin (2*cap)→ Fin blocks→ Bank

def Pages.address (s : Pages blocks cap A) (c : Fin (columns cap N A)) (x : Fin blocks) : Address :=
  if c.val=0 then .hosts (s.population x)
  else if c.val=1 then .shared s.matrix
  else if c.val=2 then .hosts s.frozen
  else if count : c.val<3+N then .hosts (s.arity x)
  else if below : c.val<3+N+4*(N*A) then
    let z:Fin (4*(N*A)):=⟨c.val-(3+N),by omega⟩
    let fi:Fin 4×Fin (N*A):=finProdFinEquiv.symm z
    let uj:Fin N×Fin A:=finProdFinEquiv.symm fi.2
    .hosts (s.pointers fi.1 uj.2 x)
  else .hosts (s.signed ⟨c.val-(3+N+4*(N*A)),by have lim:=c.isLt;unfold columns at lim;omega⟩ x)

theorem Pages.fixed (s : Pages blocks cap A) (x : Fin blocks) :
    s.address (N:=N) ncol x=.hosts (s.population x) ∧ s.address (N:=N) mcol x=.shared s.matrix ∧
      s.address (N:=N) fcol x=.hosts s.frozen := by simp [address,ncol,mcol,fcol]

theorem Pages.node (s : Pages blocks cap A) (x : Fin blocks) (u : Fin N) :
    s.address (acol u) x=.hosts (s.arity x) := by
  have small:=u.isLt
  simp [address,acol,show 3+u.val≠1 by omega,show 3+u.val≠2 by omega,
    show 3+u.val<3+N by omega]

theorem Pages.pointer (s : Pages blocks cap A) (x : Fin blocks) (f : Fin 4) (i : Fin (N*A)) :
    s.address (pcol f i) x=.hosts (s.pointers f ((finProdFinEquiv (m:=N) (n:=A)).symm i).2 x) := by
  let z:=finProdFinEquiv (f,i)
  have size:=z.isLt
  have close : 3+N+z.val<3+N+4*(N*A):=by omega
  simp only [address,pcol]
  change (if 3+N+z.val=0 then _ else if 3+N+z.val=1 then _ else if 3+N+z.val=2 then _
    else if mid:3+N+z.val<3+N then _ else if hi:3+N+z.val<3+N+4*(N*A) then _ else _)=_
  simp only [show 3+N+z.val≠0 by omega,show 3+N+z.val≠1 by omega,show 3+N+z.val≠2 by omega,
    Nat.not_lt_of_ge (Nat.le_add_right _ _),ite_false,dite_eq_left close,Nat.add_sub_cancel_left]
  exact congrArg (fun p : Fin 4×Fin (N*A)=>Address.hosts (s.pointers p.1 (finProdFinEquiv.symm p.2).2 x))
    ((finProdFinEquiv (m:=4) (n:=N*A)).symm_apply_apply (f,i))

theorem Pages.port (s : Pages blocks cap A) (x : Fin blocks) (j : Fin (2*cap)) :
    s.address (N:=N) (scol j) x=.hosts (s.signed j x) := by
  let t:=3+N+4*(N*A)+j.val
  have hi:t≥3+N+4*(N*A):=Nat.le_add_right _ _
  simp only [address,scol]
  change (if t=0 then _ else if t=1 then _ else if t=2 then _ else if mid:t<3+N then _
    else if z:t<3+N+4*(N*A) then _ else _)=_
  rw [ite_eq_right (show t≠0 by omega),ite_eq_right (show t≠1 by omega),ite_eq_right (show t≠2 by omega),
    dite_eq_right (show ¬t<3+N by omega),dite_eq_right (Nat.not_lt_of_ge hi)]
  exact congrArg (fun b : Fin (2*cap)=>Address.hosts (s.signed b x))
    (Fin.ext (Nat.add_sub_cancel_left (3+N+4*(N*A)) j.val))

def flattened (chart : Fin L→ Fin blocks→ Address) (j : ℕ) : Expr :=
  if h:j<L*blocks then
    let idx:=((finProdFinEquiv (m:=L) (n:=blocks)).symm ⟨j,h⟩)
    (chart idx.1 idx.2).expr
  else .lit 0

def dropOff (origin blocks H L : ℕ) (chart : Fin L→ Fin blocks→ Address) :=
  DescentPackedFlowBatch.passes origin H H (flattened chart) 0 (L*blocks)

theorem fetch_blocks (chart : Fin L→ Fin blocks→ Address) (mem : Memory w) (origin H : ℕ)
    (ok : ∀j x,(chart j x).Fits origin H w) (limit : origin+(L*blocks)*H<2^w) :
    let ps:=dropOff origin blocks H L chart
    let warm:=result ps mem
    (program w ps).Exec mem warm (clock ps) ∧ CheapCode (program w ps) ∧
    (∀j x (h : Fin H),warm ((banks (L:=L) origin (blocks*H) j).base+(finProdFinEquiv (x,h)).val)=
      mem ((chart j x).atHost h)) ∧
    (∀a,a<origin ∨ origin+(L*blocks)*H≤a→ warm a=mem a) ∧
    clock ps≤4+(L*blocks)*(4+H*18) := by
  dsimp only
  have fits (j : ℕ) (hj:j<L*blocks) : (flattened chart j).Fits w origin:=by
    simp only [flattened,dite_eq_left hj]
    exact Address.room _ (ok _ _)
  obtain ⟨done,issued,lo⟩:=DescentPackedFlowBatch.execute origin H H (L*blocks) (flattened chart) mem fits limit le_rfl
  refine ⟨done,program_cheap _ _,?_,?_,?_⟩
  · intro j x h
    have read:=issued (finProdFinEquiv (j,x)) h
    have loc : (banks (L:=L) origin (blocks*H) j).base+(finProdFinEquiv (x,h)).val=
        origin+(finProdFinEquiv (j,x)).val*H+h.val:=by
      simp only [banks,column,finProdFinEquiv_apply_val]
      ring
    rw [loc]
    refine read.trans ?_
    let e : Fin L × Fin blocks ≃ Fin (L*blocks):=finProdFinEquiv
    have ix : e.symm ⟨(e (j,x)).val,(e (j,x)).isLt⟩=(j,x):=e.symm_apply_apply (j,x)
    simp only [flattened,dite_eq_left (finProdFinEquiv (j,x)).isLt]
    rw [show finProdFinEquiv.symm ⟨(finProdFinEquiv (j,x)).val,(finProdFinEquiv (j,x)).isLt⟩=(j,x) from ix]
    exact Address.read (chart j x) (ok j x) mem h
  · intro a away
    rcases away with small|big
    · exact lo _ small
    · exact DescentPackedFlowBatch.above _ _ _ _ _ 0 _ a le_rfl (by simpa using big)
  · apply DescentPackedFlowBatch.tariff origin H H (L*blocks) (flattened chart) 7
    intro j hj
    simp only [flattened,dite_eq_left hj]
    cases chart _ _ <;> simp [Address.expr,Expr.work]
def Pages.source (s : Pages blocks cap A) (mem : Memory w) (x : Fin blocks) (h : Fin H) :
    Source cap N A d :=fun j=>((mem ((s.address j x).atHost h)).val:Cell d)

/-- The gathered archive contains the true previous words at the exact address
that one shared ROM uses for all blocks and all common host ordinals. -/
theorem Pages.fetched (s : Pages blocks cap A) (mem : Memory w) (origin H : ℕ)
    (ok : ∀j : Fin (columns cap N A),∀b,(s.address j b).Fits origin H w)
    (room : origin+(columns cap N A*blocks)*H<2^w) (x : Fin blocks) (h : Fin H) :
    let L:=columns cap N A
    let warm:=result (dropOff origin blocks H L s.address) mem
    low (d:=d) (banks (L:=L) origin (blocks*H)) warm (finProdFinEquiv (x,h))=s.source mem x h := by
  dsimp only
  have published:=(fetch_blocks s.address mem origin H ok room).2.2.1
  funext j
  exact congrArg (fun w : Word _=>(w.val:Cell d)) (published j x h)

/-- Run the gathers and the shared pointer dictionary consecutively. Static
addresses specify genuine preceding columns. All reads of dynamic content
happen before the dense output pass. -/
theorem Pages.execute (s : Pages blocks cap A) (mem : Memory w) (origin H : ℕ)
    (f : (Fin (columns cap N A)→ Cell d)→ Cell b)
    (ok : ∀j x,(s.address (N:=N) j x).Fits origin H w) (slot : 2^d < 2^w)
    (room : rom origin (columns cap N A) (blocks*H)+DescentTerminalPointerFrame.size (columns cap N A) d+blocks*H < 2^w) :
    let L:=columns cap N A
    let ps:=dropOff origin blocks H L s.address
    let warm:=result ps mem
    let B:=banks (L:=L) origin (blocks*H)
    let base:=rom origin L (blocks*H)
    let start:=base+DescentTerminalPointerFrame.size L d
    let after:=DescentTerminalPointerFrame.result base B (blocks*H) f warm
    ((program w ps).seq (DescentTerminalPointerFrame.program w base B (blocks*H) f)).Exec mem after
      (clock ps+((4+10*DescentTerminalPointerFrame.size L d)+(4+(blocks*H)*(16+26*L)))) ∧
    CheapCode ((program w ps).seq (DescentTerminalPointerFrame.program w base B (blocks*H) f)) ∧
    (∀(x : Fin blocks)(h : Fin H),after (start+(finProdFinEquiv (x,h)).val)=((f (s.source mem x h)).val:Word w)) ∧
    (∀a,a<origin ∨ start+blocks*H≤a→ after a=mem a) ∧
    clock ps≤4+(L*blocks)*(4+H*18) := by
  dsimp only
  let L:=columns cap N A
  have sep : origin+(L*blocks)*H≤rom origin L (blocks*H):=by
    rw [Nat.mul_assoc];exact Nat.le_add_right _ _
  have small : origin+(L*blocks)*H<2^w:=by dsimp only [L] at *;omega
  obtain ⟨g,cheap₀,values,keep₀,time⟩:=fetch_blocks s.address mem origin H ok small
  let warm:=result (dropOff origin blocks H L s.address) mem
  let B:=banks (L:=L) origin (blocks*H)
  have room':=banks_fit (L:=L) origin (blocks*H) d slot room
  obtain ⟨ext,cheap₁,keep₁⟩:=DescentTerminalPointerFrame.run _ B f warm room'
  have issued:=DescentTerminalPointerFrame.read_masked _ B f warm room' (low (d:=d) B warm) (fun _ _=>rfl)
  refine ⟨g.then ext,cheap_seq cheap₀ cheap₁,?_,?_,time⟩
  · intro x h
    exact (issued (finProdFinEquiv (x,h))).trans (congrArg (fun row=>((f row).val:Word w)) (s.fetched _ _ _ ok small x h))
  · intro a away
    have before:origin≤rom origin L (blocks*H):=(Nat.le_add_right ..).trans sep
    change a<origin ∨ rom origin L (blocks*H)+DescentTerminalPointerFrame.size L d+blocks*H≤a at away
    rcases away with lowSide | highSide
    · exact (keep₁ a (Or.inl (lowSide.trans_le before))).trans (keep₀ a (Or.inl lowSide))
    · have highGather:origin+(L*blocks)*H≤a:=
        sep.trans ((Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans highSide))
      exact (keep₁ a (Or.inr highSide)).trans (keep₀ a (Or.inr highGather))


end Gather
end
end Hierarchy.DescentTerminalPointerDigits

end OAI
