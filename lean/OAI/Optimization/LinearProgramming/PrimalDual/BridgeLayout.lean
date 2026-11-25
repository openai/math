import OAI.Optimization.LinearProgramming.PrimalDual.DecoderHeader
import OAI.Optimization.LinearProgramming.PrimalDual.OutputSetup
import OAI.Optimization.LinearProgramming.PrimalDual.RAMBudget
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.VecNotation

/-! Finite workspace planning before a second feasibility call and after either return. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual
namespace Bridge

open RAM RAM.Block RAM.Tape Polynomial

def origLen (m d : Nat) := m*d+m+d
def rowCount (m d : Nat) := m+(m+(d+(d+1)))
def jointLen (m d : Nat) := rowCount m d*(d+m)+rowCount m d
def origin (m d : Nat) := 64*(m+d+1)*(m+d+1)
def jointBase (m d : Nat) := origin m d+origLen m d+d
def cutoff (m d B : Nat) := 200+B+jointBase m d+jointLen m d
def returnBase (m d : Nat) := 16*(m+d+1)+64

/-- The gathering destinations start above every low source and both second-frame
scatters. These bounds include the full dense joint matrix and both saved vectors. -/
theorem origin_above (m d : Nat) :
    3+2*(jointLen m d+2*d) ≤ origin m d ∧ 3+2*origLen m d ≤ origin m d ∧
    2*d ≤ origin m d ∧ 4 ≤ origin m d := by
  unfold origin jointLen rowCount origLen
  refine ⟨?_,?_,?_,?_⟩ <;> ring_nf <;> omega

noncomputable def termBudget {n : Nat} (es : List (AddressTerm n)) : Polynomial Nat :=
  (es.map AddressTerm.boundCost).sum

theorem termBudget_le {n : Nat} (es : List (AddressTerm n)) (v : Fin n → Nat)
    (B : Nat) (h : ∀ i, v i ≤ B) :
    (es.map (·.cost v)).sum ≤ (termBudget es).eval B := by
  induction es with
  | nil => simp [termBudget]
  | cons e es ih =>
    simpa [termBudget] using Nat.add_le_add (e.cost_le v B h) ih

def firstTerms : List (AddressTerm 3) :=
  let m := AddressTerm.reg 0
  let d := AddressTerm.reg 1
  let B := AddressTerm.reg 2
  let nr := m+(m+(d+(d+1)))
  let J := nr*(d+m)+nr
  let L := m*d+m+d
  let O := 64*(m+d+1)*(m+d+1)
  let Jbase := O+L+d
  let Q := 200+B+Jbase+J
  [0,m,3,d,O,O+L,Jbase,O+m*d+m,L,d+d,J,Q,nr,d+m]

/-- Register numbers 41 and 43 are odd. The original row and column counts in
them survive an isolated second call with different dimensions. -/
structure FirstRegs (ix : Nat → Nat) (m d B : Nat) : Prop where
  even : ix 40 = 0
  mreg : ix 41 = m
  odd : ix 42 = 3
  dreg : ix 43 = d
  orig : ix 44 = (origin m d)
  point : ix 45 = (origin m d)+(origLen m d)
  joint : ix 46 = (jointBase m d)
  saved : ix 47 = (origin m d)+m*d+m
  inputLen : ix 48 = (origLen m d)
  savedLen : ix 49 = d+d
  jointLen : ix 50 = (jointLen m d)
  limit : ix 51 = (cutoff m d B)
  rows : ix 52 = (rowCount m d)
  cols : ix 53 = d+m

def returnTerms : List (AddressTerm 2) :=
  let m := AddressTerm.reg 0
  let d := AddressTerm.reg 1
  let R := 16*(m+d+1)+64
  [0,m,3,d,R,R+d,R+d+d,R+d+d+d,R+d+d+d+d,d+m,R+(d+m)+1,m+m+m+m,m+m+m+m+d+d,3+d+d]

structure ReturnRegs (ix : Nat → Nat) (m d : Nat) : Prop where
  even : ix 40 = 0
  mreg : ix 41 = m
  odd : ix 42 = 3
  dreg : ix 43 = d
  buffer : ix 44 = (returnBase m d)
  minus : ix 45 = (returnBase m d)+d
  rayObj : ix 46 = (returnBase m d)+d+d
  xbuf : ix 47 = (returnBase m d)+d+d+d
  outbuf : ix 48 = (returnBase m d)+d+d+d+d
  zlen : ix 49 = d+m
  optObj : ix 50 = (returnBase m d)+(d+m)+1
  plusSrc : ix 51 = m+m+m+m
  minusSrc : ix 52 = m+m+m+m+d+d
  xsrc : ix 53 = 3+d+d

/-- Copy the preserved odd headers down before computing any new indices. -/
def firstHeader : Block :=
  .seq (CursorBind.script [.reg 0 9,.reg 1 11,.reg 2 21]) (Header.write 40 firstTerms)

def returnHeader (mr dr : Nat) : Block :=
  .seq (CursorBind.script [.reg 0 mr,.reg 1 dr]) (Header.write 40 returnTerms)

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

theorem firstHeader_correct (s : Memory K) (safe : Good P s) (m d B : Nat)
    (h9 : s.index 9=m) (h11 : s.index 11=d) (h21 : s.index 21=B) :
    ∃ t k, Eval (Good P) firstHeader s k t ∧ k ≤ 3+(termBudget firstTerms).eval (m+d+B) ∧
      t.data = s.data ∧ FirstRegs t.index m d B := by
  let bs : List CursorBind := [.reg 0 9,.reg 1 11,.reg 2 21]
  let u := CursorBind.install bs s
  have init := CursorBind.run bs s safe
  let env : Fin 3 → Nat := ![m,d,B]
  have henv (i : Fin 3) : u.index i.val = env i := by
    fin_cases i <;> simp [u,bs,CursorBind.install,CursorBind.apply,env,h9,h11,h21]
  obtain ⟨t,k,r,hk,hd,_,w⟩ := Header.write_correct firstTerms env 40 u (by decide) henv init.safe_end
  have h := (termBudget_le firstTerms env (m+d+B) (by intro i; fin_cases i <;> dsimp [env] <;> omega))
  refine ⟨t,_,init.seq r,Nat.add_le_add_left (hk.trans h) 3,hd,?_⟩
  exact ⟨w ⟨0,by decide⟩,w ⟨1,by decide⟩,w ⟨2,by decide⟩,w ⟨3,by decide⟩,w ⟨4,by decide⟩,w ⟨5,by decide⟩,w ⟨6,by decide⟩,w ⟨7,by decide⟩,w ⟨8,by decide⟩,w ⟨9,by decide⟩,w ⟨10,by decide⟩,w ⟨11,by decide⟩,w ⟨12,by decide⟩,w ⟨13,by decide⟩⟩

theorem returnHeader_correct (s : Memory K) (safe : Good P s) (mr dr m d : Nat)
    (_hmr : 6 ≤ mr) (hdr : 6 ≤ dr) (hm : s.index mr=m) (hd : s.index dr=d) :
    ∃ t k, Eval (Good P) (returnHeader mr dr) s k t ∧ k ≤ 2+(termBudget returnTerms).eval (m+d) ∧
      t.data = s.data ∧ ReturnRegs t.index m d := by
  let bs : List CursorBind := [.reg 0 mr,.reg 1 dr]
  let u := CursorBind.install bs s
  have init := CursorBind.run bs s safe
  let env : Fin 2 → Nat := ![m,d]
  have henv (i : Fin 2) : u.index i.val = env i := by
    fin_cases i <;> simp [u,bs,CursorBind.install,CursorBind.apply,env,hm,hd,
      Memory.putIndex_ne _ (by omega : dr ≠ 0)]
  obtain ⟨t,k,r,hk,data,_,w⟩ := Header.write_correct returnTerms env 40 u (by decide) henv init.safe_end
  have h := termBudget_le returnTerms env (m+d) (by intro i; fin_cases i <;> dsimp [env] <;> omega)
  refine ⟨t,_,init.seq r,Nat.add_le_add_left (hk.trans h) 2,data,?_⟩
  exact ⟨w ⟨0,by decide⟩,w ⟨1,by decide⟩,w ⟨2,by decide⟩,w ⟨3,by decide⟩,w ⟨4,by decide⟩,w ⟨5,by decide⟩,w ⟨6,by decide⟩,w ⟨7,by decide⟩,w ⟨8,by decide⟩,w ⟨9,by decide⟩,w ⟨10,by decide⟩,w ⟨11,by decide⟩,w ⟨12,by decide⟩,w ⟨13,by decide⟩⟩

end Bridge
end PrimalDual
end LinearProgramming
end Optimization
end OAI
