import OAI.Hierarchy.DescentTerminalBookCableEntry

namespace OAI
/-! # Literal table for the original six geometry fields at one terminal home -/
namespace Hierarchy.DescentTerminalLocalPortBook
open DescentTerminalPointerDigits DescentTerminalPeerChronology DescentSharedCableNames
open scoped Classical BigOperators
noncomputable section

/-- Resident shape and p-grain panel at a common host. Sides encode the
comparison with the opposite host. The lookup never keys on a full host number. -/
structure Board (D groups blocks cap:ℕ) where
  side : Fin D→Ordering
  venue : Fin groups→Fin blocks→Option ℕ
  ports : Fin groups→Fin blocks→Fin (2*cap)→Option (Stage.Live D cap)

namespace Board
variable {D groups blocks cap:ℕ} (B:Board D groups blocks cap)

def here (s:Ordering):ℕ:=if s=.gt then 1 else 0
def other (s:Ordering):ℕ:=if s=.lt then 1 else 0

theorem short_key (x y g b K:ℕ) (u:Stage.Live D cap) :
    wingKey (here (compare x y)) (other (compare x y)) g b K u=wingKey x y g b K u := by
  rcases lt_trichotomy x y with h|rfl|h
  · rw [Std.compare_eq_lt.mpr h]
    cases targetEq : u.target <;> simp [wingKey,targetEq,cell,DescentTerminalPeerChronology.side,here,other,Nat.min_eq_left h.le,h.ne]
  · cases u.target <;> simp [wingKey,cell,DescentTerminalPeerChronology.side,here,other]
  · rw [Std.compare_eq_gt.mpr h]
    cases targetEq : u.target <;> simp [wingKey,targetEq,cell,DescentTerminalPeerChronology.side,here,other,Nat.min_eq_right h.le,h.ne]

def keys (lane:Fin D):Finset ℕ :=
  peerKeys (here (B.side lane)) (other (B.side lane)) lane B.ports

def internal (scale:ℕ) (g:Fin groups) (b:Fin blocks) :=
  (grains (B.ports g b)).card*scale

def exterior (scale:ℕ) (g:Fin groups) (b:Fin blocks) :=
  (B.venue g b).getD 0-B.internal scale g b

def counts (scale:ℕ) : Fin (D+1)→ℕ :=
  Fin.cases (∑g,∑b,B.exterior scale g b) fun lane=>(B.keys lane).card*scale

/-- Each finest coordinate is evaluated inside the common position's static
truth table. The machine runs one scan iteration per host and output field. -/
def lookupCable (scale:ℕ) (g:Fin groups) (b:Fin blocks) (j:ℕ) : Option (Fin (D+1)×ℕ) :=
  let panel:=B.ports g b
  let candidates:=fun (entry:Fin (2*cap)×Fin scale)=>(panel entry.1).bind fun r=>
    if operandOffset panel r scale entry.2.val=j then
      some (r.neighbor.succ,portOffset (B.keys r.neighbor) (here (B.side r.neighbor)) (other (B.side r.neighbor))
        g.val b.val blocks scale entry.2.val r) else none
  if hit:∃x,(candidates x).isSome then candidates hit.choose else none

def directory (A scale pinWords calendar:ℕ) (active:Fin groups→Fin blocks→ℕ) :
    Directory (D+1) (groups*blocks) A where
  pieces:=B.counts scale
  venue v:=let u:=finProdFinEquiv.symm v;B.venue u.1 u.2
  address v j:=
    let u:=finProdFinEquiv.symm v
    let inner:=B.internal scale u.1 u.2
    if j.val< inner then B.lookupCable scale u.1 u.2 j.val else
      let num:=j.val-inner
      some (0,(num/pinWords*calendar+active u.1 u.2)*pinWords+num%pinWords)

theorem lookup_read (scale:ℕ) (g:Fin groups) (b:Fin blocks) (j:ℕ) (dest:Fin (D+1)×ℕ)
    (live:∃s r, ∃l:Fin scale,B.ports g b s=some r ∧ operandOffset (B.ports g b) r scale l.val=j)
    (unique:∀s r (l:Fin scale),B.ports g b s=some r→ operandOffset (B.ports g b) r scale l.val=j→
      (r.neighbor.succ,portOffset (B.keys r.neighbor) (here (B.side r.neighbor)) (other (B.side r.neighbor))
        g.val b.val blocks scale l.val r)=dest) :
    B.lookupCable scale g b j=some dest := by
  unfold lookupCable
  dsimp only
  split
  · rename_i hit
    generalize choiceEq:hit.choose=x
    obtain ⟨s,l⟩:=x
    have chosen:=hit.choose_spec
    rw [choiceEq] at chosen
    cases hs:B.ports g b s with
    | none=>simp [hs] at chosen
    | some r=>
      by_cases h:operandOffset (B.ports g b) r scale l.val=j
      · simp [h,unique s r l hs h]
      · simp [hs,h] at chosen
  · rename_i no
    obtain ⟨s,r,l,hs,eqn⟩:=live
    exact False.elim (no ⟨(s,l),by simp [hs,eqn]⟩)

theorem public_read (A scale pinWords calendar:ℕ) (active:Fin groups→Fin blocks→ℕ)
    (g:Fin groups) (b:Fin blocks) (j:Fin A) (ordinal digit:ℕ) (low:digit<pinWords)
    (offset:j.val=B.internal scale g b+ordinal*pinWords+digit) :
    (B.directory A scale pinWords calendar active).address (finProdFinEquiv (g,b)) j=
      some (0,(ordinal*calendar+active g b)*pinWords+digit) := by
  have at_:j.val-B.internal scale g b=ordinal*pinWords+digit:=by omega
  have after:¬j.val<B.internal scale g b:=by omega
  simp only [directory,Equiv.symm_apply_apply,ite_eq_right after,at_]
  rw [Nat.mul_comm ordinal pinWords, Nat.mul_add_div (Nat.zero_lt_of_lt low), Nat.div_eq_of_lt low]
  simp [Nat.add_mod,Nat.mod_eq_of_lt low]

end Board
end
end Hierarchy.DescentTerminalLocalPortBook

end OAI
