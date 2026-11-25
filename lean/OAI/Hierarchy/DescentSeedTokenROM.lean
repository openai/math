import OAI.Hierarchy.DescentSeedTokenMap
import OAI.Hierarchy.DescentResetStemHeaderROM

namespace OAI
/-! # The literal dictionary and four row columns for reading seed donor tokens -/
namespace Hierarchy.DescentSeedTokenColumns
open DescentSixParty.Chronology DescentSIMDLookup DescentDyadicSpan ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {O H b G M w : ℕ}

def dictionary (base a M : ℕ) : Bank := ⟨base,a*M⟩
def column (base a M n t : ℕ) : Bank := ⟨base+2^(a*M)+t*span n,Nat.clog 2 n⟩
def size (a M n : ℕ) := 2^(a*M)+4*span n

def oldFlag (x : Option (Option (Fin O))) : ℕ :=
  match x with
  | some (some _) => 1
  | _ => 0

def oldRow (src : Fin H→Option (Option (Fin O))) (p : Row H G M) : ℕ :=
  match src p.1 with
  | some (some v) => (row O G M (v,p.2)).val
  | _ => 0

def fallback (src : Fin H→Option (Option (Fin O))) (hub : Cell b) (p : Row H G M) : ℕ :=
  (data (fun v (_ : Fin G)=>match src v with | some none=>hub | _=>0) p).val

private def atField (src : Fin H→Option (Option (Fin O))) (hub : Cell b) (j : ℕ) (p : Row H G M) : ℕ :=
  match j with
  | 0 => oldFlag (src p.1)
  | 1 => oldRow src p
  | 2 => fallback src hub p
  | _ => maskWord b M G p.2.val

def literals (G M a : ℕ) (src : Fin H→Option (Option (Fin O))) (hub : Cell b) (k : ℕ) : ℕ :=
  if inside : k<2^(a*M) then (table (M:=M) (bump b) (⟨k,inside⟩ : Cell (a*M))).val
  else
    let n:=H*chunks G M
    let j:=k-2^(a*M)
    DescentSeedSignedBroadcast.finRead (fun i : Fin n=>atField src hub (j/span n) ((row H G M).symm i)) (j%span n)

def prepare (w G M a base : ℕ) (src : Fin H→Option (Option (Fin O))) (hub : Cell b) : NativePhase w :=
  let count:=size a M (H*chunks G M)
  ⟨DescentStaticWordColumn.program w base (literals G M a src hub) count,4+10*count,
   fun m=>DescentStaticWordColumn.image base (literals G M a src hub) m count,
   @DescentStaticWordColumn.cheap w base (literals G M a src hub) count⟩

structure Tables (G M a base : ℕ) (src : Fin H→Option (Option (Fin O))) (hub : Cell b)
    {w : ℕ} (m : Memory w) : Prop where
  dict : ∀u : Cell (a*M),m ((dictionary base a M).base+u.val)=((table (M:=M) (bump b) u).val:Word w)
  flag : ∀p : Row H G M,m ((column base a M (H*chunks G M) 0).base+(row H G M p).val)=(oldFlag (src p.1):Word w)
  addr : ∀p : Row H G M,m ((column base a M (H*chunks G M) 1).base+(row H G M p).val)=(oldRow src p:Word w)
  other : ∀p : Row H G M,m ((column base a M (H*chunks G M) 2).base+(row H G M p).val)=(fallback src hub p:Word w)
  mask : ∀p : Row H G M,m ((column base a M (H*chunks G M) 3).base+(row H G M p).val)=(maskWord b M G p.2.val:Word w)

private theorem field_read (a base : ℕ) (src : Fin H→Option (Option (Fin O))) (hub : Cell b)
    (m : Memory w) (t : Fin 4) (p : Row H G M) :
    (prepare w G M a base src hub).image m ((column base a M (H*chunks G M) t.val).base+(row H G M p).val)=
      (atField src hub t.val p:Word w) := by
  let n:=H*chunks G M
  let u : Fin n:=row H G M p
  let pow_:=2^(a*M)
  have inside : u.val < span n := u.isLt.trans_le (span_ge n)
  have bound : t.val*span n+u.val<4*span n := (Nat.add_lt_add_left inside _).trans_le
    (by rw [←Nat.succ_mul]; exact Nat.mul_le_mul_right _ t.isLt)
  have loc : pow_+(t.val*span n+u.val) < size a M n := Nat.add_lt_add_left bound _
  have mod : (t.val*span n+u.val)%span n=u.val := by
    simp [Nat.add_mod,Nat.mod_eq_of_lt inside]
  have div : (t.val*span n+u.val)/span n=t.val := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ (span_pos n),Nat.div_eq_of_lt inside,Nat.zero_add]
  change DescentStaticWordColumn.image base (literals G M a src hub) m (size a M n)
    (base+pow_+t.val*span n+u.val)=_
  rw [show base+pow_+t.val*span n+u.val=base+(pow_+(t.val*span n+u.val)) by omega,
    DescentStaticWordColumn.read _ _ _ _ loc]
  have high : ¬pow_+(t.val*span n+u.val)<pow_ := Nat.not_lt_of_ge (Nat.le_add_right ..)
  dsimp only [pow_,n,u] at high div mod ⊢
  simp only [literals,dite_eq_right high,Nat.add_sub_cancel_left,div,mod,DescentSeedSignedBroadcast.finRead,
    dite_eq_left (row H G M p).isLt]
  change (atField src hub t.val ((row H G M).symm (row H G M p)):Word w)=_
  rw [Equiv.symm_apply_apply]

theorem prepared (w G M a base : ℕ) (src : Fin H→Option (Option (Fin O))) (hub : Cell b) (m : Memory w)
    (room : base+size a M (H*chunks G M)<2^w) :
    (prepare w G M a base src hub).Runs m ∧ Tables G M a base src hub ((prepare w G M a base src hub).image m) ∧
      ∀z,z<base ∨ base+size a M (H*chunks G M)≤z → (prepare w G M a base src hub).image m z=m z := by
  let count:=size a M (H*chunks G M)
  refine ⟨?_,⟨?_,field_read a base src hub m (0:Fin 4),field_read a base src hub m (1:Fin 4),
    field_read a base src hub m (2:Fin 4),field_read a base src hub m (3:Fin 4)⟩,?_⟩
  · intro P R K machine
    exact DescentStaticWordColumn.mount base count (literals G M a src hub) m room machine
  · intro u
    have bound : u.val<count := u.isLt.trans_le (Nat.le_add_right ..)
    change DescentStaticWordColumn.image base (literals G M a src hub) m count (base+u.val)=_
    rw [DescentStaticWordColumn.read _ _ _ _ bound]
    simp only [literals,dite_eq_left u.isLt]
  · exact fun z away=>DescentStaticWordColumn.frame base count (literals G M a src hub) m z away

end
end Hierarchy.DescentSeedTokenColumns

end OAI
