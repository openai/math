import OAI.Hierarchy.DescentTerminalPointerPages

namespace OAI
/-! # Six contiguous terminal role banks from real block-major prior fields -/
namespace Hierarchy.DescentTerminalSliceShelf
open DescentTerminalPointerDigits DescentOperandStateBanks DescentSIMDLookup ProtocolRAM DescentStaticWordColumn
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {L d H blocks w:ℕ} {width:Fin 6→ℕ}
variable (base:ℕ) (chart:Fin L→Fin blocks→Gather.Address)
variable (write:(f:Fin 6)→(Fin L→Cell d)→Cell (width f))
def pad (rows:ℕ) := 2^Nat.clog 2 rows
def stage (base L d rows f:ℕ) :=
  Gather.rom base L rows+f*(DescentTerminalPointerFrame.size L d+pad rows)
def field (base L d rows f:ℕ) : Bank :=
  ⟨stage base L d rows f+DescentTerminalPointerFrame.size L d,Nat.clog 2 rows⟩
def fence (base L d rows:ℕ) := stage base L d rows 6
def clocks (L d rows f:ℕ) := 4+f*((4+10*DescentTerminalPointerFrame.size L d)+(4+rows*(16+26*L)))
def «prefix» (rows w base:ℕ) : (n:ℕ)→ n≤6→Procedure w
  | 0,_=>ProtocolRAM.program w []
  | j+1,ok=>(«prefix» rows w base j (by omega)).seq (DescentTerminalPointerFrame.program w
      (stage base L d rows j) (Gather.banks (L:=L) base rows) rows (write ⟨j,by omega⟩))
def after (rows base:ℕ) (m:Memory w) : (n:ℕ)→n≤6→Memory w
  | 0,_=>m
  | j+1,ok=>DescentTerminalPointerFrame.result (stage base L d rows j)
      (Gather.banks (L:=L) base rows) rows (write ⟨j,by omega⟩) (after rows base m j (by omega))

theorem monotone (base L d rows:ℕ) : Monotone (stage base L d rows) :=
  fun _ _ h=>Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

local notation "rows" => blocks*H
local notation "table" => stage base L d rows
local notation "out" => field base L d rows
local notation "ports" => Gather.banks (L:=L) base rows
local notation "size_" => DescentTerminalPointerFrame.size L d

theorem output_end (f:ℕ) : (out f).base+(out f).size=table (f+1) := by
  simp [field,stage,pad,Bank.size,Nat.add_mul];omega

variable (m:Memory w) (off:2^d<2^w) (room:fence base L d (blocks*H)<2^w)

include off room in
theorem converted (n:ℕ) (limit:n≤6) :
    let result_:=after write rows base m n limit
    («prefix» write rows w base n limit).Exec m result_ (clocks L d rows n) ∧ CheapCode («prefix» write rows w base n limit) ∧
    (∀a,a<table 0 ∨ table n≤a → result_ a=m a) ∧
    ∀(f:Fin 6),f.val<n→∀i:Fin rows,result_ ((out f.val).base+i.val)=
      ((write f (fun j=>((m ((ports j).base+i.val)).val : Cell d))).val:Word w) := by
  dsimp only
  induction n with
  | zero=>
    refine ⟨?_, ProtocolRAM.program_cheap w [], fun _ _ => rfl, by simp⟩
    have ticks : clocks L d rows 0 = ProtocolRAM.clock [] := by simp [clocks, ProtocolRAM.clock]
    rw [ticks]
    exact @ProtocolRAM.program_exec w [] m (by simp)
  | succ n ih=>
    let f:Fin 6:=⟨n,by omega⟩
    let before:=after write rows base m n (by omega)
    obtain ⟨old,cheap,frame,values⟩:=ih (by omega)
    have earlier:table 0≤table n:=monotone base L d rows (Nat.zero_le _)
    have bound:table (n+1)<2^w:=(monotone base L d rows limit).trans_lt room
    have e:=output_end (base:=base) (L:=L) (d:=d) (H:=H) (blocks:=blocks) n
    have len:rows≤(out n).size:=Nat.le_pow_clog (by decide) _
    have start:Gather.rom base L rows≤table n:=by simp [stage]
    have endAt:table n+size_+rows<2^w:=by
      change table n+size_+(out n).size=table (n+1) at e
      omega
    have ok:DescentTerminalPointerFrame.Room ports (table n) d rows w:=
      ⟨fun j=>(read_fits j start (by omega)).1,
        fun _=>Nat.le_pow_clog (by decide) _,off,endAt⟩
    obtain ⟨run,cheap',keep⟩:=DescentTerminalPointerFrame.run (table n) ports (write f) before ok
    refine ⟨?_,cheap_seq cheap cheap',?_,?_⟩
    · have ticks : clocks L d rows (n+1) =
          clocks L d rows n + ((4+10*size_) + (4+rows*(16+26*L))) := by
        simp only [clocks, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
      rw [ticks]
      exact @Procedure.Exec.then w («prefix» write rows w base n (by omega))
        (DescentTerminalPointerFrame.program w (table n) ports rows (write f))
        m before _ (clocks L d rows n) _ (@old) (@run)
    · intro a h
      rcases h with l|r
      · exact (keep a (.inl (l.trans_le earlier))).trans (frame a (.inl l))
      · have above:table n+size_+rows≤a:=by
          change table n+size_+(out n).size=table (n+1) at e
          omega
        exact (keep a (.inr above)).trans (frame a (.inr ((monotone base L d rows (Nat.le_succ n)).trans r)))
    · intro j hj i
      by_cases last:j.val=n
      · have same:j=f:=Fin.ext last
        subst j
        apply DescentTerminalPointerFrame.read_masked (table n) ports (write f) before ok _ _ i
        intro k col
        have minimum:Gather.rom base L rows=table 0:=by simp [stage]
        have early:(ports col).base+k.val<table 0:=by
          have bound':=(read_fits (w:=w) (src:=base) (words:=rows) col
            (show guard base L rows≤table 0 from minimum.le) (earlier.trans_lt (by omega : table n<2^w))).1.2.2
          have enough:k.val<(ports col).size:=k.isLt.trans_le (Nat.le_pow_clog (by decide) _)
          change (ports col).base+(ports col).size≤table 0 at bound'
          omega
        have unchanged : before ((ports col).base+k.val) = m ((ports col).base+k.val) :=
          frame _ (.inl early)
        exact congrArg (fun cell : Word w => cell.val % 2^d) unchanged
      · have prev:j.val<n:=by omega
        have hi:=output_end (base:=base) (L:=L) (d:=d) (H:=H) (blocks:=blocks) j.val
        have lt: i.val<(out j.val).size:=i.isLt.trans_le (Nat.le_pow_clog (by decide) _)
        have ord:=monotone base L d rows (show j.val+1≤n by omega)
        exact (keep _ (.inl (by omega))).trans (values j prev i)

end
end Hierarchy.DescentTerminalSliceShelf

end OAI
