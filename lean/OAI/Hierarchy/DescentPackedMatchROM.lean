import OAI.Hierarchy.DescentPackedMatchFee
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! # The shared public dictionaries for the native neighborhood matcher -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Gather.ROM
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {r D p d N K w : ℕ}

abbrev Page (N K : ℕ) := (Fin 1 ⊕ Fin N) ⊕ (Fin K ⊕ Fin 6)

def ordinal (N K : ℕ) : Page N K ≃ Fin ((1+N)+(K+6)) :=
  (finSumFinEquiv.sumCongr finSumFinEquiv).trans finSumFinEquiv

def pitch (unit M : ℕ) := 2^(unit*M)
def at₀ (base unit M : ℕ) (j : Page N K) := base+(ordinal N K j).val*pitch unit M
def mask₀ (base unit M N K : ℕ) := base+((1+N)+(K+6))*pitch unit M

def wordAt {b : ℕ} (value : Cell b→ℕ) (i : ℕ) := if hi : i<2^b then value ⟨i,hi⟩ else 0

theorem at_live {b : ℕ} (value : Cell b→ℕ) (i : Cell b) : wordAt value i.val=value i := by
  simp only [wordAt,dite_eq_left i.isLt]

def code (s : Shape) (d r D p B K M R : ℕ) : Page (fields r D p) K → ℕ→ℕ
  | .inl (.inl _),i=>2^(d*M)*i
  | .inl (.inr j),i=>wordAt (fun z=>(DescentPackedZip.table (M:=M) (setField (d:=d) j) z).val) i
  | .inr (.inl k),i=>wordAt (fun z=>(DescentSIMDLookup.table (M:=M) (descriptor (r:=r) (D:=D) (p:=p) (digit:=d) s B k.val) z).val) i
  | .inr (.inr j),i=>match j.val with
    | 0=>wordAt (fun z=>(DescentSIMDLookup.table (M:=M) (lookupCell s) z).val) i
    | 1=>wordAt (chunkCount s M) i
    | 2=>2^(s.digit*R+(s.digit*R+s.digit*R))*i
    | 3=>2^(s.digit*R+s.digit*R)*i
    | 4=>2^(s.digit*R)*i
    | _=>wordAt (fun z=>(ProfileTable.table s M R z).val) i

def contents (s : Shape) (d r D p B K H G M R unit : ℕ) (x : ℕ) :=
  let P:=pitch unit M
  let N:=fields r D p
  let n:=H*chunks G M
  let A:=((1+N)+(K+6))*P
  if h : x/P<(1+N)+(K+6) then code s d r D p B K M R ((ordinal N K).symm ⟨x/P,h⟩) (x%P)
  else if h : x-A<n then maskWord s.inputBits M G ((row H G M).symm ⟨_,h⟩).2.val
  else if h : x-(A+n)<(K*H)*chunks G M then maskWord s.outputBits M G ((row (K*H) G M).symm ⟨_,h⟩).2.val else 0

def size (N K H G M unit : ℕ) :=
  ((1+N)+(K+6))*pitch unit M+H*chunks G M+(K*H)*chunks G M

structure Menu where
  joins : Fin (fields r D p)→DescentPackedZip.Tables
  desc : Fin K→Bank
  mask : Bank
  lookup : Banks
  count : Bank
  profile : ProfileTable.Tables

def chart (s : Shape) (d r D p K H G M R unit base : ℕ) (source : Bank) : Menu (r:=r) (D:=D) (p:=p) (K:=K) :=
  let N:=fields r D p
  let raw:=d*N
  let reg (j : Page N K) (b : ℕ) : Bank:=⟨at₀ base unit M j,b⟩
  let last (j : Fin 6) (b : ℕ) := reg (.inr (.inr j)) b
  let a:=s.outputBits*M
  let b:=s.digit*R
  let masks:=mask₀ base unit M N K
  ⟨fun i=>⟨reg (.inl (.inl 0)) (raw*M),reg (.inl (.inr i)) ((raw+d)*M)⟩,
   fun k=>reg (.inr (.inl k)) (raw*M),⟨masks,Nat.clog 2 (H*chunks G M+1)⟩,
   ⟨source,last 0 (s.inputBits*M),⟨masks+H*chunks G M,Nat.clog 2 ((K*H)*chunks G M+1)⟩⟩,
   last 1 a,⟨last 2 a,last 3 b,last 4 b,last 5 (ProfileTable.bits a b)⟩⟩

def program (s : Shape) (d r D p B K H G M R unit w base : ℕ) :=
  DescentStaticWordColumn.program w base (contents s d r D p B K H G M R unit) (size (fields r D p) K H G M unit)

def mounted (s : Shape) (d r D p B K H G M R unit base : ℕ) (m : Memory w) :=
  DescentStaticWordColumn.image base (contents s d r D p B K H G M R unit) m (size (fields r D p) K H G M unit)

theorem run (s : Shape) (d r D p B K H G M R unit base : ℕ) (m : Memory w)
    (space : base+size (fields r D p) K H G M unit<2^w) :
    (program s d r D p B K H G M R unit w base).Exec m (mounted s d r D p B K H G M R unit base m)
      (4+10*size (fields r D p) K H G M unit) := DescentStaticWordColumn.mount base _ _ m space

theorem frame (s : Shape) (d r D p B K H G M R unit base : ℕ) (m : Memory w) (a : ℕ)
    (earlier : a<base ∨ base+size (fields r D p) K H G M unit≤a) :
    mounted s d r D p B K H G M R unit base m a=m a := DescentStaticWordColumn.frame base _ _ m a earlier

theorem page_read (s : Shape) (d r D p B K H G M R unit base : ℕ) (m : Memory w) (j : Page (fields r D p) K)
    (i : ℕ) (within : i<pitch unit M) : mounted s d r D p B K H G M R unit base m (at₀ base unit M j+i)=
      (code s d r D p B K M R j i:Word w) := by
  let N:=fields r D p
  let P:=pitch unit M
  let q:=(ordinal N K j).val
  have fits : q<(1+N)+(K+6) := (ordinal N K j).isLt
  have span := Nat.mul_le_mul_right P (Nat.succ_le_of_lt fits)
  rw [Nat.succ_mul] at span
  have address : q*P+i<size N K H G M unit := by change _ < ((1+N)+(K+6))*P+_+_;omega
  have div : (q*P+i)/P=q := by rw [Nat.mul_comm q P,Nat.mul_add_div (Nat.zero_lt_of_lt within),Nat.div_eq_of_lt within,Nat.add_zero]
  have rem : (q*P+i)%P=i:=Nat.mul_add_mod_of_lt within
  change mounted s d r D p B K H G M R unit base m ((base+q*P)+i)=_
  rw [Nat.add_assoc]
  apply Eq.trans (DescentStaticWordColumn.read base _ _ m address)
  apply congrArg (fun v : ℕ=>(v:Word w))
  change (if h : (q*P+i)/P<(1+N)+(K+6) then _ else _)=_
  dsimp only [q, N, P] at div rem fits ⊢
  simp only [div, rem, dite_eq_left fits]
  exact congrArg (fun j' => code s d r D p B K M R j' i) ((ordinal N K).symm_apply_apply j)

theorem desc_mask (s : Shape) (d r D p B K H G M R unit base : ℕ) (m : Memory w) (i : Fin (H*chunks G M)) :
    mounted s d r D p B K H G M R unit base m (mask₀ base unit M (fields r D p) K+i.val)=
      (maskWord s.inputBits M G ((row H G M).symm i).2.val:Word w) := by
  let q:=(1+fields r D p)+(K+6)
  let P:=pitch unit M
  have beyond : ¬(q*P+i.val)/P<q := Nat.not_lt.mpr ((Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).2 (Nat.le_add_right ..))
  have inside := i.isLt
  change mounted _ _ _ _ _ _ _ _ _ _ _ _ _ m ((base+q*P)+i.val)=_
  rw [Nat.add_assoc]
  apply Eq.trans (DescentStaticWordColumn.read base _ _ m (show q*P+i.val<size (fields r D p) K H G M unit by
    change _ < q*P+_+_;omega))
  apply congrArg (fun v : ℕ=>(v:Word w))
  change (if _h : (q*P+i.val)/P<q then _ else _)=_
  dsimp only [q, P] at beyond ⊢
  simp only [dite_eq_right beyond, Nat.add_sub_cancel_left, dite_eq_left inside]

theorem topo_mask (s : Shape) (d r D p B K H G M R unit base : ℕ) (m : Memory w) (i : Fin ((K*H)*chunks G M)) :
    mounted s d r D p B K H G M R unit base m ((mask₀ base unit M (fields r D p) K+H*chunks G M)+i.val)=
      (maskWord s.outputBits M G ((row (K*H) G M).symm i).2.val:Word w) := by
  let q:=(1+fields r D p)+(K+6)
  let P:=pitch unit M
  let n:=H*chunks G M
  have positive : 0 < P := Nat.two_pow_pos _
  have beyond : ¬(q*P+n+i.val)/P<q := Nat.not_lt.mpr ((Nat.le_div_iff_mul_le positive).2
    ((Nat.le_add_right (q*P) n).trans (Nat.le_add_right _ i.val)))
  have middle : ¬(q*P+n+i.val)-(q*P)<n := by omega
  have inside:=i.isLt
  change mounted _ _ _ _ _ _ _ _ _ _ _ _ _ m (((base+q*P)+n)+i.val)=_
  rw [show ((base+q*P)+n)+i.val=base+((q*P+n)+i.val) by omega]
  apply Eq.trans (DescentStaticWordColumn.read base _ _ m (show q*P+n+i.val<size (fields r D p) K H G M unit by
    change _ < (q*P+n)+_;omega))
  apply congrArg (fun v : ℕ=>(v:Word w))
  change (if _h : (q*P+n+i.val)/P<q then _ else _)=_
  dsimp only [q, P, n] at beyond middle ⊢
  simp only [dite_eq_right beyond, dite_eq_right middle, Nat.add_sub_cancel_left, dite_eq_left inside]

theorem cheap (s : Shape) (d r D p B K H G M R unit w base : ℕ) :
    CheapCode (program s d r D p B K H G M R unit w base) := by
  unfold program
  generalize size (fields r D p) K H G M unit=n
  induction n with
  | zero=>exact @scan_cheap _ _ _ _
  | succ n ih=>exact cheap_seq ih (@scan_cheap _ _ _ _)

end
end Hierarchy.DescentPacking.PackedMatch.Local.Gather.ROM

end OAI
