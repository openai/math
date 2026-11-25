import OAI.Hierarchy.DescentPackedSixBirths
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! # Actual fixed stores for the shared six-party birth lookup -/
namespace Hierarchy.DescentPacking.PackedMatch.SixBirths
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

def mountedBanks (s : Shape) (M base : ℕ) (old normalized : Bank) : Banks :=
  ⟨old,normalized,⟨base,profiles s M⟩,⟨base+2^(profiles s M),profiles s M+topology s M⟩⟩

def literal (s : Shape) (M j : ℕ) :=
  if j<2^(profiles s M) then 2^(topology s M)*j
  else controlWord s M (cut (profiles s M+topology s M) (j-2^(profiles s M)))

def entries (s : Shape) (M : ℕ) := 2^(profiles s M)+2^(profiles s M+topology s M)

def mount (s : Shape) (M base w : ℕ) := DescentStaticWordColumn.program w base (literal s M) (entries s M)
def mounted (s : Shape) (M base : ℕ) {w : ℕ} (m : Memory w) :=
  DescentStaticWordColumn.image base (literal s M) m (entries s M)

private theorem cheap (w base : ℕ) (x : ℕ→ℕ) (n : ℕ) : CheapCode (DescentStaticWordColumn.program w base x n) := by
  induction n with
  | zero=>exact @scan_cheap _ _ _ _
  | succ n ih=>exact cheap_seq ih (@scan_cheap _ _ _ _)

theorem mount_read (s : Shape) (M base w : ℕ) (old normalized : Bank)
    (mem : Memory w) (space : base+entries s M<2^w) :
    (mount s M base w).Exec mem (mounted s M base mem) (4+10*entries s M) ∧
    Static s M (mountedBanks s M base old normalized) (mounted s M base mem) ∧
    (∀a<base,mounted s M base mem a=mem a) ∧ CheapCode (mount s M base w) := by
  refine ⟨DescentStaticWordColumn.mount _ _ _ _ space,⟨?_,?_⟩,
    fun a ha=>DescentStaticWordColumn.frame _ _ _ _ _ (.inl ha),@cheap w base (literal s M) (entries s M)⟩
  · intro i
    have inside : i.val<entries s M:=i.isLt.trans_le (Nat.le_add_right ..)
    calc
      _ = (literal s M i.val : Word w) :=
        DescentStaticWordColumn.read base (entries s M) (literal s M) mem inside
      _ = _ := congrArg (fun value : ℕ => (value : Word w))
        (show literal s M i.val = 2^(topology s M)*i.val from ite_eq_left i.isLt)
  · intro i
    have inside : 2^(profiles s M)+i.val<entries s M:=Nat.add_lt_add_left i.isLt _
    rw [show (mountedBanks s M base old normalized).table.base+i.val=base+(2^(profiles s M)+i.val) by simp [mountedBanks,Nat.add_assoc]]
    rw [mounted,DescentStaticWordColumn.read _ _ _ _ inside]
    simp [literal,cut,Nat.mod_eq_of_lt i.isLt]

theorem fresh (s : Shape) (M n base out w : ℕ) (old normalized : Bank)
    (fit : Room s M n out w (mountedBanks s M base old normalized))
    (early : old.base+n≤base ∧ normalized.base+n≤base)
    (m : Memory w) (keys : Fin n→Cell (topology s M)) (issued : ∀i : Fin n,m (old.base+i.val)=((keys i).val:ℕ)) :
    let g:=mountedBanks s M base old normalized
    let p:=mounted s M base m
    let result:=after g n out p
    ((mount s M base w).seq (program g n out w)).Exec m result ((4+10*entries s M)+(4+54*n)) ∧
    (∀i : Fin n,∀a : Fin M,∀j : Fin s.pairs,∀q : Fin 6,
      digit (s.digit+1) (slot a j q).val (result (out+i.val)).val=
        if j.val<(laneCounts s M (keys i) a).val then digit s.digit (finProdFinEquiv (a,j)).val (m (normalized.base+i.val)).val+1 else 0) ∧
    CheapCode ((mount s M base w).seq (program g n out w)) := by
  let g:=mountedBanks s M base old normalized
  have space : base+entries s M<2^w:=by
    have fitTable:=fit.table.2.2
    change base+2^(profiles s M)+2^(profiles s M+topology s M)≤out at fitTable
    unfold entries
    have := fit.output
    omega
  obtain ⟨pre,load,low,preCheap⟩:=mount_read s M base w old normalized m space
  obtain ⟨scan,cheapCode⟩:=run s M n out w g fit (mounted s M base m)
  have retained (i : Fin n) : mounted s M base m (g.original.base+i.val)=((keys i).val:ℕ) :=
    (low _ ((Nat.add_lt_add_left i.isLt _).trans_le early.1)).trans (issued i)
  refine ⟨pre.then scan,?_,cheap_seq preCheap cheapCode⟩
  intro i a j q
  rw [fields s M n out w g fit _ load keys retained i a j q]
  have save:=low _ ((Nat.add_lt_add_left i.isLt _).trans_le early.2)
  simpa [g,mountedBanks] using congrArg (fun t : Word w=>if j.val<(laneCounts s M (keys i) a).val then
    digit s.digit (finProdFinEquiv (a,j)).val t.val+1 else 0) save

theorem fresh_bound (s : Shape) (M n base out w : ℕ) (original normalized : Bank)
    (fit : Room s M n out w (mountedBanks s M base original normalized))
    (early : original.base+n≤base ∧ normalized.base+n≤base)
    (m : Memory w) (keys : Fin n→Cell (topology s M)) (issued : ∀i : Fin n,m (original.base+i.val)=((keys i).val:ℕ)) :
    let g:=mountedBanks s M base original normalized
    ∀i : Fin n,(after g n out (mounted s M base m) (out+i.val)).val<2^width s M := by
  intro g i
  have space : base+entries s M<2^w:=by
    have table:=fit.table.2.2
    change base+2^(profiles s M)+2^(profiles s M+topology s M)≤out at table
    unfold entries
    have :=fit.output
    omega
  obtain ⟨_,printed,low,_⟩:=mount_read s M base w original normalized m space
  have saved (j : Fin n) : mounted s M base m (g.original.base+j.val)=((keys j).val:ℕ) :=
    (low _ ((Nat.add_lt_add_left j.isLt _).trans_le early.1)).trans (issued j)
  rw [word_read s M n out w g fit _ printed keys saved]
  exact Fin.isLt _

theorem mount_size (s : Shape) (M w : ℕ) (room : profiles s M+topology s M≤w/2) :
    entries s M≤2*2^(w/2) := by
  have first : 2^(profiles s M)≤2^(w/2):=Nat.pow_le_pow_right (by decide) (by omega)
  have last:=Nat.pow_le_pow_right (by decide : 0<2) room
  unfold entries;omega

def tapeBank (base n : ℕ) : Bank:=⟨base,Nat.clog 2 n⟩
def tableStart (old normalized : Bank) := max (old.base+old.size) (normalized.base+normalized.size)
def outputBase (s : Shape) (M : ℕ) (old normalized : Bank) := tableStart old normalized+entries s M

theorem placed (s : Shape) (M n w : ℕ) (old normalized : Bank) (ca : n≤old.size) (cb : n≤normalized.size)
    (widthFit : width s M≤w) (space : outputBase s M old normalized+n<2^w) :
    let base:=tableStart old normalized
    Room s M n (outputBase s M old normalized) w (mountedBanks s M base old normalized) ∧
      old.base+n≤base ∧ normalized.base+n≤base := by
  let base:=tableStart old normalized
  let out:=outputBase s M old normalized
  have one : old.base+old.size≤base:=le_max_left ..
  have two : normalized.base+normalized.size≤base:=le_max_right ..
  have A:=Nat.two_pow_pos (profiles s M)
  have B:=Nat.two_pow_pos (profiles s M+topology s M)
  change (base+(2^(profiles s M)+2^(profiles s M+topology s M)))+n<2^w at space
  have bank {x : Bank} (endAt : x.base+x.size≤out) : x.Fits w out := by
    refine ⟨Nat.two_pow_pos _,?_,endAt⟩
    change x.base+x.size≤base+(2^(profiles s M)+2^(profiles s M+topology s M)) at endAt
    omega
  refine ⟨⟨bank ?_,bank ?_,bank ?_,bank ?_,ca,cb,rfl,rfl,widthFit,space⟩,by omega,by omega⟩
  · change old.base+old.size≤base+(2^(profiles s M)+2^(profiles s M+topology s M));omega
  · change normalized.base+normalized.size≤base+(2^(profiles s M)+2^(profiles s M+topology s M));omega
  · change base+2^(profiles s M)≤base+(2^(profiles s M)+2^(profiles s M+topology s M));omega
  · change base+2^(profiles s M)+2^(profiles s M+topology s M)≤base+(2^(profiles s M)+2^(profiles s M+topology s M));omega

theorem control (s : Shape) (M base n out w : ℕ) (g : Banks) :
    let cpu:=(mount s M base w).seq (program g n out w)
    cpu.labels+cpu.registers+cpu.slots=126+15*entries s M := by
  change DescentStaticWordColumn.names _=_
  simp only [DescentStaticWordColumn.names_seq,mount,DescentStaticWordColumn.names_mount,program,
    DescentStaticWordColumn.names_scan,show (expr g).work=25 by rfl]
  omega

end
end Hierarchy.DescentPacking.PackedMatch.SixBirths

end OAI
