import OAI.Hierarchy.ProtocolRAMCalendarPrefixLayout
import OAI.Hierarchy.ProtocolRAMReserveUse

namespace OAI
/-! # Native cumulative reserve debits in a permanent page for every date -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.PrefixReserve
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped BigOperators Classical Fin.CommRing

variable {W count N : ℕ}

def banks (L : PrefixWidths.Layout count) (old : RouteSettlement.Banks) (j : ℕ) :
    RouteSettlement.Banks := {old with reserved := L.bank (2*j), used := L.bank (2*j+1)}

def «prefix» {A : Type} (size : Fin (N+1)) (f : Fin N→A) (i : Fin size.val) : A :=
  f (Fin.castLE (Nat.le_of_lt_succ size.isLt) i)

/-- Original immutable tagged archive, with logical owner and amount indexed by the
whole ordered history. Every shorter dated replay reads literal initial rows of it. -/
structure Directory (a : ReserveUse.Archive) (site : Fin N→Fin count) (debit : Fin N→ℕ)
    (m : Memory W) : Prop where
  kind : ∀i : Fin N,a.kind.read m ((2*i.val:ℕ):Word W)=0 ∧ a.kind.read m ((2*i.val+1:ℕ):Word W)≠0
  owner : ∀i : Fin N,a.history.read m (a.pointer.read m ((2*i.val:ℕ):Word W))=((site i).val:Word W)
  amount : ∀i : Fin N,a.history.read m (a.pointer.read m ((2*i.val+1:ℕ):Word W))=(debit i:Word W)

variable (L : PrefixWidths.Layout count) (old : RouteSettlement.Banks) (a : ReserveUse.Archive)
    (size : ℕ→Fin (N+1)) (reserve : ℕ)

def program (W : ℕ) : ℕ→Procedure W
  | 0 => ReserveUse.native W a (banks L old 0) count (size 0).val reserve
  | j+1 => (program W j).seq (ReserveUse.native W a (banks L old (j+1)) count (size (j+1)).val reserve)

def image (site : Fin N→Fin count) (debit : Fin N→ℕ) (m : Memory W) : ℕ→Memory W
  | 0 => ReserveUse.output a (banks L old 0) reserve («prefix» (size 0) site) («prefix» (size 0) debit) m
  | j+1 => ReserveUse.output a (banks L old (j+1)) reserve («prefix» (size (j+1)) site)
      («prefix» (size (j+1)) debit) (image site debit m j)

def cost (count : ℕ) (size : ℕ→Fin (N+1)) : ℕ→ℕ
  | 0 => 19+12*count+160*(size 0).val
  | j+1 => cost count size j+(19+12*count+160*(size (j+1)).val)

def used (site : Fin N→Fin count) (debit : Fin N→ℕ) (n : Fin (N+1)) (v : Fin count) : ℕ :=
  ∑ i : Fin n.val, if «prefix» n site i=v then «prefix» n debit i else 0

theorem cost_le (last : ℕ) : cost count size last≤(last+1)*(19+12*count+160*N) := by
  induction last with
  | zero =>
    have lim := (size 0).isLt
    simp only [cost]
    omega
  | succ j ih =>
    have lim := (size (j+1)).isLt
    exact (Nat.add_le_add ih (by omega : 19+12*count+160*(size (j+1)).val≤19+12*count+160*N)).trans_eq
      (Nat.succ_mul (j+1) _).symm

set_option maxHeartbeats 1600000 in
theorem cheap (last : ℕ) : CheapCode (program L old a size reserve W last) := by
  induction last with
  | zero => exact @ReserveUse.cheap W a (banks L old 0) count (size 0).val reserve
  | succ j ih =>
    exact @cheap_seq W (program L old a size reserve W j)
      (ReserveUse.native W a (banks L old (j+1)) count (size (j+1)).val reserve) (@ih)
      (@ReserveUse.cheap W a (banks L old (j+1)) count (size (j+1)).val reserve)

structure Ready (m : Memory W) (site : Fin N→Fin count) (debit : Fin N→ℕ) (last : ℕ) : Prop where
  loaded : Directory a site debit m
  archive : ∀j≤last,(ReserveUse.word a (banks L old j)).Fits W L.archive
  temporary : ∀j≤last,(L.bank (2*j+1)).base+count≤a.scratch
  room : a.scratch+2*N<2^W
  wide : reserve<2^W
  funded : ∀ j≤last,∀ i : Fin count,used site debit (size j) i≤reserve

structure Receipt (m : Memory W) (site : Fin N→Fin count) (debit : Fin N→ℕ) (j : ℕ) : Prop where
  ran : (program L old a size reserve W j).Exec m (image L old a size reserve site debit m j) (cost count size j)
  kept : ∀x<L.archive,image L old a size reserve site debit m j x=m x
  read : ∀i≤j,∀v : Fin count,
    let out := image L old a size reserve site debit m j
    (out ((banks L old i).used.base+v.val)).val=used site debit (size i) v ∧
      (out ((banks L old i).reserved.base+v.val)).val=reserve

private theorem one (m u : Memory W) (site : Fin N→Fin count) (debit : Fin N→ℕ) {last : ℕ}
    (ok : Ready L old a size reserve m site debit last) (j : ℕ) (hj : j≤last)
    (same : ∀x<L.archive,u x=m x) :
    let b := banks L old j
    let n := size j
    let out := ReserveUse.output a b reserve («prefix» n site) («prefix» n debit) u
    (ReserveUse.native W a b count n.val reserve).Exec u out (19+12*count+160*n.val) ∧
      (∀x<b.reserved.base,out x=u x) ∧ ∀v : Fin count,
      (out (b.used.base+v.val)).val=used site debit n v ∧ (out (b.reserved.base+v.val)).val=reserve := by
  intro b n out
  have separate : b.reserved.base+count<b.used.base := L.before (Nat.lt_succ_self (2*j))
  have temporary : b.used.base+count≤a.scratch := ok.temporary j hj
  have limit := n.isLt
  have room := ok.room
  have read := ReserveUse.loaded_of_archive a b site debit m ok.loaded.kind ok.loaded.owner ok.loaded.amount
  have mount : ReserveUse.Mounted a b reserve («prefix» n site) («prefix» n debit) u := by
    refine ⟨separate.le,temporary,by omega,ProtocolRAMGeneratedWrite.fits_mono _
      (L.archive_le (2*j)) (ok.archive j hj),?_⟩
    intro i
    have atArchive := read (Fin.castLE (Nat.le_of_lt_succ n.isLt) i)
    exact ⟨(eval_below (ReserveUse.word a b) _ m u (ok.archive j hj) same).trans atArchive.1,
      (eval_below (ReserveUse.word a b) _ m u (ok.archive j hj) same).trans atArchive.2⟩
  refine ⟨?_,?_,?_⟩
  · rw [←ReserveUse.clock_eq a b count n.val reserve]
    exact ReserveUse.exec a b reserve («prefix» n site) («prefix» n debit) u mount
  · intro x hx
    exact ReserveUse.frame a b reserve («prefix» n site) («prefix» n debit) u x (.inl hx)
      (.inl (by omega)) (.inl (by omega))
  · intro v
    have bound : v.val<2^W := by have := v.isLt; omega
    have rem : v.val%(2^L.bits)=v.val := Nat.mod_eq_of_lt (v.isLt.trans_le L.covered)
    have eq := ReserveUse.reported a b reserve («prefix» n site) («prefix» n debit) u mount v
      L.covered L.covered (ok.funded j hj v) ok.wide
    simpa only [out,used,RouteSettlement.actual,Bank.read,Fin.val_cast_of_lt bound,
      show b.used.size=2^L.bits from rfl,show b.reserved.size=2^L.bits from rfl,rem] using eq

theorem replay (m : Memory W) (site : Fin N→Fin count) (debit : Fin N→ℕ) (last : ℕ)
    (valid : Ready L old a size reserve m site debit last) : Receipt L old a size reserve m site debit last := by
  have atDate (j : ℕ) (hj : j≤last) : Receipt L old a size reserve m site debit j := by
    induction j with
    | zero =>
      obtain ⟨run,keep,obs⟩ := one L old a size reserve m m site debit valid 0 hj (fun _ _=>rfl)
      refine ⟨run,fun x hx=>keep x (hx.trans_le (L.archive_le _)),?_⟩
      intro i hi v
      have eq : i=0 := by omega
      subst i
      exact obs v
    | succ j ih =>
      have prev := ih (Nat.le_trans (Nat.le_succ j) hj)
      obtain ⟨run,keep,obs⟩ := one L old a size reserve m _ site debit valid (j+1) hj prev.kept
      refine ⟨Procedure.Exec.then prev.ran run,fun x hx=>(keep x (hx.trans_le (L.archive_le _))).trans (prev.kept x hx),?_⟩
      intro i hi v
      rcases Nat.eq_or_lt_of_le hi with eq | lt
      · subst i
        exact obs v
      · have oldUsed := L.before (show 2*i+1<2*(j+1) by omega)
        have oldReserved := L.before (show 2*i<2*(j+1) by omega)
        have pos := v.isLt
        have u : (banks L old i).used.base+v.val<(banks L old (j+1)).reserved.base := by
          change (L.bank (2*i+1)).base+v.val<(L.bank (2*(j+1))).base
          omega
        have r : (banks L old i).reserved.base+v.val<(banks L old (j+1)).reserved.base := by
          change (L.bank (2*i)).base+v.val<(L.bank (2*(j+1))).base
          omega
        obtain ⟨usedAt,reservedAt⟩ := prev.read i (by omega) v
        exact ⟨(congrArg Fin.val (keep _ u)).trans usedAt,(congrArg Fin.val (keep _ r)).trans reservedAt⟩
  exact atDate last le_rfl

end Hierarchy.ProtocolRAM.Calendar.PrefixReserve

end
end OAI
