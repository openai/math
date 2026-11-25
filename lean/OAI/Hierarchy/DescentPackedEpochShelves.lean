import OAI.Hierarchy.DescentEpochVoteHeader
import OAI.Hierarchy.DescentPackedEpochAdmission
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! # Consecutive compact selector shelves share one fixed profile dictionary -/
namespace Hierarchy.DescentPackedEpochShelves
open DescentTerminalEpochChart DescentPackedProfileTape DescentPackedProfileValidity DescentPackedProfileInstall
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {A : Type} {w : ℕ}

theorem raw_reads (r lo j : ℕ) (z : A→Bool) (ss : List (Source A)) (s : Shelf A) (mem : s∈shelves r lo j ss)
    (m : Memory w) :
    (∀i : Fin (slots s.src.seats r),rawTape r z lo ss m (s.base+i.val)=((packed s.src.pin z r i.val).val:Word w)) ∧
    (∀i : Fin (slots s.src.seats r),rawTape r z lo ss m ((startsBank s.base s.src.seats r).base+i.val)=(startsWord r i.val:Word w)) := by
  induction ss generalizing lo j m with
  | nil=>simp [shelves] at mem
  | cons a ss ih=>
    rcases List.mem_cons.mp mem with eqn|later
    · subst s
      let n:=slots a.seats r
      let st:=(startsBank lo a.seats r).base
      have bound : n ≤ (sourceBank lo a.seats r).size:=Nat.le_pow_clog (by decide) _
      have b : lo+n ≤ st:=Nat.add_le_add_left bound _
      have c : st+n ≤ lo+space r a:=(Nat.add_le_add_left bound st).trans_eq (next lo r a)
      change (∀i : Fin n,rawTape r z (lo+space r a) ss (prepare lo r a.pin z m) (lo+i.val)=_) ∧
        (∀i : Fin n,rawTape r z (lo+space r a) ss (prepare lo r a.pin z m) (st+i.val)=_)
      constructor <;> intro i <;> have len:=i.isLt
      · rw [raw_low r z _ ss _ (by omega)]
        have early : lo+i.val<(startsBank lo a.seats r).base := (Nat.add_lt_add_left i.isLt lo).trans_le b
        have outside : ¬((startsBank lo a.seats r).base≤lo+i.val ∧
            lo+i.val<(startsBank lo a.seats r).base+slots a.seats r) := fun hit=>(Nat.not_le_of_gt early) hit.1
        simpa only [prepare,fillSegment,ite_eq_right outside] using (at_word a.pin z w lo r m i.isLt)
      · rw [raw_low r z _ ss _ (by omega)]
        have inside : (startsBank lo a.seats r).base≤(startsBank lo a.seats r).base+i.val ∧
            (startsBank lo a.seats r).base+i.val<(startsBank lo a.seats r).base+slots a.seats r :=
          ⟨Nat.le_add_right _ _,Nat.add_lt_add_left i.isLt _⟩
        simp only [st,prepare,fillSegment,ite_eq_left inside,Nat.add_sub_cancel_left]
    · exact ih _ _ later _

def stageBanks (table C r : ℕ) (s : Shelf A) (count : ℕ) :=
  banks table C r (sourceBank s.base s.src.seats r) (startsBank s.base s.src.seats r) ⟨count,0⟩

theorem stored (lo C r : ℕ) (ss : List (Source A)) (z : A→Bool) (m : Memory w)
    (same : DescentTerminalEpochDecoder.Uniform C ss) (s : Shelf A) (mem : s∈shelves r lo 0 ss) (count : ℕ) :
    Reads (stageBanks (lo+extent r ss) C r s count) (header lo C r ss z m) s.src.pin z r := by
  have belong : s.src∈ss := sources r lo 0 ss ▸ List.mem_map_of_mem (f:=Shelf.src) mem
  have uniform:=same s.src belong
  subst C
  have end_:=((next s.base r s.src).trans_le (placed r lo 0 ss s mem).2)
  let st:=(startsBank s.base s.src.seats r).base
  have b:=Nat.le_pow_clog (by decide : 1 < 2) (slots s.src.seats r)
  have gap : s.base+slots s.src.seats r ≤ st:=Nat.add_le_add_left b _
  have hold : st+slots s.src.seats r ≤ tablesBase s.base s.src.seats r:=Nat.add_le_add_left b st
  obtain ⟨words,starts_⟩:=raw_reads r lo 0 z ss s mem m
  have dirEnd : st+slots s.src.seats r ≤ lo+extent r ss := hold.trans end_
  exact inputs (lo+extent r ss) r (sourceBank s.base s.src.seats r) (startsBank s.base s.src.seats r)
    ⟨count,0⟩ s.src.pin z (rawTape r z lo ss m) (gap.trans ((Nat.le_add_right _ _).trans dirEnd)) dirEnd words starts_

end
end Hierarchy.DescentPackedEpochShelves

end OAI
