import OAI.Hierarchy.DescentOriginalEpochSheetCharge
import OAI.Hierarchy.DescentEpochVoteHeader
import OAI.Hierarchy.DescentPackedEpochShelfLayout
import OAI.Hierarchy.DescentPackedProfileValidity
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! # Shared literal advice for the packed epoch check -/
namespace Hierarchy.DescentPackedProfileInstall
open DescentPackedProfileValidity DescentPackedProfileTape DescentSIMDLookup
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

theorem after {W : ℕ} (lo C grain : ℕ) (m : Memory W) {a : ℕ} (high : end_ lo C grain ≤ a) :
    install lo C grain m a=m a := by
  have base : lo ≤ end_ lo C grain := by dsimp [end_,dict];omega
  simp [install,fillSegment,show ¬(lo ≤ a ∧ a < lo+(end_ lo C grain-lo)) by omega]

theorem shift_at {W : ℕ} (lo C grain : ℕ) (m : Memory W) {j : ℕ} (inside : j ≤ grain) :
    install lo C grain m ((shifts lo grain).base+j)=(bankShift C grain j:Word W) := by
  have hs:=DescentDyadicSpan.span_ge (grain+1)
  change grain+1 ≤ (shifts lo grain).size at hs
  have head : lo+j < (dict lo C grain).base := by change lo+j < lo+(shifts lo grain).size;omega
  have e : (dict lo C grain).base ≤ end_ lo C grain := Nat.le_add_right _ _
  change install lo C grain m (lo+j)=_
  simp [install,fillSegment,advice,head,show lo+j < lo+(end_ lo C grain-lo) by omega]

theorem dict_at {W : ℕ} (lo C grain : ℕ) (m : Memory W) {j : ℕ} (inside : j ≤ grain)
    (key : Cell (DescentTerminalEpochBits.width C*grain)) :
    install lo C grain m ((dict lo C grain).base+(bankShift C grain j+key.val))=(bad C grain j key:Word W) := by
  let L:=2^(DescentTerminalEpochBits.width C*grain)
  let d:=(dict lo C grain).base
  let a:=bankShift C grain j+key.val
  have width_ : tariff C grain ≤ (dict lo C grain).size := Nat.le_pow_clog (by decide) _
  have le:=Nat.mul_le_mul_right L inside
  have kw : key.val < L:=key.isLt
  have fits : a < (dict lo C grain).size := by
    apply Nat.lt_of_lt_of_le _ width_
    change j*L+key.val < (grain+1)*L
    rw [Nat.add_mul,Nat.one_mul];omega
  have prior : lo ≤ d := by change lo ≤ lo+_;omega
  have next : d+a < end_ lo C grain := Nat.add_lt_add_left fits d
  have div_ : a/L=j := by
    change (j*L+key.val)/L=j
    rw [Nat.mul_comm j L, Nat.mul_add_div (show 0 < L from Nat.two_pow_pos _) j key.val,
      Nat.div_eq_of_lt kw, Nat.add_zero]
  have mod_ : a%L=key.val := by
    change (j*L+key.val)%L=key.val
    simp [Nat.add_mod,Nat.mod_eq_of_lt kw]
  have skip : ¬ d+a < (dict lo C grain).base := by change ¬ d+a < d; omega
  have offset : d+a-(dict lo C grain).base = a := by change d+a-d = a; omega
  change install lo C grain m (d+a)=_
  simp only [install,fillSegment,ite_eq_left (show lo ≤ d+a ∧ d+a < lo+(end_ lo C grain-lo) by omega),
    advice,ite_eq_right skip,offset]
  change (bad C grain (a/L) ⟨a%L,_⟩:Word W)=(bad C grain j key:Word W)
  rw [div_]
  exact congrArg (fun x=>(bad C grain j x:Word W)) (Fin.ext mod_)

/-- Native source and fixed row starts may occupy arbitrary disjoint columns.
The shared dictionary and shifts have their actual compiler-selected bases. -/
def banks (rom C grain : ℕ) (source starts count : Bank) : DescentPackedProfileValidity.Banks :=
  ⟨source,starts,shifts rom grain,dict rom C grain,count⟩

theorem inputs {A : Type} {C seats W : ℕ} (base grain : ℕ) (source starts count : Bank)
    (pin : DescentTerminalEpochBits.Pins C seats→A) (z : A→Bool) (old : Memory W)
    (sourceLow : source.base+slots seats grain ≤ base) (startsLow : starts.base+slots seats grain ≤ base)
    (loaded : ∀i : Fin (slots seats grain),old (source.base+i.val)=((packed pin z grain i.val).val:Word W))
    (directory : ∀i : Fin (slots seats grain),old (starts.base+i.val)=(startsWord grain i.val:Word W)) :
    Reads (banks base C grain source starts count) (install base C grain old) pin z grain := by
  refine ⟨?_,?_,fun _ h=>shift_at base C grain old h,fun _ h key=>dict_at base C grain old h key⟩
  · intro i
    exact (before base C grain old (a:=source.base+i.val) (by have := i.isLt;omega)).trans (loaded i)
  · intro i
    exact (before base C grain old (a:=starts.base+i.val) (by have := i.isLt;omega)).trans (directory i)

def initial {A : Type} {C seats W : ℕ} (lo grain : ℕ) (pin : DescentTerminalEpochBits.Pins C seats→A)
    (z : A→Bool) (old : Memory W) := install (tablesBase lo seats grain) C grain (prepare lo grain pin z old)

def actual (lo count C seats grain : ℕ) :=
  banks (tablesBase lo seats grain) C grain (sourceBank lo seats grain) (startsBank lo seats grain) ⟨count,0⟩

theorem actual_inputs {A : Type} {C seats W : ℕ} (lo grain addr : ℕ)
    (pin : DescentTerminalEpochBits.Pins C seats→A) (z : A→Bool) (old : Memory W) :
    Reads (actual lo addr C seats grain) (initial lo grain pin z old) pin z grain := by
  have size : slots seats grain ≤ (sourceBank lo seats grain).size :=
    Nat.le_pow_clog (by decide : 1 < 2) _
  have loStart : lo+slots seats grain ≤ (startsBank lo seats grain).base :=
    Nat.add_le_add_left size lo
  have dirEnd : (startsBank lo seats grain).base+slots seats grain ≤ tablesBase lo seats grain :=
    Nat.add_le_add_left size _
  refine inputs (tablesBase lo seats grain) grain (sourceBank lo seats grain)
    (startsBank lo seats grain) ⟨addr,0⟩ pin z (prepare lo grain pin z old) ?_ dirEnd ?_ ?_
  · exact loStart.trans ((Nat.le_add_right _ _).trans dirEnd)
  · intro i
    have early := (Nat.add_lt_add_left i.isLt lo).trans_le loStart
    have outside : ¬ ((startsBank lo seats grain).base ≤ lo+i.val ∧
        lo+i.val < (startsBank lo seats grain).base+slots seats grain) :=
      fun hit => (Nat.not_le_of_gt early) hit.1
    change prepare lo grain pin z old (lo+i.val)=_
    simpa only [prepare,fillSegment,ite_eq_right outside] using
      (DescentPackedProfileTape.at_word pin z W lo grain old i.isLt)
  · intro i
    have inside : (startsBank lo seats grain).base ≤ (startsBank lo seats grain).base+i.val ∧
        (startsBank lo seats grain).base+i.val < (startsBank lo seats grain).base+slots seats grain :=
      ⟨Nat.le_add_right _ _, Nat.add_lt_add_left i.isLt _⟩
    simp only [prepare,fillSegment,ite_eq_left inside,Nat.add_sub_cancel_left]

theorem initial_lower {A : Type} {C seats W : ℕ} (lo grain : ℕ)
    (pin : DescentTerminalEpochBits.Pins C seats→A) (z : A→Bool) (old : Memory W)
    {a : ℕ} (low : a < lo) : initial lo grain pin z old a=old a := by
  have h : lo ≤ (startsBank lo seats grain).base := Nat.le_add_right _ _
  have hh : (startsBank lo seats grain).base ≤ tablesBase lo seats grain := Nat.le_add_right _ _
  exact (before (tablesBase lo seats grain) C grain (prepare lo grain pin z old)
    (low.trans_le (h.trans hh))).trans
    (DescentPackedEpochShelves.prepare_low grain lo ⟨C,seats,pin⟩ z old low)

theorem actual_room (lo addr C seats W grain dst : ℕ) (countLow : addr < lo)
    (after_ : end_ (tablesBase lo seats grain) C grain ≤ dst)
    (laneFit : slots seats grain*grain < 2^W) (outFit : dst+(slots seats grain+1) < 2^W) :
    Room (actual lo addr C seats grain) W C seats grain dst := by
  let src:=sourceBank lo seats grain
  let st:=startsBank lo seats grain
  let base:=tablesBase lo seats grain
  let sh:=shifts base grain
  let tab:=dict base C grain
  have a : src.base+src.size=st.base:=rfl
  have b : st.base+st.size=base:=rfl
  have c : sh.base=base:=rfl
  have d : base+sh.size=tab.base:=rfl
  have e : tab.base+tab.size ≤ dst:=after_
  have f : src.base=lo:=rfl
  have fits (v : Bank) (before : v.base+v.size ≤ dst) : v.Fits W dst:=
    ⟨Nat.two_pow_pos _,by omega,before⟩
  exact ⟨fits src (by omega),fits st (by omega),fits sh (by omega),fits tab e,
    fits ⟨addr,0⟩ (by change addr+1 ≤ dst;omega),
    Nat.le_pow_clog (by decide : 1 < 2) (slots seats grain),
    Nat.le_pow_clog (by decide : 1 < 2) (slots seats grain),
    Nat.le_pow_clog (by decide : 1 < 2) (grain+1),
    Nat.le_pow_clog (by decide : 1 < 2) (tariff C grain),laneFit,outFit⟩

theorem check {A : Type} {C seats W : ℕ} (lo grain addr dst : ℕ)
    (pin : DescentTerminalEpochBits.Pins C seats→A) (z : A→Bool) (old : Memory W)
    (pos : 0 < grain) (countLow : addr < lo)
    (after_ : end_ (tablesBase lo seats grain) C grain ≤ dst)
    (laneFit : slots seats grain*grain < 2^W) (outFit : dst+(slots seats grain+1) < 2^W) :
    let b:=actual lo addr C seats grain
    let m:=initial lo grain pin z old
    (proc b W grain seats dst).Spec (·=m) (fun _ o =>
      (o (dst+slots seats grain)=if ∀i : Fin seats,DescentTerminalEpochFlags.SeatValid C (old addr).val
        (DescentTerminalEpochBits.raw (z∘pin) i) i.val then 0 else 1) ∧
      ∀a,a < dst ∨ dst+(slots seats grain+1) ≤ a → o a=m a) (fee b grain seats) ∧
      CheapCode (proc b W grain seats dst) := by
  let b:=actual lo addr C seats grain
  let m:=initial lo grain pin z old
  have count_ : m b.count.base=old addr:=initial_lower lo grain pin z old countLow
  have checked:=run b pin z grain dst m (actual_room lo addr C seats W grain dst countLow after_ laneFit outFit)
    (actual_inputs lo grain addr pin z old) pos
  simpa only [count_] using checked

end
end Hierarchy.DescentPackedProfileInstall

end OAI
