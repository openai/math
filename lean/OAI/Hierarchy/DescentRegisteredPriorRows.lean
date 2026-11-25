import OAI.Hierarchy.DescentPriorPadWordTariff
import OAI.Hierarchy.DescentOrdinaryRoleHostPadPrice

namespace OAI
/-! # Paying the actual preceding row when a whole group fits in one operand word -/
namespace Hierarchy
open DescentSIMDLookup DescentStaticWordColumn
namespace DescentOrdinaryPriorRetile
noncomputable section
variable (l : DescentDatedPriorOperand.Layout) (lanes base prior w h ratio u₀ u₁ : ℕ)

theorem word_rows (old : 0<l.lanes) (new : 0<lanes) (live : 0<l.hosts)
    (inCap : l.lanes≤h) (outCap : lanes≤h) (short : digits l*l.lanes≤h/2)
    (inFill : l.hosts*chunks l.groups l.lanes*h≤l.hosts*h+l.hosts*l.groups*u₀) (outFill : h≤lanes*u₁) (bus : w≤ratio*h) :
    let p:=phase l lanes base prior w
    (p.ticks+7*names p.program)*w≤
      4096*ratio*(pages l+1)*(h+3*l.hosts*h+l.hosts*l.groups*(2*u₀+u₁))+
      (4096*ratio)*(2*(h+1)^2*2^(h/2))*h :=
  Overlap.page_word_rows l.hosts l.groups l.lanes lanes (digits l) (pages l) h w ratio u₀ u₁ _ live inCap outCap short inFill outFill bus (shared_fee l lanes base prior w old new)
end
end DescentOrdinaryPriorRetile

namespace DescentOrdinaryRoleRetile.Layout
noncomputable section
variable (L : Layout) (base : ℕ) (prior : Fin L.blocks→ProtocolRAM.Bank) (w h ratio u₀ u₁ : ℕ)
theorem word_rows (old : 0<L.beforeLanes) (new : 0<L.afterLanes) (live : 0<L.hosts)
    (inCap : L.beforeLanes≤h) (outCap : L.afterLanes≤h) (short : L.bits*L.beforeLanes≤h/2)
    (inFill : L.hosts*chunks L.groups L.beforeLanes*h≤L.hosts*h+L.hosts*L.groups*u₀) (outFill : h≤L.afterLanes*u₁) (bus : w≤ratio*h) :
    let p:=L.phase base prior w
    (p.ticks+7*names p.program)*w≤
      4096*ratio*(L.blocks+1)*(h+3*L.hosts*h+L.hosts*L.groups*(2*u₀+u₁))+
      (4096*ratio)*(2*(h+1)^2*2^(h/2))*h :=
  Overlap.page_word_rows L.hosts L.groups L.beforeLanes L.afterLanes L.bits L.blocks h w ratio u₀ u₁ _ live inCap outCap short inFill outFill bus (shared_fee L base prior w old new)
end
end DescentOrdinaryRoleRetile.Layout
end Hierarchy

namespace Hierarchy.DescentOrdinaryPriorPad
open DescentSixParty.Chronology DescentDatedPriorOperand DescentSIMDLookup DescentDatedSeedStartup
open DescentStaticWordColumn
noncomputable section
variable (l : Layout) (currentH lanes base prior w h ratio u₀ u₁ : ℕ)

theorem padded_word_rows (old : 0<l.lanes) (new_ : 0<lanes) (live : 0<l.hosts)
    (inCap : l.lanes≤h) (outCap : lanes≤h) (short : DescentOrdinaryPriorRetile.digits l*l.lanes≤h/2)
    (inFill : l.hosts*chunks l.groups l.lanes*h≤l.hosts*h+l.hosts*l.groups*u₀) (outFill : h≤lanes*u₁) (bus : w≤ratio*h) :
    let pages:=DescentOrdinaryPriorRetile.pages l
    (phase l currentH lanes base prior w).wordInvoice≤
      4096*ratio*(pages+1)*(h+3*l.hosts*h+l.hosts*l.groups*(2*u₀+u₁))+
      (4096*ratio)*(2*(h+1)^2*2^(h/2))*h+
      512*ratio*(pages+1)*(h+currentH*h+currentH*l.groups*u₁) :=by
  intro count
  have before:=DescentOrdinaryPriorRetile.word_rows l lanes base prior w h ratio u₀ u₁
    old new_ live inCap outCap short inFill outFill bus
  have ext:=extension_fee l currentH lanes base w
  have rounded:=chunk_work currentH l.groups lanes h u₁ outFill
  have copy : (extension l currentH lanes base w).wordInvoice≤512*ratio*(count+1)*(h+currentH*h+currentH*l.groups*u₁) :=by
    refine (Nat.mul_le_mul ext bus).trans ?_
    calc
      _=512*ratio*(count+1)*(h+(currentH*chunks l.groups lanes)*h) :=by unfold rows;ring
      _≤_ :=by rw [Nat.add_assoc h];gcongr
  exact (NativePhase.wordInvoice_seq ..).le.trans (Nat.add_le_add before copy)

end
end Hierarchy.DescentOrdinaryPriorPad

namespace Hierarchy.DescentOrdinaryRoleHostPad.Layout
open DescentSIMDLookup DescentStaticWordColumn
noncomputable section
variable (L : Layout) (base : ℕ) (prior : Fin L.blocks→ProtocolRAM.Bank) (w h ratio u₀ u₁ : ℕ)
theorem word_rows (old : 0<L.beforeLanes) (new : 0<L.afterLanes) (live : 0<L.oldHosts)
    (inCap : L.beforeLanes≤h) (outCap : L.afterLanes≤h) (short : L.bits*L.beforeLanes≤h/2)
    (inFill : L.oldHosts*chunks L.groups L.beforeLanes*h≤L.oldHosts*h+L.oldHosts*L.groups*u₀) (outFill : h≤L.afterLanes*u₁) (bus : w≤ratio*h) :
    let p:=L.phase base prior w
    (p.ticks+7*names p.program)*w≤
      (4096*ratio*(L.blocks+1)*(h+3*L.oldHosts*h+L.oldHosts*L.groups*(2*u₀+u₁))+
        (4096*ratio)*(2*(h+1)^2*2^(h/2))*h)+
      512*ratio*(L.blocks+1)*(h+L.hosts*h+L.hosts*L.groups*u₁):=by
  have one:=L.retile.word_rows base prior w h ratio u₀ u₁ old new live inCap outCap short inFill outFill bus
  have two:=L.rect.fee (L.split base) (L.retile.bank base) w
  have dense:=DescentDatedSeedStartup.chunk_work L.hosts L.groups L.afterLanes h u₁ outFill
  let q:=L.rect.phase (L.split base) (L.retile.bank base) w
  let earlier:=L.retile.phase base prior w
  have local_ : (q.ticks+7*names q.program)*w≤512*ratio*(L.blocks+1)*(h+L.hosts*h+L.hosts*L.groups*u₁):=by
    calc _ ≤ (512*(L.blocks+1)*(L.rows+1))*(ratio*h):=Nat.mul_le_mul two bus
         _=512*ratio*(L.blocks+1)*(h+L.rows*h):=by ring
         _≤_:=Nat.mul_le_mul_left _ (by unfold rows; omega)
  change (earlier.ticks+q.ticks+7*names (earlier.program.seq q.program))*w≤_
  rw [names_seq]
  calc _=(earlier.ticks+7*names earlier.program)*w+(q.ticks+7*names q.program)*w:=by ring
       _≤_:=Nat.add_le_add one local_

end
end Hierarchy.DescentOrdinaryRoleHostPad.Layout

end OAI
