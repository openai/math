import OAI.Computability.BorderVNP.TransmissionDeliveryReturns
import OAI.Computability.BorderVNP.TransmissionJointPrivate

/-! # Private site strings, programmed literals and substituted live pins at their actual receivers -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Pins

open VPVNP.BurstRAM

/-- The actual prepared substitution array, including every zero padding position. -/
def SubstitutionAt {w : ℕ} (L : Layout) (guess : ℕ → Bool) (m : Memory w) : Prop :=
  ∀ x < L.count, m (L.ibase+x) = if L.active x then Fin.ofNat _ (guess x).toNat else 0

/-- Recover the substitute array from an actual native pin return. Only the
substitution cells must survive the following public-table writes. -/
theorem substitution_of_return {w : ℕ} (L : Layout) (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (m : Memory w) (s : Bank w) (frame : Frame L (readings pub) (readings m))
    (hframe : readings pub 0+24 < 2^w) (teams : 0 < L.teams) (stride : L.stride < 2^w)
    (count : L.count < 2^w) (width : L.width ≤ L.count) (fits : LoopFits w L) (sep : Separated L)
    (z : Return pub macros s m) (current : Memory w)
    (keep : ∀ x < L.count, current (L.ibase+x) = z.val.2.2 (L.ibase+x)) :
    ∃ b : Fin L.guessWidth → Bool, z.val.1.flatMap TeamRAM.Event.choices = List.ofFn b ∧
      SubstitutionAt L (extendGuess b) current := by
  obtain ⟨E,eff⟩ := preparePins_exact L pub macros m s frame hframe teams stride count width fits
  obtain ⟨b,rfl⟩ := E.surjective z
  refine ⟨b,(eff b).1,fun x hx => ?_⟩
  rw [keep x hx,(eff b).2.2.2.2]
  exact preparedMemory_substitute L (extendGuess b) m sep le_rfl hx

end RoutingISA.Pins

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission RoutingISA.Pins Routing
open Packing.Directory (Row)

variable {R r t d link inner n w : ℕ} {Edge : Type}
variable {G : Wiring R r t d link inner n Edge} {pin : Fin d → Bool}
variable {ext : Exterior R r link → Bool} {wire : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {ib hb sb : Fin (R+1) → ℕ}

local notation "PL" => fun u => G.pinLayout u (ib u) (hb u) (sb u)
local notation "F" => ReturnedDelivery G pin ext wire D pp lp owner origin stride H PL

/-- The physical processor input at a native return's entry, independent of the
three private scratch pointers that the caller uses to interpret the pin layout. -/
theorem ReturnedDelivery.loaded (f : F) (u : Fin (R+1)) :
    (G.processorFields u pin ext (ib u) (hb u) (sb u)).ContainsInput (H u).initial := by
  let A := (f.bank u).initial
  rw [← (f.bank u).memory]
  exact A.physical

/-- A live field-zero bit in the consumer's native memory equals the programmed
literal at the true source processor. -/
theorem ReturnedDelivery.live_literal (f : F) (block : 0 < D.block) (fields : 0 < D.fields)
    (u : Fin (R+1)) (team : Fin D.teams) (tu : team.val = u.val) (p : Fin D.processors) (b : Fin D.literal) :
    let pos := p.val*D.stride+b.val
    let dst := lp (team.val*D.sites+pos/D.block)
    (H (owner dst.1)).history.val.2.2 (origin+dst.1*stride+dst.2+pos%D.block) =
      TeamTapeInputEmit.headerWord w ((G.processorFields u pin ext (ib u) (hb u) (sb u)).literal
        (p.cast (f.dimensions u).1)) b.val := by
  let pos := p.val*D.stride+b.val
  let dst := lp (team.val*D.sites+pos/D.block)
  obtain ⟨row,mem,e,he,ht,hp,hf,ho,hc,hs⟩ := D.live_delivered pp lp team p ⟨0,fields⟩ block b
  simp only [Nat.zero_mul,Nat.add_zero] at hc hs
  change row.cell = dst.1 at hc
  change row.slot+e = dst.2+pos%D.block at hs
  have read := (f.receipt row mem e he u (ht.trans tu)).read
  have addr : row.sourceBase (PL u)+e = p.val*(PL u).stride+b.val := by
    change row.field = 0 at hf
    rw [Row.sourceBase,ite_eq_left hf,Nat.add_assoc,ho,hp]
  rw [addr] at read
  have result := read.trans ((f.loaded u).literal (p.cast (f.dimensions u).1) (b.cast (f.dimensions u).2))
  rw [hc,Nat.add_assoc (origin+dst.1*stride),hs,← Nat.add_assoc (origin+dst.1*stride)] at result
  exact result

/-- The live field-one lane is the guessed substituted index on the active team,
and zero in every clamped slot, after the actual receiver has returned. -/
theorem ReturnedDelivery.live_substitute (f : F) (block : 0 < D.block) (fields : 1 < D.fields)
    (u : Fin (R+1)) (team : Fin D.teams) (tu : team.val = u.val) (p : Fin D.processors) (b : Fin D.literal)
    (guess : ℕ → Bool) (subst : SubstitutionAt (PL u) guess (H u).initial) :
    let pos := p.val*D.stride+(D.literal+(D.teams-1)*D.link)+b.val
    let dst := lp (team.val*D.sites+pos/D.block)
    let x := p.val*D.literal+b.val
    (H (owner dst.1)).history.val.2.2 (origin+dst.1*stride+dst.2+pos%D.block) =
      if (PL u).active x then Fin.ofNat _ (guess x).toNat else 0 := by
  let pos := p.val*D.stride+(D.literal+(D.teams-1)*D.link)+b.val
  let dst := lp (team.val*D.sites+pos/D.block)
  obtain ⟨row,mem,e,he,ht,hp,hf,ho,hc,hs⟩ := D.live_delivered pp lp team p ⟨1,fields⟩ block b
  simp only [Nat.one_mul] at hc hs
  change row.cell = dst.1 at hc
  change row.slot+e = dst.2+pos%D.block at hs
  change row.field = 1 at hf
  have addr : row.sourceBase (PL u)+e = (PL u).ibase+(p.val*D.literal+b.val) := by
    simp only [Row.sourceBase,hf,ite_eq_right (by decide : (1 : ℕ) ≠ 0),Nat.add_assoc,hp,ho,(f.dimensions u).2]
  have read := (f.receipt row mem e he u (ht.trans tu)).read
  rw [addr] at read
  have lim : p.val*D.literal+b.val < (PL u).count := by
    change p.val*D.literal+b.val < (PL u).processors*(PL u).literal
    rw [← (f.dimensions u).1,← (f.dimensions u).2]
    exact (Nat.add_lt_add_left b.isLt _).trans_le ((Nat.succ_mul _ _).symm ▸ Nat.mul_le_mul_right _ p.isLt)
  have result := read.trans (subst _ lim)
  rw [hc,Nat.add_assoc (origin+dst.1*stride),hs,← Nat.add_assoc (origin+dst.1*stride)] at result
  exact result

end TeamContraction

end BorderVNP
end Computability
end OAI
