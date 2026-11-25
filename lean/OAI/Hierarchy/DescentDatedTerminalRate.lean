import OAI.Hierarchy.DescentTerminalAddressPlan
import OAI.Hierarchy.DescentDatedChronology

namespace OAI
/-! # One final word-size bound for the actual accumulated calendar and the native terminal -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open DescentDatedAddressBook Filter
noncomputable section

structure Rates (S : ℕ→Shape) (I : ℕ→Input) : Prop where
  sites : Bounded (ι:=fun _=>Unit) (fun h _=>(S h).sites)
  rows : Bounded (ι:=fun _=>Unit) (fun h _=>(S h).terminal.rows)
  packets : Bounded (ι:=fun _=>Unit) (fun h _=>(S h).packets)
  pool : Bounded (ι:=fun _=>Unit) (fun h _=>(S h).terminal.pool)
  sources : Bounded (ι:=fun _=>Unit) (fun h _=>∑j,DescentTerminalEmitter.Compact.need ((I h).sources j))
  dense : Bounded (ι:=fun _=>Unit) (fun h _=>(S h).terminal.plane.rawRows)
  publicRows : Bounded (ι:=fun _=>Unit) (fun h _=>(S h).terminal.plane.publicRows)
  widths : Bounded (ι:=fun _=>Unit) (fun h _=>(S h).terminal.plane.headerRows)
  leaves : Bounded (ι:=fun _=>Unit) (fun h _=>(S h).terminal.leaves)
  indexEvents : Bounded (ι:=fun _=>Unit) (fun h _=>(I h).indexEvents)
  formatEvents : Bounded (ι:=fun _=>Unit) (fun h _=>(I h).formatEvents)
  profile : ∀h,let t:=(S h).terminal.plane;DescentExteriorShelf.tableBits t.headBits t.restBits t.bitLanes≤h/2

structure CofinalRates (S : ℕ→Shape) (I : ℕ→Input) : Prop where
  sites : Bounded (ι:=fun _=>Unit) (fun h _=>(S h).sites)
  rows : Bounded (ι:=fun _=>Unit) (fun h _=>(S h).terminal.rows)
  packets : Bounded (ι:=fun _=>Unit) (fun h _=>(S h).packets)
  pool : Bounded (ι:=fun _=>Unit) (fun h _=>(S h).terminal.pool)
  sources : Bounded (ι:=fun _=>Unit) (fun h _=>∑j,DescentTerminalEmitter.Compact.need ((I h).sources j))
  dense : Bounded (ι:=fun _=>Unit) (fun h _=>(S h).terminal.plane.rawRows)
  publicRows : Bounded (ι:=fun _=>Unit) (fun h _=>(S h).terminal.plane.publicRows)
  widths : Bounded (ι:=fun _=>Unit) (fun h _=>(S h).terminal.plane.headerRows)
  leaves : Bounded (ι:=fun _=>Unit) (fun h _=>(S h).terminal.leaves)
  indexEvents : Bounded (ι:=fun _=>Unit) (fun h _=>(I h).indexEvents)
  formatEvents : Bounded (ι:=fun _=>Unit) (fun h _=>(I h).formatEvents)
  profile : ∀ᶠ h : ℕ in atTop,let t:=(S h).terminal.plane;DescentExteriorShelf.tableBits t.headBits t.restBits t.bitLanes≤h/2

instance {S : ℕ→Shape} {I : ℕ→Input} : Coe (Rates S I) (CofinalRates S I) where
  coe b:=⟨b.sites,b.rows,b.packets,b.pool,b.sources,b.dense,b.publicRows,b.widths,b.leaves,b.indexEvents,b.formatEvents,Eventually.of_forall b.profile⟩

theorem realized_suffix_cofinal_rate (S : ℕ→Shape) (I : ℕ→Input) (b : CofinalRates S I)
    (base : ℕ→ℕ) (prior : Bounded (ι:=fun _=>Unit) (fun h _=>base h)) :
    Bounded (ι:=fun _=>Unit) (fun h _=>endAddress (S h) (I h) (base h)) := by
  have short : Bounded (ι:=fun _=>Unit) (fun h _=>2^(h/2)) :=Bounded.pow_of_linear (K:=1)
    (Eventually.of_forall fun h _=>by simpa only [Nat.one_mul] using Nat.div_le_self h 2)
  have first:=(((b.sites.add b.rows).add b.packets).add b.pool).add (Bounded.const 1)
  have tapes:=((((b.packets.add short).add b.dense).add b.publicRows).add b.widths).add (Bounded.const 1)
  have emitter:=(((((b.rows.add b.pool).add b.leaves).add b.indexEvents).add b.formatEvents).add (Bounded.const 1))
  have pagesBound := prior.add ((Bounded.const 92).mul first)
  have sourcesBound := (pagesBound.add ((Bounded.const 2).mul b.sources)).add (Bounded.const 43)
  have planeBound := sourcesBound.add ((Bounded.const 64).mul tapes)
  have emitterBound := planeBound.add ((Bounded.const 60).mul emitter)
  have room := ((emitterBound.add ((Bounded.const 8).mul b.rows)).add (Bounded.const 6)).add b.pool
  obtain ⟨K,hK⟩:=room
  refine ⟨K,?_⟩
  filter_upwards [hK,b.profile] with h bound profile
  intro u
  exact (address_bill (S h) (I h) (base h) profile).trans (bound u)

theorem realized_suffix_rate (S : ℕ→Shape) (I : ℕ→Input) (b : Rates S I)
    (base : ℕ→ℕ) (prior : Bounded (ι:=fun _=>Unit) (fun h _=>base h)) :
    Bounded (ι:=fun _=>Unit) (fun h _=>endAddress (S h) (I h) (base h)) := realized_suffix_cofinal_rate S I (b : CofinalRates S I) base prior

/-- A single word size is valid at every chronological store and at the final histogram keys. -/
theorem realized_calendar_room (S : ℕ→Shape) (I : ℕ→Input) (b : Rates S I)
    (start dates : ℕ→ℕ) (next : ℕ→ℕ→ℕ→ℕ) (extends_ : ∀h t a,a≤next h t a)
    (initial : Bounded (ι:=fun _=>Unit) (fun h _=>start h))
    (length : Bounded (ι:=fun _=>Unit) (fun h _=>dates h))
    (dated : Bounded (ι:=fun h=>Fin (dates h))
      (fun h t=>next h t (cursor (start h) (next h) t)-cursor (start h) (next h) t))
    (beforeMask : ℕ→ℕ) (mask : Bounded (ι:=fun _=>Unit)
      (fun h _=>beforeMask h-cursor (start h) (next h) (dates h))) :
    ∃K : ℕ,∀ᶠ h:ℕ in atTop,endAddress (S h) (I h) (beforeMask h)<2^(K*h) := by
  obtain ⟨C,hc⟩:=eventual_calendar_room (start:=start) (dates:=dates) next extends_ initial length dated
  have old : Bounded (ι:=fun _=>Unit) (fun h _=>cursor (start h) (next h) (dates h)) :=
    ⟨C,hc.mono fun _ lt _=>lt.le⟩
  have begin_ : Bounded (ι:=fun _=>Unit) (fun h _=>beforeMask h) := (old.add mask).of_le fun _ _=>by omega
  obtain ⟨A,hw⟩:=realized_suffix_rate S I b beforeMask begin_
  refine ⟨A+1,?_⟩
  filter_upwards [hw,eventually_ge_atTop 1] with h area positive
  apply (area ()).trans_lt
  apply Nat.pow_lt_pow_right (by decide : 1<2)
  rw [Nat.add_mul]
  omega

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
