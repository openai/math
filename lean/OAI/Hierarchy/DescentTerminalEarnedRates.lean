import OAI.Hierarchy.DescentDatedTerminalRate

namespace OAI
/-! # Terminal address rates from the five public row counts in the paid shell -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open DescentDatedAddressBook DescentTerminalEmitter.Compact Filter
open scoped BigOperators

/-- The leaf scan, both event streams, and the exterior sort reuse the bought capacities. -/
structure EarnedCounts (h : ℕ) (S : Shape) (I : Input) : Prop where
  paid : S.terminal.rows=S.terminal.pool
  leaves : S.terminal.leaves=S.terminal.pool
  packets : S.packets=S.terminal.plane.publicRows
  indices : I.indexEvents=S.terminal.rows
  formats : I.formatEvents=S.terminal.rows
  literal : ∀j,need (I.sources j)≤2^(h/2)+4*S.terminal.pool
  profile : DescentExteriorShelf.tableBits S.terminal.plane.headBits S.terminal.plane.restBits S.terminal.plane.bitLanes≤h/2

private abbrev Count (f : ℕ→ℕ) := Bounded (ι:=fun _=>Unit) (fun h _=>f h)

private theorem of_eventually {x y : ℕ→ℕ} (count : Count x) (smaller : ∀ᶠ h:ℕ in atTop,y h≤x h) : Count y :=by
  obtain ⟨K,c⟩:=count
  exact ⟨K,(c.and smaller).mono (fun h hh _=>(hh.2).trans (hh.1 ()))⟩

theorem earned_rates {S : ℕ→Shape} {I : ℕ→Input} (actual : ∀ᶠ h:ℕ in atTop,EarnedCounts h (S h) (I h))
    (sites : Count (fun h=>(S h).sites)) (paid : Count (fun h=>(S h).terminal.pool))
    (publicRows : Count (fun h=>(S h).terminal.plane.publicRows))
    (dense : Count (fun h=>(S h).terminal.plane.rawRows)) (headers : Count (fun h=>(S h).terminal.plane.headerRows)) :
    CofinalRates S I :=by
  have short : Count (fun h=>2^(h/2)):=Bounded.pow_of_linear (K:=1)
    (Eventually.of_forall fun h _=>by simpa only [Nat.one_mul] using Nat.div_le_self h 2)
  let c (n:ℕ):=Bounded.const (ι:=fun _=>Unit) n
  have data:= (c 43).mul (short.add ((c 4).mul paid))
  have bought : Count (fun h=>∑j,need ((I h).sources j)):=by
    apply of_eventually data
    filter_upwards [actual] with h receipt
    calc
      _ ≤ ∑_:Fin 43,(2^(h/2)+4*(S h).terminal.pool) := Finset.sum_le_sum (fun j _=>receipt.literal j)
      _ = _ :=by simp
  have rows:=of_eventually paid (actual.mono fun _ receipt=>receipt.paid.le)
  exact ⟨sites,rows,of_eventually publicRows (actual.mono fun _ r=>r.packets.le),paid,bought,dense,publicRows,headers,
    of_eventually paid (actual.mono fun _ r=>r.leaves.le),of_eventually rows (actual.mono fun _ r=>r.indices.le),
    of_eventually rows (actual.mono fun _ r=>r.formats.le),actual.mono fun _ r=>r.profile⟩

end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
