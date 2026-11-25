import OAI.Optimization.LinearProgramming.Compression.SignWireAddressEnvelope
import OAI.Optimization.LinearProgramming.Compression.SignWireService
import OAI.Optimization.LinearProgramming.Compression.SignWirePorts

/-! Reuse a physically initialized finite numeric cache across BitRAM sign
queries. The public bit packets are disjoint from the entire numeric window. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire
open RAM RAM.Callable MinorProxyCache
open scoped BigOperators

structure CallbackArena (n fuel cap base src send recv : ℕ) : Prop where
  rowHeader : 135 ≤ cap
  nestedRow : 2*(base+n)+1 ≤ cap
  sendOutside : 2*cap < send
  replyOutside : 2*cap < recv
  room : send+(n+1)*(2*(fuel+1)+2) ≤ src

theorem callbackArena_standard (n fuel cap base : ℕ) (header : 135 ≤ cap) (row : 2*(base+n)+1 ≤ cap) :
    CallbackArena n fuel cap base (callbackRow n fuel cap) (callbackSend cap) (callbackReply n fuel cap) := by
  refine ⟨header,row,?_,?_,le_rfl⟩ <;> simp only [callbackSend,callbackReply,callbackRow] <;> omega

/-- Every finite application-specific word and bit bound is carried by the
installed cache or the public port allocation. After this actual comparison,
the returned memory is itself ready for the next query. -/
theorem wordComparator_reusable {n : ℕ} (fuel prec B C R addr cap src base send recv : ℕ)
    (A : ℤ) (mag : ℕ → ℚ) (L : Buffers) (m : Memory ℚ) (row : Fin (n+1) → ℤ)
    (bits : ∀ i : Fin n, ratBits (mag i) ≤ B)
    (form : |row (Fin.last n)|+∑ j : Fin n, |row j.castSucc| ≤ A)
    (cut : (2:ℤ)^prec*A ≤ 2^fuel) (hcap : symbolicQueryCap n fuel ≤ C)
    (prog : addressBudget (tagReturningProgram (cachedProxySignFragment (.index 14))) ≤ addr)
    (envelope : max (2*C) (2*R+1) ≤ addr) (reserve : addr+(cachedProxySignSteps n fuel C+5) ≤ cap)
    (arena : CallbackArena n fuel cap base src send recv)
    (ports : PublicPorts (n+1) send recv src base m) (hstate : m.AllData (fun q => ratBits q ≤ wordComparatorBits n fuel prec B))
    (resident : ResidentHigh (n:=n) mag L fuel prec C R cap base (fun q => ratBits q ≤ wordComparatorBits n fuel prec B) m)
    (len : m.index 37=(Lattice.signRowWord row).length)
    (packet : BitRAM.ScalarPacket m send (Lattice.signRowWord row)) :
    let P := fun q => ratBits q ≤ wordComparatorBits n fuel prec B
    ∃ t, BitRAM.NativeService.RawReply wordComparator P m (wordComparatorTime n fuel C)
      (Lattice.signReply (formOrdering (DyadicRAM.cachedForm fuel prec mag row))) t ∧
      PublicPorts (n+1) send recv src base t ∧ ResidentHigh (n:=n) mag L fuel prec C
        (nextResidentBound n fuel C R) cap base P t := by
  let P := fun q => ratBits q ≤ wordComparatorBits n fuel prec B
  have afterSend : 2*cap < src := by have := arena.sendOutside;have := arena.room;omega
  have received : 3 ≤ recv := by have := arena.rowHeader;have := arena.replyOutside;omega
  have base9 : 9 ≤ send := by have := arena.rowHeader;have := arena.sendOutside;omega
  have apart : send+(Lattice.signRowWord row).length ≤ src :=
    (Nat.add_le_add_left (row_word_length_le row fuel prec form cut) _).trans arena.room
  have enough : 16 ≤ C := by
    have h : 11*(n+1)+42 ≤ C := (le_max_right ..).trans hcap
    omega
  have safeRead (i j : ℕ) (hi : i<j) (hj : j<n+1) : 4*(base+i)+2 ≠ src+j := by
    have := arena.nestedRow;omega
  have carry (z : Memory ℚ) (hz : z.AllData P)
      (df : ∀ i,(i < 3 ∨ 8 < i) → (i < src ∨ src+(n+1) ≤ i) → z.data i=m.data i)
      (af : ∀ i,(i < 3 ∨ 6 < i) → i ≠ 10 → i ≠ 11 → i ≠ 12 → z.index i=m.index i) :
      OuterJobData (n:=n) mag L fuel prec C R cap src base P z := by
    let read : WireReadFrame m z src (n+1) := ⟨df,af⟩
    have zp := read.ports ports
    have zr := read.resident afterSend resident
    exact outerJobData_of_high_shell mag L fuel prec C R cap src base P z zr hz enough
      zp.count zp.target (by rw [zp.answer];exact received) (by omega) safeRead
  obtain ⟨t,done,u,y,read,receipt,wrote⟩ := wordComparator_rawReply_capture fuel prec B C R addr cap
    src base send A mag L m row bits form cut hcap prog envelope reserve hstate ports.query len ports.count
    ports.source base9 apart packet carry
  have up := read.ports ports
  have yp := up.transfer (fun i hi => receipt.oddIndex i (by omega))
  have rr := receipt.toResidentHigh (read.resident afterSend resident) arena.rowHeader
  exact ⟨t,done,wrote.ports yp,wrote.resident (by rw [yp.answer];exact arena.replyOutside) rr⟩

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI
