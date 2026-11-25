import OAI.Computability.NearSquareRoot.InterchangeROMBinaryRequest
import OAI.Computability.NearSquareRoot.InterchangeBQuestLocal

/-! # The fixed programs around the selected native radix command

The outer header is saved while the native command is running. Both adapters
are single programs for all radices, geometries and payloads, at each fixed
thickness exponent of the native stage.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMBinary.Ticket

open IntegerMultiplication Code Strip Strip.Dims Loom Adic
open NearSquareRoot.InterchangeAddress NearSquareRoot.InterchangeAddress.Request
open NearSquareRoot.PhysicalWalsh

open private dense_len dense_pos from OAI.Computability.NearSquareRoot.InterchangeROMBinaryHaloAuto

noncomputable section

private abbrev rateRows := total
private abbrev rowWidth := fun x : Ticket => x.w

private theorem dense_station : Station regime (fun x : Ticket => x.rows) := by
  let s := terminal (p:=2) (by decide) (fun x : Ticket => x.n) has_n
  exact toldP.station.product (s.product (toldG.station.product (s.product toldB.station)))

private theorem lift_dense {p q : Ticket → Tree}
    (h : Rip regime (fun x : Ticket => x.rows.count) rowWidth p q) : Rip regime rateRows rowWidth p q :=
  h.monoSize dense_len (fun _ => le_rfl)

private theorem converted (k : ℕ) (f : (x : Ticket) → DenseKey x → List Bool)
    (hf : ∀ x a, (f x a).length = x.w) :
    let orig x := stripe x.rows (fun a => send (f x a))
    let enc x := stripe x.rows (fun a => send (InterchangeBeadConvert.padded (pad k x) (f x a)))
    Drive regime rateRows rowWidth orig enc ∧ Drive regime rateRows rowWidth enc orig := by
  have active := InterchangeBeadConvert.stream_alive (fun x : Ticket => x.rows) dense_station f
    (fun x a => (hf x a).le)
  obtain ⟨a,b⟩ := InterchangeBeadConvert.charge _ dense_station (pad k) (has_pad k) f active
  exact ⟨lift_dense a,lift_dense b⟩

/-- The binary prefix, gap and suffix already use the native header codec.
Only the leading field width changes. -/
private theorem native_head (k : ℕ) : regime.Small (fun x : Ticket => (x.request k).header) :=
  has_e.pair (toldP.shape.pair (toldG.shape.pair toldB.shape))

private theorem positive (x : Ticket) : 1 ≤ x.total := (dense_pos x).trans_le (dense_len x)

private theorem local_parts (k : ℕ) :
    let input x := (send x.compact).fork (stripe x.rows (send ∘ x.bits))
    let kept x := (send x.compact).fork ((job x.b).issue (x.request k))
    let back x := (send x.compact).fork ((job x.b).reply (x.request k))
    Rip regime total rowWidth input kept ∧ Rip regime total rowWidth back (fun x => x.toPacket.output) := by
  have scan (grow : Bool) := auto_rip (recordTree k) (recordSize k) (recordTree_size k)
    (k:=k) (C:=4) (fun x => by simp [recordSize,Nat.add_comm (pad k x) x.w]) grow
  have hall := halo_header.monoSize (L:=rowWidth) (fun _ => le_rfl) (fun _ => Nat.zero_le _)
  have conv := (converted k (fun x => x.bits) (fun x => x.exactWidth)).1
  have head := (Rip.split conv.again).1
  have code := (head.chain hall).twice conv
  have forward := code.chain (scan true)
  have issue := (head.chain (Rip.header positive (native_head k))).twice forward
  refine ⟨head.twice issue,?_⟩
  have reply := (Rip.split (scan false).again).2.idle
  have restore := Drive.fetch positive reply
  have crop := ((restore.chain hall).twice (Drive.self positive reply)).chain (scan false)
  have conv' := (converted k (fun x a => x.bits (swapper _ _ _ a))
    (fun x a => x.exactWidth _)).2
  exact (restore.twice crop).chain conv'

/-- One fixed pair of commands and one exponent suffice simultaneously for all
chosen radices. The native call between these commands acts on the right. -/
theorem parts (k : ℕ) : ∃ t pre post,
    ClosedRuns pre (rawMass t) (rawMass t)
      (fun x => (send x.compact).fork (stripe x.rows (send ∘ x.bits)))
      (fun x => (send x.compact).fork ((job x.b).issue (x.request k))) ∧
    ClosedRuns post (rawMass t) (rawMass t)
      (fun x => (send x.compact).fork ((job x.b).reply (x.request k)))
      (fun x => x.toPacket.output) := by
  obtain ⟨⟨a,pre⟩,⟨b,post⟩⟩ := local_parts k
  let t := max a b
  obtain ⟨c,hc⟩ := InterchangeSpace.carries_bounded (pre.larger (mass_le (le_max_left a b)))
  obtain ⟨d,hd⟩ := InterchangeSpace.carries_bounded (post.larger (mass_le (le_max_right a b)))
  exact ⟨t,c,d,hc,hd⟩

end
end InterchangeROMBinary.Ticket

end NearSquareRoot
end Computability
end OAI
