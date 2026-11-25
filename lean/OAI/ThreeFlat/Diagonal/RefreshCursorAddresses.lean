import OAI.ThreeFlat.Diagonal.RefreshOwnerImage

namespace OAI
/-! # Physical node arrays and wires precede the persistent child and owner streams -/

namespace ThreeFlat.Diagonal.RefreshStageNav.CursorSpace

open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.HeaderScan NavigationDirectory RefreshDemandRows

variable {v a t h pad K : ℕ} {c : Cursor}
set_option quotPrecheck false
local notation "m" => mPort a
local notation "d" => 1+h+pad
local notation "n" => v*m*2^t
local notation "entry" => allocate K c (.refresh v m (2^t) h pad)
local notation "P" => recordPointers entry
local notation "new" => nextColumns entry v m h pad

include c K v a t h pad in
theorem retained_addresses :
    (entry).words 3+v*2^t*m*h≤(entry).words 34 ∧ c.heap+3*(v*2^t)≤(entry).words 34 ∧
    (new).graph+6*(new).rows≤(entry).words 34 ∧ (new).widths+v*m*d*2^t≤(entry).words 34 ∧
    ∀ q,(P).dst q+Records.length v m t d q≤(entry).words 42 := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := ordered (c:=c) (K:=K) (v:=v) (a:=a) (t:=t) (h:=h) (pad:=pad)
  obtain ⟨k0,m0,a0,e0,last⟩ := record_layout (c:=c) (K:=K) (v:=v) (a:=a) (t:=t) (h:=h) (pad:=pad)
  obtain ⟨left,finish,beg,endRow⟩ := RefreshNodeOwners.owner_spans (c:=c) (v:=v) (a:=a) (t:=t) (h:=h) (pad:=pad) (K:=K)
  have h34 : (entry).words 34=(P).kernel := rfl
  have h40 : (entry).words 40=(P).halves := rfl
  have h41 : (entry).words 41=n*(8*d) := Nat.mul_comm (8*d) n
  refine ⟨by omega,by omega,by omega,by omega,?_⟩
  intro q
  rw [← endRow, h40, h41]
  cases q with
  | kernel =>
    change (P).kernel + n*5 ≤ (P).halves + n*(8*d)
    omega
  | motif =>
    change (P).motif + n*6 ≤ (P).halves + n*(8*d)
    omega
  | halfHeader =>
    change (P).headers + n*2 ≤ (P).halves + n*(8*d)
    omega
  | halves =>
    exact le_rfl

theorem stage_bounds (W : ℕ) (cur : Word W) (mem : Memory W)
    (u : CursorSpace cur mem c K v a t h pad) : (entry).words 34≤(entry).words 42 ∧ (entry).words 42≤cur.val ∧
      (entry).words 44+n≤cur.val := by
  obtain ⟨l,r,ha,e⟩ := RefreshNodeOwners.owner_spans (c:=c) (v:=v) (a:=a) (t:=t) (h:=h) (pad:=pad) (K:=K)
  have := (retained_addresses (c:=c) (v:=v) (a:=a) (t:=t) (h:=h) (pad:=pad) (K:=K)).2.2.2.2 Records.Table.kernel
  change (entry).words 34+n*5≤_ at this
  have := u.controls
  omega


end ThreeFlat.Diagonal.RefreshStageNav.CursorSpace

end OAI
