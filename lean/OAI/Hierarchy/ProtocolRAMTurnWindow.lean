import OAI.Hierarchy.ProtocolRAMPackedBias
import OAI.Hierarchy.ProtocolRAMTurnDirectory

namespace OAI
/-! # Space for one chronological route report

The running visit sum and its pointer tape precede the seven occurrence columns.
The sparse five-column physical shelf and its replay tape follow those columns.
An inactive write goes to the first scratch word, above all retained inputs. -/
namespace Hierarchy.ProtocolRAMTurnWindow
open Computability.VPVNP.BurstRAM PrivateRAM
open ProtocolRAM ProtocolRAMPackedRanked

structure Layout where
  floor : ℕ
  rows : ℕ
  sites : ℕ
  seats : ℕ

namespace Layout
variable (L : Layout)

def sink := L.floor
def zero := L.floor+1
def site : Bank := ⟨L.zero+1+2*L.rows,groupBits L.rows⟩
def src := L.site.base+L.site.size
def srcBits := groupBits (5*L.rows)
def base := L.src+6*L.rows+2^L.srcBits
def scratch := L.base+5*(L.sites*L.seats)
def stop := L.scratch+10*L.rows+1

theorem site_room : L.rows ≤ L.site.size := group_capacity L.rows

theorem src_room : 5*L.rows ≤ 2^L.srcBits := group_capacity (5*L.rows)

theorem bounds : L.floor < L.zero ∧ L.zero+1+3*L.rows ≤ L.src ∧
    L.src+7*L.rows ≤ L.base ∧ L.base+5*(L.sites*L.seats) ≤ L.scratch ∧
    L.scratch+10*L.rows < L.stop := by
  have a := L.site_room
  have b := L.src_room
  change L.rows≤2^groupBits L.rows at a
  dsimp only [zero,site,src,base,scratch,stop,Bank.size] at *
  omega

theorem stop_le : L.stop ≤ L.floor+30*L.rows+5*(L.sites*L.seats)+7 := by
  have a := bias_words L.rows
  have b := bias_words (5*L.rows)
  dsimp [stop,scratch,base,src,site,srcBits,zero,Bank.size]
  omega

/-- Two fixed ROMs may be allocated once below the working area. They are indexed
by chronological row, or by the public destination site and field ordinal. -/
def romBits := groupBits (5*L.rows+L.sites)

theorem rom_capacity : L.rows*5 ≤ 2^L.romBits ∧ L.sites ≤ 2^L.romBits := by
  have a := group_capacity (5*L.rows+L.sites)
  change 5*L.rows+L.sites≤2^L.romBits at a
  omega

theorem rom_words : 6*2^groupBits L.rows+4*2^L.romBits ≤
    52*L.rows+8*L.sites+20 := by
  have a := bias_words L.rows
  have b := bias_words (5*L.rows+L.sites)
  unfold romBits
  omega

theorem below {a : ℕ} (old : a<L.floor) :
    a<L.zero ∧ a<L.src ∧ a<L.base ∧ a<L.scratch ∧ a≠L.sink := by
  have h := L.bounds
  change a<L.zero ∧ a<L.src ∧ a<L.base ∧ a<L.scratch ∧ a≠L.floor
  omega

theorem site_fit {w : ℕ} (room : L.stop≤2^w) : L.site.Fits w L.src := by
  have h := L.bounds
  refine ⟨Nat.two_pow_pos _,?_,le_rfl⟩
  change 2^groupBits L.rows<2^w
  have eq : L.src=L.floor+1+1+2*L.rows+2^groupBits L.rows := rfl
  omega

end Layout
end Hierarchy.ProtocolRAMTurnWindow

end OAI
