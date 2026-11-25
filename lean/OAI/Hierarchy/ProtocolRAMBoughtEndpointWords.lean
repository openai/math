import OAI.Hierarchy.ProtocolRAMBoughtSockets
import OAI.Hierarchy.ProbePositiveSiteROM
import OAI.Hierarchy.ProtocolRAMPurchaseCTNumbering

namespace OAI
/-! # Two true endpoints of each retained chain on the physical port directory -/

namespace Hierarchy.ProtocolRAM.BoughtSockets
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseFrozen PurchaseCT ReportSockets
open TaggedShorterSupergroups
open ThreeFlat.RAM
open scoped Fin.CommRing Classical
noncomputable section
variable {z W k attempts K : ℕ}

theorem numbered_after {d : ℕ} (π : Equiv.Perm (Fin (2^z))) (input : Shelf.Mem z d)
    (done : After (d:=d) π input (rounds d)) : numberLoaded groupNumber π (images z d input (rounds d)) :=
  fun t => (resident_numbered π t 0 0 0 0 input done).group

theorem numbered_of_frame {d : ℕ} (num : ReportGroupROM.Numbering z d) (π : Equiv.Perm (Fin (2^z)))
    (m m' : Shelf.Mem z d) (rows : numberLoaded num π m)
    (same : ∀a,a<heapEnd z d Native.copies→m' a=m a) : numberLoaded num π m' := by
  intro t r
  have rem:=Nat.mod_lt (r.val:Word (wordBits z d Native.copies)).val (Nat.two_pow_pos (banks t).group.bits)
  exact (same _ ((Nat.add_lt_add_left rem _).trans_le (stageBank_end z d (stageNumber t) 0))).trans (rows t r)

abbrev pathKey (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth : ℕ) (marked : Marks z W k attempts)
    (a : Fin attempts) (p : LiveChains S π depth (marked a)) : Key z (2^W) k :=
  key p.1 ((PurchaseMarks.signedDirection k).symm p.2.1)

def eventIndex (keyBase : ℕ) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth : ℕ)
    (marked : Marks z W k attempts) (a : Fin attempts) (p : LiveChains S π depth (marked a))
    (r : PurchaseDirectory.Index (2^z) S.degree depth) :=
  let header:=StripDirectory.stratumHeader z (2^W) k S.degree depth keyBase
  header.enum ⟨pathKey S π depth marked a p,⟨r.val,by simpa [header,StripDirectory.stratumHeader,paths] using r.isLt⟩⟩

structure Reads {w : ℕ} (fields : Inputs) (m : Memory w) (r : Word w) (groups : Fin K ≃ AllGroups z (2^W))
    (x : StageColumns z (2^W) × Role k attempts) : Prop where
  group : fields.group.eval m r=((groups.symm (owner x.1)).val:Word w)
  port : fields.port.eval m r=((socketPort x.1).val:Word w)
  tag : fields.tag.eval m r=((socketTag x.1 x.2).val:Word w)

/-- Both ends use the same original candidate ID, including when two DFS
words happen to describe the same chain. The witness specifies the selected
candidate's literal tile columns at all positions. -/
theorem retained (groupBase keyBase : ℕ) (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth : ℕ)
    (marked : Marks z W k attempts) (unique : Exclusive marked) (a : Fin attempts) (p : LiveChains S π depth (marked a))
    (groups : Fin K ≃ AllGroups z (2^W)) (num : ReportGroupROM.Numbering z (2^W)) (m : Shelf.Mem z (2^W))
    (geo : numberLoaded num π m) (remap : ReportGroupROM.Resident groupBase groups num m)
    (data : sh.PortData S π depth (pathKey S π depth marked a p) m)
    (room : (depth+1)*paths z S.degree depth≤2^wordBits z (2^W) Native.copies)
    (keyFit : count z (2^W) k ≤ 2^wordBits z (2^W) Native.copies)
    (header : (StripDirectory.stratumHeader z (2^W) k S.degree depth keyBase).Loaded m)
    (r : PurchaseDirectory.Index (2^z) S.degree depth)
    (hit : ∀j,Shelf.pathRows S π depth (pathKey S π depth marked a p) r j=(liveRow S π depth (marked a) p j).castSucc)
    (side : Bool) :
    Reads (event groupBase keyBase sh S z (2^W) k depth a side) m ((eventIndex keyBase S π depth marked a p r).val:Word _)
      groups (locate S π depth marked unique (.inr ⟨a,p⟩,side)) := by
  let i:=pathKey S π depth marked a p
  let tile:=liveRow S π depth (marked a) p
  let row : Fin (paths z S.degree depth) := ⟨r.val,by simpa [paths] using r.isLt⟩
  have keyRead := local_read groupBase sh S π depth i a side m groups num geo remap data room r
    (tile 0) (tile (position depth side)) (hit 0) (hit (position depth side))
  have input:=event_read groupBase keyBase sh S depth a side m i row keyFit header
  let origin:=eventIndex keyBase S π depth marked a p r
  let fields:=event groupBase keyBase sh S z (2^W) k depth a side
  let t:=p.1
  let pts:=advisedStage z (2^W) π t
  have atStage : stage i=t := stage_key ..
  let groupWord (u : StageAt z (2^W)) : Word (wordBits z (2^W) Native.copies) :=
    (groups.symm ⟨u,(advisedStage z (2^W) π u).group (tile 0)⟩).val
  let portWord (u : StageAt z (2^W)) : Word (wordBits z (2^W) Native.copies) :=
    let endpoints:=advisedStage z (2^W) π u
    (if side then endpoints.output (tile (position depth side))
      else endpoints.input (tile (position depth side))).val
  have g : fields.group.eval m (origin.val:Word _)=((groups.symm ⟨t,pts.group (tile 0)⟩).val:Word _) :=
    input.1.trans (keyRead.1.trans (congrArg groupWord atStage))
  have s : fields.port.eval m (origin.val:Word _)=
      ((if side then pts.output (tile (position depth side)) else pts.input (tile (position depth side))).val:Word _) :=
    input.2.1.trans (keyRead.2.1.trans (congrArg portWord atStage))
  have b : fields.tag.eval m (origin.val:Word _)=(((Fintype.equivFin (Bool × Role k attempts)) (side,.inr a)).val:Word _) :=
    input.2.2.trans keyRead.2.2
  have physical : (locate S π depth marked unique (.inr ⟨a,p⟩,side)).1=
      purchaseSockets S π depth (marked a) (unique a) (p,side) := rfl
  have role : (locate S π depth marked unique (.inr ⟨a,p⟩,side)).2=Sum.inr a := rfl
  cases side with
  | false =>
    rw [purchaseSockets_in] at physical
    exact ⟨by rw [physical];exact g,by rw [physical];exact s,by rw [role,physical];exact b⟩
  | true =>
    rw [purchaseSockets_out] at physical
    exact ⟨by rw [physical];exact g,by rw [physical];exact s,by rw [role,physical];exact b⟩

end
end Hierarchy.ProtocolRAM.BoughtSockets

end OAI
