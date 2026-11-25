import OAI.Hierarchy.DescentTerminalMaskReady
import OAI.Hierarchy.DescentPrivateMaskPrice

namespace OAI
/-! # From actual issued physical fields and the held path sum to the terminal field exponent -/
namespace Hierarchy.DescentTerminalVertexFields.MaskAllocation
open DescentTerminalSiteShelves DescentTerminalRecipeRows ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentCompiler.TerminalScale ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
variable {q t H N A p groups blocks sites V B bw : ℕ}
local notation "F₀" => Fin (channels blocks)
local notation "size" => channelSize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p) (groups:=groups) (blocks:=blocks)
local notation "cap" => cohortSize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p) (groups:=groups) (blocks:=blocks)
variable (R : Channels blocks) (base header : ℕ)
local notation "cells" => marks size+cap
local notation "C" => counter (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) R base
local notation "O" => PrivateCounter.registers C header sites cap
local notation "read" => measured (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p) (groups:=groups) (C).layout
local notation "clock" => privateMaskedClock cells cap sites blocks p
local notation "phase" => PrivateCounter.machine (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (homes:=sites) (bw:=bw) C O
local notation "fetch" proof => program (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (blocks:=blocks) (V:=V) (B:=B) proof bw base
local notation "printed" proof => image (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (blocks:=blocks) (V:=V) (B:=B) (bw:=bw) proof base
local notation "out" => PrivateCounter.rawFinal (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (homes:=sites) C O

private theorem room_bounds (atBase tableCells capacityRows homes limit : ℕ)
    (room : atBase+tableCells+capacityRows+homes+homes+3<limit) :
    atBase+tableCells<limit ∧ atBase+tableCells+capacityRows+homes+homes+1<limit := by omega

private theorem frame_bounds (atBase tableCells capacityRows homes addr : ℕ)
    (outside : addr<atBase ∨ atBase+tableCells+capacityRows+homes+homes+3≤addr) :
    (addr<atBase+tableCells ∨ atBase+tableCells+capacityRows+homes+homes<addr) ∧
    addr≠atBase+tableCells+capacityRows+homes+homes+1 ∧
    addr≠atBase+tableCells+capacityRows+homes+homes+2 ∧
    (addr<atBase ∨ atBase+tableCells≤addr) := by omega

private theorem compose_counter {w : ℕ} (first second : Procedure w) (m₀ m₁ m₂ : Memory w)
    (a b : ℕ) (left : first.Exec m₀ m₁ a) (right : second.Exec m₁ m₂ b)
    (cheapLeft : CheapCode first) (cheapRight : CheapCode second) :
    (first.seq second).Exec m₀ m₂ (a+b) ∧ CheapCode (first.seq second) :=
  ⟨@Procedure.Exec.then w first second m₀ m₁ m₂ a b (@left) (@right),
    @cheap_seq w first second (@cheapLeft) (@cheapRight)⟩

attribute [local irreducible] PrivateCounter.machine PrivateCounter.rawFinal literal
set_option cleanup.letToHave false
set_option maxHeartbeats 1200000

/-- Execution and raw allocation are total even when the cost and the nine prior data fields are malformed. -/
theorem terminal_any (fit : V * span q t H N A p ≤ B) (m : Memory bw) (prior : ∀f,(R.bank f).base+(R.bank f).size≤base)
    (safe : header<base) (endAt : base+cells+cap+sites+sites+3<2^bw) :
    ((fetch fit).seq phase).Exec m (out ((printed fit) m)) clock ∧ CheapCode ((fetch fit).seq phase) ∧
    MountedMask (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p) (V:=V) (B:=B)
      (groups:=groups) (blocks:=blocks) (bits:=bw) (C).layout (out ((printed fit) m)) fit ∧
    (∀f z,(R.bank f).read (out ((printed fit) m)) z=(R.bank f).read m z) ∧ out ((printed fit) m) header=m header := by
  have bounds := room_bounds base cells cap sites (2^bw) endAt
  have install := install_at (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p)
    (groups:=groups) (blocks:=blocks) (V:=V) (B:=B) (bw:=bw) R base fit m bounds.1
  have ready := prepared (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p)
    (groups:=groups) (blocks:=blocks) (V:=V) (B:=B) (bw:=bw) (sites:=sites) R base header m fit prior safe endAt
  have counted := PrivateCounter.any_raw (q:=q) (t:=t) (H:=H) (N:=N) (A:=A)
    (p:=p) (groups:=groups) (homes:=sites) C O ((printed fit) m) ready.1 bounds.2 ready.2.1
  have joined := compose_counter (fetch fit) phase m ((printed fit) m) (out ((printed fit) m))
    (4+10*cells) (privateHomeClock cap sites blocks p) (@install.1) (@counted.1)
    (@install.2.2.2) (@counted.2)
  exact ⟨joined.1, @joined.2, ready.2.2⟩

/-- The earlier archives and every address after the final scalar registers are
preserved on every input, including malformed branch memories. -/
theorem terminal_frame (fit : V * span q t H N A p ≤ B) (m : Memory bw) (j : ℕ)
    (away : j<base ∨ base+cells+cap+sites+sites+3≤j) :
    out ((printed fit) m) j=m j := by
  have bounds := frame_bounds base cells cap sites j away
  have first := PrivateCounter.rawFinal_frame (q:=q) (t:=t) (H:=H) (N:=N) (A:=A)
    (p:=p) (groups:=groups) (homes:=sites) C O ((printed fit) m) j bounds.1 bounds.2.1 bounds.2.2.1
  exact first.trans (DescentStaticWordColumn.frame base cells (literal (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p)
    (groups:=groups) (blocks:=blocks) (V:=V) (B:=B) fit) m j bounds.2.2.2)

/-- The held source count is read at its original address across the real ROM
writer. The live count reads the identical raw channel words. -/
theorem terminal (fit : V * span q t H N A p ≤ B) (m : Memory bw) (allBits : ℕ) (prior : ∀f,(R.bank f).base+(R.bank f).size≤base)
    (safe : header<base) (endAt : base+cells+cap+sites+sites+3<2^bw)
    (held : m header=(allBits:Word bw)) (bound : (∑i : Fin sites,privateHome (read m i))*p≤allBits) :
    ((fetch fit).seq phase).Exec m (out ((printed fit) m)) clock ∧ CheapCode ((fetch fit).seq phase) ∧
    out ((printed fit) m) (O).deadBits=((allBits-(∑i : Fin sites,privateHome (read m i))*p:ℕ):Word bw) ∧
    MountedMask (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p) (V:=V) (B:=B)
      (groups:=groups) (blocks:=blocks) (bits:=bw) (C).layout (out ((printed fit) m)) fit ∧
    (∀f z,(R.bank f).read (out ((printed fit) m)) z=(R.bank f).read m z) := by
  obtain ⟨run,cheap,shelf,old,_⟩:=terminal_any (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p)
    (groups:=groups) (blocks:=blocks) (V:=V) (B:=B) (bw:=bw) (sites:=sites) R base header fit m prior safe endAt
  have bounds := room_bounds base cells cap sites (2^bw) endAt
  obtain ⟨stamp,initialized,frame,hw⟩:=install_at (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p)
    (groups:=groups) (blocks:=blocks) (V:=V) (B:=B) (bw:=bw) R base fit m bounds.1
  obtain ⟨healthy,regs,rest⟩:=prepared (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p)
    (groups:=groups) (blocks:=blocks) (V:=V) (B:=B) (bw:=bw) (sites:=sites) R base header m fit prior safe endAt
  have rawFields (i : Fin sites) : read ((printed fit) m) i=read m i := by
    funext f
    have idx : (R.bank f).base+((i.val:Word bw).val%(R.bank f).size)<base :=
      (Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _).trans_le (prior f)
    have eqn : (R.bank f).read ((printed fit) m) (i.val:Word bw)=(R.bank f).read m (i.val:Word bw) := frame _ (.inl idx)
    exact congrArg (fun v : Word bw=>(v.val:Word (size f))) eqn
  have total : (∑i : Fin sites,privateHome (read ((printed fit) m) i))=∑i : Fin sites,privateHome (read m i) := by
    exact Finset.sum_congr rfl (fun i _=>congrArg privateHome (rawFields i))
  have sameUsed := congrArg (fun n : ℕ => n*p) total
  have enough := (le_of_eq sameUsed).trans bound
  have shifted : PrivateCounter.Shift (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p)
      (groups:=groups) (blocks:=blocks) (bw:=bw) (C).layout ((printed fit) m) :=
    ⟨initialized.shift⟩
  have one:=PrivateCounter.exponent (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (homes:=sites) C O ((printed fit) m) allBits healthy shifted bounds.2 regs
    (lt_of_lt_of_le safe (Nat.le_add_right base cells)) rfl ((frame header (.inl safe)).trans held) enough
  have measured:=PrivateCounter.raw_eq_final (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (homes:=sites) C O ((printed fit) m) healthy bounds.2 regs shifted rfl
  have sameOutput := congrFun measured (O).deadBits
  have sameValue := congrArg (fun n : ℕ => ((allBits-n : ℕ) : Word bw)) sameUsed
  exact ⟨@run, @cheap, sameOutput.trans (one.2.2.trans sameValue), shelf, old⟩

end
end Hierarchy.DescentTerminalVertexFields.MaskAllocation

end OAI
