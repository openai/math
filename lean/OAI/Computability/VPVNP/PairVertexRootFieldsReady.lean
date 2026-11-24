import OAI.Computability.VPVNP.PairVertexRootFields
import OAI.Computability.VPVNP.PairVertexRootPacket
import OAI.Computability.VPVNP.PairVertexRootGatherResident

/-!
# Root packet and DFS state at the end of the terminal gather

The bootstrap pushes the root address onto an initially zero private memory.
The gather installs the actual terminal vertex's two half-wire lists in its
node interval. At DFS row zero the pending root, vertex-wide geometry, all
38 cached leaf inputs and the zero histogram are resident together.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexRootFields

open BurstRAM PrivateRAM LiveProgram Compression VertexImage TerminalSiteStart TerminalRootGather LeafSourceLoad
open scoped Fin.CommRing

variable {c : Constants} {degree a b p r w : ℕ} {leaf shrink refresh : VertexImage.Segment}
local notation "S" => segments (VertexGeometry.segment c degree a b) TerminalRootGather.segment leaf shrink refresh
variable {A : Placement (segments (VertexGeometry.segment c degree a b) TerminalRootGather.segment leaf shrink refresh) p r}
  {M : Machine w p r 11} {m : Memory w} {hdr ord : Word w} {boot geo : Config w p r}
  {vals : Static 34 → Word w}

local notation "lay" => TerminalRootGather.Layout.ofHeader degree M.publicData hdr ord m
local notation "area" => NativeFrame.fromHeader degree M.publicData hdr m
local notation "N" => Fin.val (M.publicData 6)
local notation "G" => NativeFrame.frameBase (NativeFrame.fromHeader degree M.publicData hdr m)
local notation "role" => boot.reg (A.saved roleOffset)
local notation "rootWord" => (m (Fin.val (hdr+6)) + m (Fin.val (hdr+15)) * ord)

private theorem predecessor (n : Word w) (hn : 0 < n.val) : ((n.val-1 : ℕ) : Word w) = n-1 := by
  rw [Nat.cast_sub hn,Nat.cast_one,Fin.cast_val_eq_self]

/-- The concrete boot store gives exactly the singleton stack below the
geometry pointer, even when the payload word is zero. -/
theorem singleton {priv : Word w → Word w} (mem : boot.privateMem =
    Function.update priv (M.publicData 6-1) rootWord) (hn : 0 < N) :
    DFS.Represents boot.privateMem (N-1) [((lay).root : Word w)] := by
  have hmod := (M.publicData 6).isLt
  refine ⟨by simp only [List.length_singleton]; omega,?_⟩
  intro i
  have hi : i.val = 0 := by have := i.isLt; simp only [List.length_singleton] at this; omega
  have he : i = (⟨0,by simp⟩ : Fin [((lay).root : Word w)].length) := Fin.ext hi
  subst i
  change boot.privateMem ((N-1+0 : ℕ) : Word w) = ((lay).root : Word w)
  rw [mem,Nat.add_zero,predecessor _ hn,Function.update_self]
  exact (Fin.cast_val_eq_self rootWord).symm

private theorem boot_histogram (mem : boot.privateMem =
    Function.update (fun _ => 0) (M.publicData 6-1) rootWord) (hn : 0 < N)
    (histAfter : N < (area).histBase) (cacheFit : (area).cacheBase+38 ≤ 2^w)
    (i : Fin (area).histWords) : boot.privateMem (((area).histBase+i.val : ℕ) : Word w) = 0 := by
  have hbound := (Nat.add_lt_add_left i.isLt (area).histBase).trans_le (area).hist_before
  have val : ((((area).histBase+i.val : ℕ) : Word w)).val = (area).histBase+i.val := Nat.mod_eq_of_lt (by omega)
  have nfit := (M.publicData 6).isLt
  have prev : (M.publicData 6-1).val = N-1 := by
    rw [← predecessor (M.publicData 6) hn]; exact Nat.mod_eq_of_lt (by omega)
  rw [mem,Function.update_of_ne]
  intro eq
  have hv := congrArg Fin.val eq
  rw [val,prev] at hv
  omega

variable {ex lanes : ℕ} {X : State ex lanes} {u : X.network.Site}
variable (f : Fin (∑ i, TerminalPrefix.width X i) → Bool)

local notation "q₀" => VertexRootPacket.packet X lay u f

theorem ready_of_placed (hb : BootReady (M.publicData 6) hdr ord m (boot.reg ∘ bootBank A))
    (hg : VertexGeometry.Ready c degree a b A m M.publicData boot geo vals)
    (fresh : boot.privateMem = Function.update (fun _ => 0) (M.publicData 6-1) rootWord)
    (num : TerminalGatherGeometry.Numbering X lay u) (rows : TerminalGatherGeometry.Rows X lay m)
    (bits : ∀ i, m ((lay).wires+i.val) = PrivateFields.bitValue w (f i))
    (fit : (lay).Fits m) (hn : 0 < N) (rootPos : 0 < (lay).root) (rootBound : (lay).root < (area).nodes)
    (deg : 2^ex ≤ degree) (width : X.maxWireWidth ≤ N) (cacheFit : (area).cacheBase+38 ≤ 2^w) (out : Config w p r)
    (placed : out.privateMem = TerminalRootGather.Layout.placed (lay).dest ((lay).packet m) geo.privateMem) :
    (q₀).Fits (area).arguments w N ∧ (q₀).Stored (area).arguments (DFS.scratch N out.privateMem) ∧
      Resident area N (N-1) [((lay).root : Word w)] (NativeFrame.leafWords degree M.publicData hdr role m)
        (NativeFrame.fields degree M.publicData hdr role m) vals out.privateMem := by
  have size := VertexRootPacket.length_le_stride X lay u f degree deg width
  obtain ⟨qfit,stored,bound⟩ := VertexRootPacket.of_gather num rows f bits fit area rfl rfl rootBound size geo out placed
  have len : ((lay).packet m).length = (q₀).bits.length := by
    rw [TerminalGatherGeometry.packet_eq num rows f bits,List.length_map]; rfl
  have packetEnd : (lay).dest + ((lay).packet m).length ≤ (area).histBase := by rw [len]; exact bound
  have pointerBelow : N < (lay).dest := by
    change N < N+(lay).root*(2*degree*N+1)
    exact Nat.lt_add_of_pos_right (Nat.mul_pos rootPos (Nat.succ_pos _))
  have histAfter : N < (area).histBase := pointerBelow.trans_le ((Nat.le_add_right _ _).trans packetEnd)
  have before := singleton (degree := degree) (m := m) (hdr := hdr) (ord := ord) fresh hn
  have ends : N-1 + [((lay).root : Word w)].length ≤ N := by simp only [List.length_singleton]; omega
  have hh : boot.reg (A.saved header) = hdr := hb.header
  have resident := Resident.of_ready hg before ends (hh ▸ histAfter) (hh ▸ cacheFit)
    (by rw [hh]; exact boot_histogram fresh hn histAfter cacheFit)
  rw [hh] at resident
  have gh := (area).hist_before
  have room : G+12 ≤ 2^w := by change (area).histBase+(area).histWords+12 ≤ _; omega
  exact ⟨qfit,stored,resident.after_gather placed ends pointerBelow packetEnd room cacheFit⟩

theorem gather_ready (contains : Contains A M) (hb : BootReady (M.publicData 6) hdr ord m (boot.reg ∘ bootBank A))
    (hg : VertexGeometry.Ready c degree a b A m M.publicData boot geo vals)
    (fresh : boot.privateMem = Function.update (fun _ => 0) (M.publicData 6-1) rootWord)
    (num : TerminalGatherGeometry.Numbering X lay u) (rows : TerminalGatherGeometry.Rows X lay m)
    (bits : ∀ i, m ((lay).wires+i.val) = PrivateFields.bitValue w (f i))
    (fit : (lay).Fits m) (hn : 0 < N) (rootPos : 0 < (lay).root) (rootBound : (lay).root < (area).nodes)
    (deg : 2^ex ≤ degree) (width : X.maxWireWidth ≤ N) (cacheFit : (area).cacheBase+38 ≤ 2^w) :
    ∃ out es, out.pc = A.dfsPC 0 ∧ out.persistent = geo.persistent ∧
      (∀ i, out.reg (A.dfs i) = geo.reg (A.dfs i)) ∧ (∀ i, out.reg (A.saved i) = geo.reg (A.saved i)) ∧
      Frame (imageRegs A (rfl : S .rootFields = TerminalRootGather.segment)) geo out ∧
      out.privateMem = TerminalRootGather.Layout.placed (lay).dest ((lay).packet m) geo.privateMem ∧
      (q₀).Fits (area).arguments w N ∧ (q₀).Stored (area).arguments (DFS.scratch N out.privateMem) ∧
      Resident area N (N-1) [((lay).root : Word w)] (NativeFrame.leafWords degree M.publicData hdr role m)
        (NativeFrame.fields degree M.publicData hdr role m) vals out.privateMem ∧
      Cost es (15+21*(lay).degree+5*((lay).packet m).length) (5*(lay).degree+((lay).packet m).length) ∧
      Prefix M m geo es out := by
  obtain ⟨out,es,done,st,dfs,saved,frame,placed,cost,pre⟩ := gather contains hb hg fit
  obtain ⟨qfit,stored,resident⟩ := ready_of_placed f hb hg fresh num rows bits fit hn rootPos rootBound
    deg width cacheFit out placed
  exact ⟨out,es,done,st,dfs,saved,frame,placed,qfit,stored,resident,cost,pre⟩

end PairSimulation.VertexRootFields

end VPVNP
end Computability
end OAI
