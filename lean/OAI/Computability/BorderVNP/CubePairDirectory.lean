import OAI.Computability.BorderVNP.CubePairDirectoryFrame
import OAI.Computability.BorderVNP.CubePairDirectoryPass

/-! # Native frame-to-directory computation for ordered label pairs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.PairDirectory

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- The three actual memory loads for a particular source and destination label
recover exactly their kind, first packet index and vertex number. -/
theorem Image.lookup {l : Layout} {orig mem : ℕ → ℕ} (h : Image l orig l.count mem)
    (u v : ℕ) (hu : u < l.Z) (hv : v < l.Z) :
    let addr := l.table+3*(u*l.Z+v)
    mem addr = kind l.d u v l.axes ∧ mem (addr+1) = firstPacketIndex l.d u v l.axes l.blocks ∧
      mem (addr+2) = vertexNo l.d u v l.axes := by
  have hq : u*l.Z+v < l.count := by
    have hb := Nat.mul_le_mul_right l.Z hu
    rw [Nat.succ_mul] at hb
    exact (Nat.add_lt_add_left hv _).trans_le hb
  have hz := Nat.zero_lt_of_lt hv
  have hd : (u*l.Z+v)/l.Z = u := by
    rw [Nat.mul_comm u, Nat.mul_add_div hz, Nat.div_eq_of_lt hv,Nat.add_zero]
  have hm : (u*l.Z+v)%l.Z = v := by
    rw [Nat.mul_comm u,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt hv]
  exact ⟨by simpa only [Layout.entry,hd,hm,Nat.add_zero] using h.fields _ hq 0 (by decide),
    by simpa only [Layout.entry,hd,hm] using h.fields _ hq 1 (by decide),
    by simpa only [Layout.entry,hd,hm] using h.fields _ hq 2 (by decide)⟩

/-- Load the declaration frame and construct the full public pair directory. -/
def directory : Code := .seq setup pass

/-- Every ordered pair has its three prescribed words in the table at frame
field 91. All memory outside the table agrees with the input memory. -/
theorem run_directory {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (l : Layout)
    (s : Bank w) (m : Memory w) (fit : l.Fits w) (hf : (pub 0).val = l.frame)
    (fields : l.Fields (readings m)) :
    BoundedRun pub mac directory s m
      (setup.slots+(2+l.count*(start.slots+l.axes*(body.slots+1)+1+commit.slots+1)))
      (RowState l (readings m) l.count) := by
  apply (run_setup pub mac l s m fit hf fields).seq
  intro t mt h
  have same : readings mt = readings m := h.2
  simpa only [same] using run_pass pub mac l t mt fit h.1

/-- Every terminating execution from the loaded frame produces the same complete
directory. The fixed instruction counts give the explicit native work bound. -/
theorem directory_image_of_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (l : Layout)
    {s t : Bank w} {m mt : Memory w} {es : List (TeamRAM.Event w)} (fit : l.Fits w) (hf : (pub 0).val = l.frame)
    (fields : l.Fields (readings m)) (run : Runs pub mac directory s m es t mt) :
    traceCost es ≤ 30 + l.count*(24+27*l.axes) ∧ RowState l (readings m) l.count (.ofWords t mt) := by
  obtain ⟨fs,u,mu,good,cap,rows⟩ := run_directory pub mac l s m fit hf fields
  obtain ⟨rfl,rfl,rfl⟩ := good.unique_of_deterministic (by decide) run
  refine ⟨cap.trans_eq ?_,rows⟩
  change 28+(2+l.count*(10+l.axes*(26+1)+1+12+1)) = 30 + l.count*(24+27*l.axes)
  ring

end Cube.PairDirectory

end BorderVNP
end Computability
end OAI
