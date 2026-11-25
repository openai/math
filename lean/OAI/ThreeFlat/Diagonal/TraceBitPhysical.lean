import OAI.ThreeFlat.Diagonal.TraceBitAddresses
import OAI.ThreeFlat.Diagonal.TraceBitNetwork
import OAI.ThreeFlat.RAM.RawTickStartup

namespace OAI
/-! # Native startup for the same one-bit trace network used by the diagonal rank proof -/

namespace ThreeFlat.Diagonal.TraceBitPhysical

open Computability.VPVNP BurstRAM RAM TraceBitDescriptor
open scoped Fin.CommRing
noncomputable section
variable {F : Type} [Fintype F] [Field F] {w W p r k d S f : ℕ}
variable (hF : Fintype.card F ≤ 2^w) (hw : 3≤w+1) (hp : p≤2^(w+1))
    (hs : S≤2^w) (hf : f≤2^(w+1)) (base : ℕ) (st : Word w)
local notation "G" => TraceStaticRow.gateTable hF hw hp base f st r k d
local notation "srcs" => input (p:=p) (r:=r) (k:=k) (d:=d) hw hs hf base
local notation "fields" => records (p:=p) (r:=r) (k:=k) (d:=d) hw base S f
local notation "X" => TraceBitHeader.network hF hw hp base st hs hf r k d

theorem same_network : PhysicalTraceSource.expanded G srcs = X :=
  (TraceBitHeader.network_eq_guarded hF hw hp base st hs hf r k d).symm

variable (code : FieldCode F W) (source raw packed : ℕ)
local notation "P" => RawTickBuilder.contiguous X raw

/-- A deterministic native procedure receives only the bit tape of the local gates and
source-address formulas. Its output contains the physically numbered trace rows and links. -/
theorem startup (fit : RawTickStartup.Fits (w:=W) G srcs source raw packed)
    (safe : ∀ (v : Fin (2^d)) j,(fields j).Fits W v.val) :
    (RawTickStartup.procedure G code srcs source raw packed).Spec
      (fun m => ∀ i,m (source+i.val)=((FixedTraceImage.parameter G code fields i).toNat : Word W))
      (fun start out =>
        let tmp := FixedTraceImage.packed G code fields packed start
        let rawMem := fillSegment raw (11*(X).cells) (PhysicalTraceSource.rowWord X code raw) tmp
        RawTickBuilder.loaded X code raw rawMem ∧
          RawTickBuilder.Result X raw (P).lastBase (P).prevBase (P).dstBase rawMem out)
      (RawTickStartup.cost (w:=W) G srcs) := by
  intro pcs regs pubs M pc reg pub exit installed data c m start bits
  obtain ⟨n,hn,state,out,run,ret,good⟩ :=
    RawTickStartup.run G code fields srcs source raw packed fit safe (records_correct hw hs hf base)
      M pc reg pub exit installed data c m start bits
  refine ⟨n,hn,state,out,run,ret,?_⟩
  have eqN := same_network (r:=r) (k:=k) (d:=d) hF hw hp hs hf base st
  exact eqN ▸ good

end
end ThreeFlat.Diagonal.TraceBitPhysical

end OAI
