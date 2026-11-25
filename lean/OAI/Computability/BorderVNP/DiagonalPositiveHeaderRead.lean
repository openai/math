import OAI.Computability.BorderVNP.DiagonalNativeTimedModes
import OAI.Computability.BorderVNP.CubeScatterTransmissionHeader

/-! # All common-header coordinates of a nonzero physical evaluation product -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Pins RoutingISA.Evaluator ProcessorSlots Routing
open scoped BigOperators Classical

variable {R r t d link inner n w : ℕ} {Edge : Type} (G : Wiring R r t d link inner n Edge)
  (args : Fin (R+1) → UnitAddresses) (pin : Fin d → Bool) (ext : Exterior R r link → Bool)

/-- Original RAM word at a given position in the team's physical reference block. -/
noncomputable def headerReading (u : Fin (R+1)) (i : ℕ) : ℕ :=
  let f := G.transferFrame u (args u).header (args u).dst
  readings (modeMemory (w:=w) G args pin ext u) (f.addr f.partner i)

/-- Two accepted broadcasts agree at each physically reserved coordinate, through
the actual words shared by the two team input images. -/
theorem headerReading_eq {u v : Fin (R+1)} {base : ℕ} (i : ℕ)
    (fu : (G.transferFrame u (args u).header (args u).dst).Fits w base)
    (iu : i < (args u).header) (iv : i < (args v).header)
    (hu : (G.transferFrame u (args u).header (args u).dst).Agrees (readings (modeMemory (w:=w) G args pin ext u)))
    (hv : (G.transferFrame v (args v).header (args v).dst).Agrees (readings (modeMemory (w:=w) G args pin ext v))) :
    headerReading (w:=w) G args pin ext u i = headerReading (w:=w) G args pin ext v i := by
  by_cases same : u=v
  · rw [same]
  let p : Fin (r*link) := ⟨i,by simpa only [BroadcastFrame.capacity,Wiring.transferFrame,Nat.mul_comm] using iu.trans_le fu.cap⟩
  let A := G.processorFields u pin ext (args u).ibase (args u).hbase (args u).starbase
  let B := G.processorFields v pin ext (args v).ibase (args v).hbase (args v).starbase
  have shared := G.read_exterior_swap u v same pin ext _ _ _ _ _ _ (processorMemory A w) (processorMemory B w)
    (A.containsInput_initial w) (B.containsInput_initial w) p
  exact (hu v v.isLt (fun eq => same (Fin.ext eq.symm)) i iu).symm.trans
    ((congrArg Fin.val shared).trans (hv u u.isLt (fun eq => same (Fin.ext eq)) i iv))

/-- Every reference word is the bit of any chosen physical block, on the genuine
initial RAM image of the team. Hence there is one common entire bit list. -/
theorem headerReading_observed (L : WireLayout (R+1) r link) (hw : 0 < w)
    (width : ∀ u, (args u).header = L.header) (base : Fin (R+1) → ℕ)
    (fit : ∀ u, (G.transferFrame u (args u).header (args u).dst).Fits w (base u))
    (guard : ∀ u, (G.transferFrame u (args u).header (args u).dst).Agrees (readings (modeMemory (w:=w) G args pin ext u)))
    (fixed : Block (R+1)) (u : Fin (R+1)) (i : Fin L.header) :
    headerReading (w:=w) G args pin ext u i = ((L.exteriorEquiv ext).broadcast fixed i).toNat := by
  let lo := fixed.val.1
  let hi := fixed.val.2
  have lohi : lo < hi := fixed.property
  have near := headerReading_eq G args pin ext i.val (fit u) (i.isLt.trans_eq (width u).symm)
    (i.isLt.trans_eq (width lo).symm) (guard u) (guard lo)
  let A := G.processorFields lo pin ext (args lo).ibase (args lo).hbase (args lo).starbase
  have read := G.read_message_header L lo hi lohi.ne pin ext _ _ _ (processorMemory A w) (A.containsInput_initial w) hw i
  have edge : blockOf lo hi lohi.ne = fixed := by apply Subtype.ext; simp [blockOf,lohi,lo,hi]
  rw [edge] at read
  have same := guard lo hi hi.isLt (fun eq => lohi.ne (Fin.ext eq.symm)) i.val (i.isLt.trans_eq (width lo).symm)
  exact near.trans (same.symm.trans read)

/-- All positive agreeing teams read the same observed list, beginning with the
positive tag. Every equality refers to the original physical processor RAM. -/
theorem observed_positive (L : WireLayout (R+1) r link) (hw : 0<w)
    (sizes : ∀ i, (args i).header = L.header) (base : Fin (R+1) → ℕ)
    (fit : ∀ i, (G.transferFrame i (args i).header (args i).dst).Fits w (base i))
    (guards : ∀ i, (G.transferFrame i (args i).header (args i).dst).Agrees (readings (modeMemory (w:=w) G args pin ext i)))
    (tag : modeTag (w:=w) G args pin ext 0 ≠ 0) (fixed : Block (R+1)) :
    (∀ b, (L.exteriorEquiv ext).broadcast b = (L.exteriorEquiv ext).broadcast fixed) ∧
      (JointHeader.observed L ext fixed).head? = some true ∧
      ∀ u (j : Fin L.header), headerReading (w:=w) G args pin ext u j = ((L.exteriorEquiv ext).broadcast fixed j).toNat := by
  have read := headerReading_observed G args pin ext L hw sizes base fit guards
  have room := (fit 0).branch.trans_eq (sizes 0)
  have first := read fixed 0 ⟨0,room⟩
  change modeTag (w:=w) G args pin ext 0 = _ at first
  have on : (L.exteriorEquiv ext).broadcast fixed ⟨0,room⟩ = true := by
    cases z : (L.exteriorEquiv ext).broadcast fixed ⟨0,room⟩ with
    | false => exact (tag (first.trans (congrArg Bool.toNat z))).elim
    | true => rfl
  refine ⟨?_,?_,read fixed⟩
  · intro b
    funext j
    exact (show Function.Injective Bool.toNat by decide) ((read b 0 j).symm.trans (read fixed 0 j))
  · change (List.ofFn ((L.exteriorEquiv ext).broadcast fixed)).head? = some true
    rw [List.head?_eq_some_head (by simp [room.ne']),List.head_ofFn]
    exact congrArg some on

namespace ProcessorSlots

/-- A nonzero product of the actual positive evaluators determines the full common
header on every unordered block. Every true residual native machine received exactly
that copied list, with the tick charge subtracted from its original window. -/
theorem positive_product_header (physical : UniversalMachine.Program) {a e : ℕ} (eval : Code)
    (mac : TeamOpcode.Macros w 8) (S : SiteData R r 64 32 w a) (pack : Fin (R+1) → ReferencePacket w d)
    (fit : fitsWith physical 64 32 r w a R link n e) (args : Fin (R+1) → UnitAddresses)
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (L : WireLayout (R+1) r link)
    (fixed : Block (R+1)) (hw : 0 < w) (width : ∀ u, (args u).header = L.header) (he : eval.withoutAccept = true) :
    let P := (withStartup eval).program
    let G := wiringWith physical P (S.withPacket pack) d link n e fit
    let val := positiveMaskedNativeValue G eval mac S.publicWords S.registers args pin S.limit.val S.burst.val (n^25) ext
    let bits := JointHeader.observed L ext fixed
    (∀ u, (args u).Fitted G u (pack u) (S.publicWords u) (adviceOffsetWith physical r 32 64 w n)) →
    (∀ u, packetUnitBudget (args u).advice.count w (G.transferFrame u (args u).header (args u).dst)
      (G.pinLayout u (args u).ibase (args u).hbase (args u).starbase) ≤ S.limit.val) →
    (∏ u, val u) ≠ 0 →
    (∀ b, (L.exteriorEquiv ext).broadcast b = JointHeader.headerBits bits (JointHeader.observed_length ..)) ∧
      bits.head? = some true ∧ ∀ u, let f := G.transferFrame u (args u).header (args u).dst
        ∃ used bank mem, used ≤ jointBudget (args u).advice.count w+f.readTicks+2 ∧
          (G.processorFields u pin ext (args u).ibase (args u).hbase (args u).starbase).ContainsInput mem ∧
          Frame (G.pinLayout u (args u).ibase (args u).hbase (args u).starbase) (readings (S.publicWords u)) (readings mem) ∧
          JointHeader.FlatAt mem (args u).dst bits ∧
          val u = boundedValue eval (S.publicWords u) mac bank mem (S.limit.val-used) S.burst.val (n^25) := by
  intro P G val bits fitted time nz
  have live (u : Fin (R+1)) : val u ≠ 0 := fun hz => nz (Finset.prod_eq_zero (Finset.mem_univ u) hz)
  have residual := fun u => positiveMasked_residual physical eval mac S pack fit args pin ext u he (fitted u) (time u) (live u)
  obtain ⟨common,active,read⟩ := observed_positive G args pin ext L hw width (fun u => ((S.publicWords u) 0).val)
    (fun u => (fitted u).physical) (fun u => (residual u).2.1) (residual 0).1 fixed
  refine ⟨fun b => (common b).trans (JointHeader.observed_bits ..).symm,active,?_⟩
  · intro u f
    obtain ⟨used,bank,mem,ticks,physical',frame,copied,eq⟩ := (residual u).2.2
    refine ⟨used,bank,mem,ticks,physical',frame,JointHeader.flatAt_of_values hw mem (args u).dst bits ?_,eq⟩
    intro i
    have j : i.val < L.header := i.isLt.trans_eq (JointHeader.observed_length ..)
    exact (copied i.val (j.trans_eq (width u).symm)).trans ((read u ⟨i.val,j⟩).trans (by simp [bits,JointHeader.observed]))

end ProcessorSlots
end TeamContraction

end BorderVNP
end Computability
end OAI
