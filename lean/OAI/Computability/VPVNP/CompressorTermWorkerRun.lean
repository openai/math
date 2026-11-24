import OAI.Computability.VPVNP.CompressorTermWorker
import OAI.Computability.VPVNP.CompressorTermWorkerFuel

/-!
# Native execution of a complete term-descriptor visit

The strided worker uses one fixed pass table for all motif ordinals.
Its only nondeterministic instructions read the selected outer vector.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.TermWorker

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM PrimedCounter
open MotifGrid MotifBlocks MotifConversion MotifSelector
open scoped Fin.CommRing

variable {k : Type*} [Field k] {J D S : Type} [Fintype J] [Fintype D] [Fintype S]
variable {a b : D → J} {P : Supply J S} {p : D → ℚ} {q : S → ℚ} {H H' : ℝ}
variable (B : FixedBlock k a b P (realWidths p) (realWidths q) H H')
variable {d n w : ℕ}

private noncomputable abbrev gridCode (order : Fin d ≃ D) := DemandGridRAM.code order (DemandGridRAM.fixedRows B)
private noncomputable abbrev gridWords (order : Fin d ≃ D) (w : ℕ) :=
  (DemandGridRAM.machine order p (DemandGridRAM.fixedRows B) w).publicData

private abbrev payloadCode (n : ℕ) :=
  PayloadWrite.storedCall n (B.scale*B.radius.num.natAbs) (MotifAdmission.denominator q)
private abbrev payloadWords (supply : Fin n ≃ S) (w : ℕ) := (PayloadWrite.storedMachine B supply w).publicData

private theorem components (order : Fin d ≃ D) (src dst row u : BurstRAM.Word w) (mem : Memory w)
    (fuel : ℕ) (gs rs : List (Event w))
    (h : TermRecord.headers B order src dst mem fuel = some
      [⟨gs,some row⟩,TermRecord.saved dst src row,⟨rs,some u⟩,TermRecord.saved (dst+1) (dst+2) u])
    (hgm : after mem gs = mem)
    (hrm : after (writeMemory mem dst row) rs = writeMemory mem dst row) :
    ∃ G R, Flow.Exec (gridWords B order w) src (gridCode B order) (fun _ => 0) mem gs G mem ∧
      G 1 = row ∧ Flow.Exec (DemandPreparation.publicWords order p B.scale w) src
        (DemandPreparation.repetitionCall d) (fun _ => 0) (writeMemory mem dst row) rs R (writeMemory mem dst row) ∧
      R 2 = u := by
  let grid := DemandGridRAM.machine order p (DemandGridRAM.fixedRows B) w
  let gf := 6*d+(11*d+4)*B.grid.demands.toList.length+8
  let reps := DemandPreparation.repetitionMachine order p B.scale w
  unfold TermRecord.headers at h
  change (execute grid.program gf (grid.program.start src) mem []).bind _ = _ at h
  cases hg : execute grid.program gf (grid.program.start src) mem [] with
  | none => simp [hg] at h
  | some gr =>
    cases gr with | mk ge grow =>
    cases grow with
    | none => simp [hg,bind] at h
    | some v =>
      rw [hg] at h
      simp only [Option.bind_some,bind] at h
      rw [(TermRecord.save_native dst src v _).1] at h
      simp only [Option.bind_some,TermRecord.saved] at h
      let mid := writeMemory (after mem ge) dst v
      change (execute reps.program fuel (reps.program.start src) mid []).bind _ = _ at h
      cases hr : execute reps.program fuel (reps.program.start src) mid [] with
      | none => simp [hr] at h
      | some rr =>
        cases rr with | mk re ru =>
        cases ru with
        | none => simp [hr] at h
        | some u' =>
          rw [hr] at h
          simp only [Option.bind_some] at h
          rw [(TermRecord.save_native (dst+1) (dst+2) u' _).1] at h
          simp only [Option.bind_some,pure,Option.some.injEq,List.cons.injEq,Report.mk.injEq] at h
          obtain ⟨⟨rfl,hv⟩,_,⟨rfl,hu⟩,_⟩ := h
          cases hv
          cases hu
          dsimp only [mid] at hr
          rw [hgm] at hr
          obtain ⟨G,mG,eG,gval,_,_⟩ := (Flow.template_execute_iff (gridCode B order) (some 1) (gridWords B order w)
            src (fun _ => 0) (fun _ => 0) mem gf [] ⟨ge,some row⟩).mp hg
          obtain ⟨R,mR,eR,rval,_,_⟩ := (Flow.template_execute_iff (DemandPreparation.repetitionCall d) (some 2)
            (DemandPreparation.publicWords order p B.scale w) src (fun _ => 0) (fun _ => 0)
            (writeMemory mem dst row) fuel [] ⟨re,some u⟩).mp hr
          rw [← Call.exec_memory eG,hgm] at eG
          rw [← Call.exec_memory eR,hrm] at eR
          exact ⟨G,R,eG,(Option.some.inj gval).symm,eR,(Option.some.inj rval).symm⟩

/-- The same finite instruction table handles every row at every machine width. -/
noncomputable def motifPass (order : Fin d ≃ D) (n : ℕ) : Schedule.Pass :=
  pass (gridCode B order) (DemandPreparation.repetitionCall d) (payloadCode B n)

/-- Assemble the address operands and grid, repetition, and payload constants for the selected
motif template. -/
noncomputable def motifData (order : Fin d ≃ D) (supply : Fin n ≃ S) (w : ℕ)
    (addr : Fin 4 → BurstRAM.Word w) : Fin (motifPass B order n).params → BurstRAM.Word w :=
  words addr (gridWords B order w) (DemandPreparation.publicWords order p B.scale w) (payloadWords B supply w)

/-- Instruction allowance for one fused term call at the given word width and maximum demand
width. -/
noncomputable def budget (d n w M : ℕ) :=
  15 + (6*d+(11*d+4)*B.grid.demands.toList.length+8) +
    (6*d+7*((∑ i, MotifAdmission.weight p i).size+2*Nat.clog 2 (M+1))+10) + PayloadWrite.storedFuel B n w

/-- For a fixed motif, the instruction cap grows linearly with machine word width. -/
theorem budget_linear (d n : ℕ) : ∃ A : ℕ, ∀ w M, M < 2^w →
    budget B d n w M ≤ A + (4*n+14)*w := by
  let c := B.grid.demands.toList.length
  let weights := (∑ i, MotifAdmission.weight p i).size
  refine ⟨15 + 6*d+(11*d+4)*c+8 + 6*d+7*weights+10 + n*12 +
    2*(B.scale*B.radius.num.natAbs).size + 4*(MotifAdmission.denominator q).size + 20,fun w M fit => ?_⟩
  have hlog : Nat.clog 2 (M+1) ≤ w := Nat.clog_le_of_le_pow fit
  have hp := PayloadWrite.storedFuel_le B n w
  unfold budget
  simp only [c,weights,Nat.mul_add,Nat.add_mul,Nat.mul_assoc] at *
  rw [show n*(4*w) = 4*(n*w) by ring] at hp
  omega

/-- Row arithmetic in a strided scan agrees with the natural addresses reduced to words. -/
theorem strided_addresses (w src dst srcStride dstStride i : ℕ) :
    let addr : Fin 4 → BurstRAM.Word w := ![src,srcStride,dst,dstStride]
    source addr (i : BurstRAM.Word w) = Fin.ofNat _ (src+i*srcStride) ∧
      base addr (i : BurstRAM.Word w) = Fin.ofNat _ (dst+i*dstStride) := by
  dsimp only
  change ((i : BurstRAM.Word w) * srcStride + src) = ((src+i*srcStride : ℕ) : BurstRAM.Word w) ∧
    ((i : BurstRAM.Word w) * dstStride + dst) = ((dst+i*dstStride : ℕ) : BurstRAM.Word w)
  simp [Nat.cast_add,Nat.cast_mul,add_comm]

/-- Every admitted tape returns the successor ordinal and the complete term
record. Conversely, at every sufficient cap, successful native calls consume
exactly the canonical outer-choice tapes. -/
theorem native (order : Fin d ≃ D) (supply : Fin n ≃ S)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    ∃ K : ℕ, ∀ M w, K+4*Nat.clog 2 (M+1) ≤ w → ∀ (addr : Fin 4 → BurstRAM.Word w)
      (j : BurstRAM.Word w) (mem : Memory w),
      let src := source addr j
      let dst := base addr j
      let demand := DemandPreparation.demandAt order src mem
      src.val+d ≤ 2^w → dst.val+2+n < 2^w → (src.val+d ≤ dst.val ∨ dst.val+2+n ≤ src.val) →
      (∀ e, demand e ≤ M) →
      let T := ((motifPass B order n).table.instantiate w (motifData B order supply w addr)).program
      ∃ (hw : outerCap B demand < 2^w) (row u : BurstRAM.Word w),
        B.grid.demands.toList[row.val]? = some (demandGrid B hp demand).val ∧ u.val = repetitions B demand ∧
        ∀ cap, budget B d n w M ≤ cap →
          (∀ bs, (execute T cap (T.start j) mem bs).isSome ↔
            ∃ v, (outerReader B supply hq demand w hw).read bs = some (v,[])) ∧
          ∀ v, ∃ es, execute T cap (T.start j) mem ((outerReader B supply hq demand w hw).encode v) =
            some ⟨es,some (j+1)⟩ ∧ after mem es = TermRecord.recordMemory mem dst row u supply v.val ∧
            choiceBits es = (outerReader B supply hq demand w hw).encode v ∧
            countProbes es ≤ d+B.grid.demands.toList.length*d+d+n+3 ∧ es.length < budget B d n w M := by
  obtain ⟨kh,headers⟩ := TermRecord.headers_native B order hp
  obtain ⟨kv,payload⟩ := PayloadWrite.stored_outer_paths B supply hq
  refine ⟨max kh kv,fun M w hW addr j mem hsrc hdst hsep hD => ?_⟩
  have hk := le_max_left kh kv
  have hk' := le_max_right kh kv
  let src := source addr j
  let dst := base addr j
  let demand := DemandPreparation.demandAt order src mem
  let gf := 6*d+(11*d+4)*B.grid.demands.toList.length+8
  let rf := 6*d+7*((∑ i, MotifAdmission.weight p i).size+2*Nat.clog 2 (M+1))+10
  obtain ⟨row,u,gs,rs,hrow,hu,hh,hgm,hrm,hgb,hrb,hgp,hrp,hgl,hrl⟩ :=
    headers M w (by omega) src dst mem hsrc (by dsimp only [src,dst] at *; omega) hD
  obtain ⟨G,R,hG,G₁,hR,R₂⟩ := components B order src dst row u mem rf gs rs hh hgm hrm
  let middle := TermRecord.withHeaders mem dst row u
  have payloadAddr : (dst+2).val = dst.val+2 := by
    have hfit : dst.val+2+n < 2^w := hdst
    have two : 2 < 2^w := by omega
    rw [Fin.val_add,show (2 : BurstRAM.Word w).val = 2 from Nat.mod_eq_of_lt two,Nat.mod_eq_of_lt (by omega)]
  have hread : (middle (dst+2-1).val).val = repetitions B demand := by
    rw [show dst+2-1 = dst+1 by ring]
    simp [middle,TermRecord.withHeaders,writeMemory,hu,demand]
  obtain ⟨hw,hs,paths⟩ := payload M demand hD w (by omega) (dst+2) middle
    (by rw [payloadAddr]; change dst.val+2+n < 2^w at hdst; omega) hread
  let pre := headerLog dst row u gs rs
  let T := ((motifPass B order n).table.instantiate w (motifData B order supply w addr)).program
  have hdr (cap bs rep) : execute T cap (T.start j) mem bs = some rep ↔
      ∃ vs V mv, Flow.Exec (payloadWords B supply w) (dst+2) (payloadCode B n) (fun _ => 0) middle vs V mv ∧
        rep = ⟨pre++vs,some (j+1)⟩ ∧ pre.length+vs.length < cap ∧ choiceBits vs = bs := by
    have hr' := hR
    rw [← G₁] at hr'
    have he := execute_iff (payloadCode B n) addr (gridWords B order w) (DemandPreparation.publicWords order p B.scale w)
      (payloadWords B supply w) j mem mem (writeMemory mem dst (G 1)) gs rs G R hG hgb hr' hrb cap bs rep
    dsimp only at he
    rw [G₁,R₂] at he
    exact he
  let pf := PayloadWrite.storedFuel B n w
  let Q := (PayloadWrite.storedMachine B supply w).program
  have part (bs : List Bool) (r : Report w) : execute Q pf (Q.start (dst+2)) middle bs = some r ↔
      ∃ V mv, Flow.Exec (payloadWords B supply w) (dst+2) (payloadCode B n) (fun _ => 0) middle r.events V mv ∧
        r.result = none ∧ r.events.length < pf ∧ choiceBits r.events = bs :=
    Flow.template_execute_iff (payloadCode B n) none (payloadWords B supply w) (dst+2) (fun _ => 0) (fun _ => 0)
      middle pf bs r
  have len : pre.length = 15+gs.length+rs.length := by simp [pre,headerLog]; omega
  have enough (vs : List (Event w)) (hlt : vs.length < pf) : pre.length+vs.length < budget B d n w M := by
    rw [len]
    change gs.length < gf at hgl
    change rs.length < rf at hrl
    change _ < 15+gf+rf+pf
    omega
  refine ⟨hw,row,u,hrow,hu,fun cap hcap => ⟨fun bs => ?_,fun v => ?_⟩⟩
  · rw [← hs bs,Option.isSome_iff_exists,Option.isSome_iff_exists]
    constructor
    · rintro ⟨r,he⟩
      obtain ⟨vs,V,mv,hv,_,_,hb⟩ := (hdr cap bs r).mp he
      exact ⟨⟨vs,none⟩,(part bs _).mpr ⟨V,mv,hv,rfl,PayloadWrite.storedCall_exec_length_lt B hv,hb⟩⟩
    · rintro ⟨r,he⟩
      obtain ⟨V,mv,hv,_,hlt,hb⟩ := (part bs r).mp he
      exact ⟨_,(hdr cap bs _).mpr ⟨r.events,V,mv,hv,rfl,(enough _ hlt).trans_le hcap,hb⟩⟩
  · obtain ⟨vs,run,hm,hp',hv,hb⟩ := paths v
    obtain ⟨V,mv,he,_,_,_⟩ := (part _ _).mp run
    have fits := enough vs hv
    refine ⟨pre++vs,(hdr _ _ _).mpr ⟨vs,V,mv,he,rfl,fits.trans_le hcap,hb⟩,?_,?_,?_,?_⟩
    · have first : after mem pre = middle := by
        simp only [pre,headerLog,after,List.foldl_append]
        change after (writeMemory (after (writeMemory (after mem gs) dst row) rs) (dst+1) u) [] = _
        rw [hgm,hrm]; rfl
      rw [show after mem (pre++vs) = after (after mem pre) vs from List.foldl_append,first]; exact hm
    · simp [pre,headerLog,Flow.choiceBits_append,hgb,hrb,hb,choiceBits,List.replicate_succ]
      rfl
    · simp [pre,headerLog,DemandPreparation.probes_append,hrp,hp',countProbes,List.replicate_succ]
      simp only [Finset.length_toList] at hgp
      omega
    · rwa [List.length_append]

end CompressorRecords.TermWorker

end VPVNP
end Computability
end OAI
