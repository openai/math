import OAI.Computability.BorderVNP.CellPacketLoad
import OAI.Computability.BorderVNP.CellPacketEncode
import OAI.Computability.BorderVNP.CellPacketCopy
import OAI.Computability.BorderVNP.CellPacketCopyHeader

/-! # Dispatch of sparse cell sources in the physical word machine -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellPacket

open VPVNP.BurstRAM CellPacketEncode

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

/-- A public word range is encoded in place. A private box length is decoded from
the actual received header before copying the opaque payload. -/
def dispatch : Code := .ifEq 10 0 (encoder true) (.seq CellPacketCopy.header (CellPacketCopy.copy true))

/-- The full native iteration first obtains its three-word descriptor. -/
def oneChunk : Code := .seq loadChunk dispatch

/-- Shared postcondition of the public encoder and private box reader. -/
def emitted (s : Bank w) (m : Memory w) (bits : List Bool) (z : NatState) : Prop :=
  Persistent (readings s) z.reg ∧ z.reg 2 = readings s 2 ∧
  z.reg 20 = readings s 20 + bits.length ∧ z.mem = putDigits (readings m) (readings s 20) bits

private theorem branch_run {s : Bank w} {m : Memory w} {x y : Reg} {a b : Code}
    {d : ℕ} {P : NatState → Prop}
    (run : BoundedRun pub macros (if s x = s y then a else b) s m d P) :
    BoundedRun pub macros (.ifEq x y a b) s m (1+d) P := by
  obtain ⟨es,t,mt,h,hr,hp⟩ := run
  exact ⟨_,t,mt,.ifEq h,Nat.add_le_add_left hr 1,hp⟩

private theorem header_persistent {r t : Reg → ℕ}
    (h : ∀ j, j≠14 → j≠15 → j≠16 → j≠21 → j≠22 → t j = r j) :
    Persistent r t := by
  intro i hi
  have small : i.val ≤ 9 ∨ i=18 := hi.imp And.left id
  apply h <;> intro he <;> subst i <;> norm_num at small

/-- Execute one selected encoder, deriving the source length of a private range
entirely from its RAM contents. -/
theorem dispatch_run (c : Chunk) (s : Bank w) (m : Memory w) (hc : Constants (readings s))
    (kind : readings s 10 = c.kind) (base : readings s 14 = c.base)
    (stop : readings s 15 = c.base + c.count) (input : c.Stored (readings m))
    (apart : c.endSource ≤ readings s 20) (fit : readings s 20 + (tags true c.bits).length < 2^w) :
    BoundedRun pub macros dispatch s m (c.work w) (emitted s m (tags true c.bits)) := by
  cases c with
  | words a xs =>
    have eq : s 10 = s 0 := Fin.ext (kind.trans hc.1.symm)
    have run := encoder_run (pub := pub) (macros := macros) true xs a (readings s 20) s m hc base stop rfl
      (fun i hi => input ⟨i,hi⟩) (.inl apart) fit
    unfold dispatch
    apply (branch_run (x := 10) (y := 0) (b := .seq CellPacketCopy.header (CellPacketCopy.copy true))
      (by simpa [eq] using run)).mono
    · simp only [Chunk.work]; nlinarith
    · intro z h
      exact ⟨persistent_of_fixed h.fixed, h.fixed 2 (by decide) (by decide) (by decide) (by decide),
        h.destination,h.memory⟩
  | box a H bs =>
    have neq : s 10 ≠ s 0 := fun he => Nat.one_ne_zero (kind.symm.trans ((congrArg Fin.val he).trans hc.1))
    have s14 : readings s 14 = a := base
    have s15 : readings s 15 = a+H := stop
    change readings s 20 + (tags true bs).length < 2^w at fit
    have endLe : a+H+bs.length ≤ readings s 20 := apart
    obtain ⟨fitHeader,head,body⟩ := input
    have run := CellPacketCopy.headerRun (pub := pub) (macros := macros) s m H bs.length hc
      (by rw [s14,s15]) (by simpa only [s14] using head) fitHeader
      (by have h := (s 20).isLt; change readings s 20 < 2^w at h; omega)
    have both := run.seq (Q := emitted s m (tags true bs)) (t := 7*bs.length+1) (b := CellPacketCopy.copy true)
      (fun t mt ⟨fix,t14,t15,mem⟩ => by
        change readings mt = readings m at mem
        change readings t 14 = readings s 15 at t14
        change readings t 15 = readings s 15 + bs.length at t15
        have per := header_persistent fix
        have t20 : readings t 20 = readings s 20 := fix 20 (by decide) (by decide) (by decide) (by decide) (by decide)
        have copy := CellPacketCopy.copy_run (pub := pub) (macros := macros) true t mt bs (per.constants hc)
          (by rw [t15,t14]) (by simpa only [mem,t14,s15] using body)
          (.inl (by simpa only [t14,s15,t20] using endLe)) (by simpa only [t20] using fit)
        apply copy.mono le_rfl
        rintro z ⟨fixed,_,dst,out⟩
        refine ⟨per.trans (persistent_of_fixed fixed),?_,?_,?_⟩
        · exact (fixed 2 (by decide) (by decide) (by decide) (by decide)).trans
            (fix 2 (by decide) (by decide) (by decide) (by decide) (by decide))
        · simpa only [t20] using dst
        · simpa only [mem,t20] using out)
    unfold dispatch
    apply (branch_run (x := 10) (y := 0) (a := encoder true) (by simpa [neq] using both)).mono
    · simp only [Chunk.work]; omega
    · exact fun _ h => h

/-- Actual RAM descriptor load and both data-source cases under one cost bound. -/
theorem oneChunk_run (c : Chunk) (s : Bank w) (m : Memory w) (a : ℕ)
    (cursor : readings s 2 = a) (hc : Constants (readings s)) (row : WordsAt (readings m) a c.descriptor)
    (input : c.Stored (readings m)) (endDesc : a+3 < 2^w) (apart : c.endSource ≤ readings s 20)
    (fit : readings s 20 + (tags true c.bits).length < 2^w) :
    BoundedRun pub macros oneChunk s m (7+c.work w) (fun z =>
      Persistent (readings s) z.reg ∧ z.reg 2 = a+3 ∧ z.reg 20 = readings s 20 + (tags true c.bits).length ∧
      z.mem = putDigits (readings m) (readings s 20) (tags true c.bits)) := by
  apply (loadChunk_run pub macros s m c a cursor hc row endDesc (apart.trans_lt (s 20).isLt)).seq
  rintro t mt ⟨per,cur,kind,src,stop,dst,mem⟩
  change readings t 20 = readings s 20 at dst
  change readings mt = readings m at mem
  apply (dispatch_run (pub := pub) (macros := macros) c t mt (per.constants hc) kind src stop
    (mem ▸ input) (dst ▸ apart) (dst ▸ fit)).mono le_rfl
  rintro z ⟨hp,hc,hd,hm⟩
  exact ⟨per.trans hp,hc.trans cur,by simpa only [dst] using hd,by simpa only [mem,dst] using hm⟩

end RoutingISA.CellPacket

end BorderVNP
end Computability
end OAI
