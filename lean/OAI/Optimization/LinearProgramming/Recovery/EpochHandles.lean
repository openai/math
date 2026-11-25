import OAI.Optimization.LinearProgramming.Recovery.PriceTransfer
import OAI.Optimization.LinearProgramming.Recovery.OddEpochModel
import OAI.Optimization.LinearProgramming.Recovery.BitEpoch
import OAI.Optimization.LinearProgramming.BitRAM.ReachablePrice
import OAI.Optimization.LinearProgramming.Geometry.WordService

/-! Service every price packet that the sealed finite bit program actually reaches,
using the real rational geometry and RAM cache and its dimension-only call clock. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PackedPCG

open RAM RAM.Tape RAM.Callable OracleSpec Contract BitRAM Geometry
open _root_.OAI.Optimization.LinearProgramming.Geometry.BorderBatch
open _root_.OAI.Optimization.LinearProgramming.Recovery.OracleInline

variable {r s n : ℕ} {D : Matrix (Fin r) (Fin n) ℚ} {E : Matrix (Fin s) (Fin n) ℚ}

noncomputable def sourceReply (S : Service D E) (initial : History ℚ) : Transcript→Word→Bool :=
  BitEpoch.reply S.serveWord initial

noncomputable def numericalEnv (S : Service D E) (x : LabelInput.Buffers r s n) (initial : History ℚ)
    (anchor : Fin n) (wordBase baseWidth increment : ℕ) : Environment ℚ where
  cache h numeric := let a:=BitEpoch.scan S.serveWord initial h
    a.stopped=false ∧ Stored S x a.state (baseWidth+h.length*increment) numeric
  ports vm := Ports anchor wordBase vm
  preserve := fun _ _ _ frame h=>h.preserve frame

noncomputable def eventReceipt (S : Service D E) (x : LabelInput.Buffers r s n) (initial : History ℚ)
    (baseWidth increment T : ℕ) (p : BitProgram) (bit : Bool) : Receipt p ℚ := fun c _ _ next=>
  let a:=BitEpoch.scan S.serveWord initial c.transcript
  ∃ after,Stored S x after (baseWidth+(c.transcript.length+1)*increment) next ∧ a.stopped=false ∧ c.transcript.length ≤ T ∧
    if bit then S.serveWord a.state c.bufferRev.reverse=.restart after else
      S.serveWord a.state c.bufferRev.reverse=.answer (sourceReply S initial c.transcript c.bufferRev.reverse) after

/-- `e` bounds only the actual input basis and all syntactically possible emitted
prices. The numerical scratch bound grows additively only with executed requests. -/
theorem native_handles (S : Service D E) (x : LabelInput.Buffers r s n) (p : BitProgram) (anchor : Fin n)
    (initial : History ℚ) (R T e baseWidth wordBase W : ℕ) (last : p.Config)
    (pcg : p.ComputesWithin (fun h w=>[sourceReply S initial h w]) (priceInput R anchor) T (pricePost R anchor))
    (hD : LinearIndependent ℚ D.row) (hrn : r ≤ n) (room : 256+T ≤ x.dual)
    (height : S.height ≤ baseWidth) (ready : RowRAM.Within S.height S.ready.memory)
    (arg : T+3 ≤ baseWidth) (encoded : T+3 ≤ e) (matrix : ∀i j,ratBits (D i j) ≤ e)
    (envelope : baseWidth+(T+1)*geometricIncrement r s n e S.outputBits ≤ W) :
    let Δ:=geometricIncrement r s n e S.outputBits
    Handles p (fun h w=>[sourceReply S initial h w]) (fun z=>ratBits z ≤ W)
      (numericalEnv S x initial anchor wordBase baseWidth Δ) (eventReceipt S x initial baseWidth Δ T p false)
      (eventReceipt S x initial baseWidth Δ T p true) (priceHandler S.program) (p.initial (priceInput R anchor)) last
      (transferTime r s n S.clock T) := by
  let f:=sourceReply S initial
  let bo : WordOracle:=fun h w=>[f h w]
  intro Δ c used time native vm reach _rest ok h s0 next u pre _suffix suspended uSafe _data stable
  have full:=reach.append (pre.run bo)
  obtain ⟨pc,living,ask⟩:=prefix_action pre
  obtain ⟨⟨i,prices,word⟩,spent⟩:=Dispatch.reachable_price_request f pcg full living ask
  change s0.bufferRev.reverse=priceQuery i prices at word
  change used+h+2+s0.bufferRev.reverse.length ≤ T at spent
  let price : PriceGame.Query n:=⟨prices,i⟩
  let h0:=s0.transcript
  let a:=BitEpoch.scan S.serveWord initial h0
  have same : h0=c.transcript:=pre.history
  have current : a.stopped=false ∧ Stored S x a.state (baseWidth+h0.length*Δ) native := by
    have cached:=ok.cache
    dsimp only [numericalEnv] at cached
    rw [←same] at cached
    exact cached
  have count : h0.length ≤ T := by
    have len:=(BitEpoch.run_follows full (.nil)).2
    change h0.length ≤ 0+(used+h) at len
    omega
  have short : (priceQuery i prices).length ≤ T := by rw [←word];omega
  have priceShort : (priceQuery price.index price.prices).length ≤ T := short
  have grown : baseWidth+h0.length*Δ+Δ=baseWidth+(h0.length+1)*Δ := by rw [Nat.add_mul];simp [Nat.add_assoc]
  have load : baseWidth+h0.length*Δ+Δ ≤ W := by
    rw [grown]
    exact (Nat.add_le_add_left (Nat.mul_le_mul_right Δ (Nat.succ_le_succ count)) baseWidth).trans envelope
  have ports : Ports anchor wordBase u:=ok.ports.preserve stable
  have clear : u.index statusReg=0:=(stable _ (by decide) (by decide)).trans ok.clean
  have headroom : baseWidth ≤ baseWidth+h0.length*Δ:=Nat.le_add_right _ _
  obtain ⟨m,v,call,cache',mark,portKeep⟩:=transfer_at_price S x price a.state native u suspended clear word ports.send
    ((Nat.add_le_add_left priceShort 256).trans room) (baseWidth+h0.length*Δ) e W current.2 hD hrn uSafe load
    ((Nat.add_le_add_right priceShort 3).trans (arg.trans headroom))
    ((Nat.add_le_add_right priceShort 3).trans encoded) matrix (height.trans headroom) ready
  have run:=call.mono (transferTime_mono r s n S.clock priceShort)
  have goodVM : Good (fun z=>ratBits z ≤ W) v := fun j=>by simpa only [Odd.data_slot] using call.safe_end (Odd.slot j)
  have goodNative : m.AllData (fun z=>ratBits z ≤ W) := fun j=>by simpa only [Odd.data_even] using call.safe_end (2*j)
  rw [grown] at cache'
  let result:=(S.priceStep a.state price).2
  have serve : S.serveWord a.state s0.bufferRev.reverse=Service.toReply (S.priceStep a.state price).1 result :=
    (congrArg (S.serveWord a.state) word).trans (S.serveWord_priceQuery a.state i prices)
  have retained:=ports.of_preserved portKeep
  refine ⟨m,v,run,?_⟩
  cases which : (S.priceStep a.state price).1 with
  | none =>
    have bad : S.serveWord a.state s0.bufferRev.reverse=.restart result:=by simpa [Service.toReply,which] using serve
    have observed : eventReceipt S x initial baseWidth Δ T p true s0 next native m:=⟨result,cache',current.1,count,bad⟩
    rw [which] at mark
    exact .interrupted observed goodNative goodVM mark.1 (by rw [mark.2];decide) retained
  | some b =>
    have active : (BitEpoch.scan S.serveWord initial s0.transcript).stopped=false := current.1
    have normal : S.serveWord (BitEpoch.scan S.serveWord initial s0.transcript).state s0.bufferRev.reverse=.answer b result := by
      simpa [Service.toReply,which] using serve
    have expected : sourceReply S initial s0.transcript s0.bufferRev.reverse=b := by
      simp [sourceReply,BitEpoch.reply,active,normal]
    have observed : eventReceipt S x initial baseWidth Δ T p false s0 next native m:=by
      refine ⟨result,cache',current.1,count,?_⟩
      simp only [Bool.false_eq_true,ite_false,expected]
      exact normal
    rw [which] at mark
    have answered : Dispatch.answered bo s0 next=receivedConfig p s0 next [b] := by
      calc
        _ = receivedConfig p s0 next [sourceReply S initial s0.transcript s0.bufferRev.reverse] := rfl
        _ = _ := congrArg (fun bit : Bool => receivedConfig p s0 next [bit]) expected
    have forward : BitEpoch.scan S.serveWord initial ((s0.bufferRev.reverse,[b])::s0.transcript)=
        ⟨result,false,(BitEpoch.scan S.serveWord initial s0.transcript).events++[(s0.bufferRev.reverse,some b)]⟩ := by
      simp [BitEpoch.scan,active,normal]
    have live : Live p (fun z=>ratBits z ≤ W) (numericalEnv S x initial anchor wordBase baseWidth Δ)
        (Dispatch.answered bo s0 next) m v := by
      rw [answered]
      refine ⟨mark.1,goodVM,goodNative,retained,?_,mark.2⟩
      change (BitEpoch.scan S.serveWord initial ((s0.bufferRev.reverse,[b])::s0.transcript)).stopped=false ∧
        Stored S x (BitEpoch.scan S.serveWord initial ((s0.bufferRev.reverse,[b])::s0.transcript)).state
          (baseWidth+((s0.bufferRev.reverse,[b])::s0.transcript).length*Δ) m
      rw [forward]
      exact ⟨rfl,cache'⟩
    exact .answered observed live

end PackedPCG
end Recovery
end LinearProgramming
end Optimization
end OAI
