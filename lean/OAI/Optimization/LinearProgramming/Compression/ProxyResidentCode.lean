import OAI.Optimization.LinearProgramming.RAM.CallHeader
import OAI.Optimization.LinearProgramming.Compression.ServiceAddressPlan
import OAI.Optimization.LinearProgramming.Compression.ServiceSlotMoves

/-! Fixed native instructions for installing the ordinary numerical cache in its
nested resident lanes. This executable definition is independent of the query proof. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace ResidentInstall

open RAM GeneratorTable

def capture : List AddressSet := [.read 10 102,.read 11 103,.read 12 104,.read 13 105]
def setup : List AddressSet := [.next 1 2,.next 1 1,.fix 3 0,.fix 8 15,.fix 14 60]
def publish : List AddressSet := [.read 57 10,.read 59 11,.read 61 12,.read 63 13]

/-- Save all four public metadata words, build the two physical cursors by two counted
doublings, and initialize the scalar zero and the finite scatter-control addresses. -/
def startBlock : Block := .seq (addressPlan capture) (.seq (Call.doubleHeaderEntry 1 0)
  (.seq (Call.doubleHeaderEntry 2 1) (.seq (addressPlan setup) (.op (.const 1 0)))))

def finishBlock : Block := addressPlan publish

def selectAddress : Block :=
  .branch (.addrLT 0 14) (.op (.addrConst 4 0)) (.op (.addrLoad 4 0))
def plusTwo : List SlotMove := [.incr 7 7,.incr 7 7]

/-- Register 7 receives the physical address value `4*x+2`. -/
def encodeResidentAddress : Block := .seq selectAddress <| .seq (Call.doubleHeaderEntry 6 4) <|
  .seq (Call.doubleHeaderEntry 7 6) (slotMoves plusTwo)

def writePair : Block := .seq (.op (.addrStore 1 7)) <| .seq (.op (.addrStore 2 3)) <|
  .seq (.op (.load 0 0)) <| .seq (.op (.store 1 0)) (.op (.store 2 1))

def retreat : List SlotMove :=
  [.decr 0 0,.decr 1 1,.decr 1 1,.decr 1 1,.decr 1 1,.decr 2 2,.decr 2 2,.decr 2 2,.decr 2 2]

def scatterResidentRow : Block := .seq encodeResidentAddress (.seq writePair (slotMoves retreat))

def scatterResidentLoop : Block := .loop (.addrLT 8 0) scatterResidentRow

end ResidentInstall
end Compression
end LinearProgramming
end Optimization
end OAI

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire

open RAM ResidentInstall

/-- The original logical prefix is read in descending order, permitting in-place
expansion to nested lanes with two index encodings. -/
def installResident : Block := .seq startBlock (.seq scatterResidentLoop finishBlock)

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI
