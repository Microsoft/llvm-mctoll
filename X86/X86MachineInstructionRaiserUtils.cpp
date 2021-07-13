//===-- X86MachineInstructionRaiserUtils.cpp ---------------------*- C++-*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file contains the various utility/helper functions declared in
// X86MachineInstructionRaiser class for use by llvm-mctoll.
//
//===----------------------------------------------------------------------===//

#include "ExternalFunctions.h"
#include "InstMetadata.h"
#include "X86MachineInstructionRaiser.h"
#include "X86RaisedValueTracker.h"
#include "X86RegisterUtils.h"
#include "llvm-mctoll.h"
#include "llvm/Object/ELF.h"
#include "llvm/Object/ELFObjectFile.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include <X86InstrBuilder.h>
#include <X86Subtarget.h>
#include <iterator>

#define DEBUG_TYPE "mctoll"

using namespace llvm;
using namespace mctoll;
using namespace X86RegisterUtils;

Value *X86MachineInstructionRaiser::getMemoryRefValue(const MachineInstr &MI) {
  const MCInstrDesc &MIDesc = MI.getDesc();
  unsigned int Opcode = MI.getOpcode();

  int LoadOrStoreOpIndex = -1;

  // Get index of memory reference in the instruction.
  int MemoryRefOpIndex = getMemoryRefOpIndex(MI);
  // Should have found the index of the memory reference operand
  assert(MemoryRefOpIndex != -1 && "Unable to find memory reference "
                                   "operand of a load/store instruction");
  X86AddressMode MemRef = llvm::getAddressFromInstr(&MI, MemoryRefOpIndex);

  // Get the operand whose value is stored to memory or that is loaded from
  // memory.

  if (MIDesc.mayStore()) {
    // If the instruction stores to stack, find the register whose value is
    // being stored. It would be the operand at offset
    // memRefOperandStartIndex + X86::AddrNumOperands
    LoadOrStoreOpIndex = MemoryRefOpIndex + X86::AddrNumOperands;
  } else if (MIDesc.mayLoad()) {
    // If the instruction loads to memory to a register, it has 1 def.
    // Operand 0 is the loadOrStoreOp.
    assert(((MIDesc.getNumDefs() == 0) || (MIDesc.getNumDefs() == 1)) &&
           "Instruction that loads from memory expected to have only "
           "one target");
    if (MIDesc.getNumDefs() == 1) {
      LoadOrStoreOpIndex = 0;
      assert(MI.getOperand(LoadOrStoreOpIndex).isReg() &&
             "Target of instruction that loads from "
             "memory expected to be a register");
    } else if (!MIDesc.isCompare() && !MIDesc.isCall()) {
      switch (getInstructionKind(Opcode)) {
      case InstructionKind::DIVIDE_MEM_OP:
      case InstructionKind::LOAD_FPU_REG:
      case InstructionKind::SSE_COMPARE_RM:
        break;
      default:
        MI.print(errs());
        assert(false && "Encountered unhandled memory load instruction");
      }
    }
  } else {
    MI.print(errs());
    assert(false && "Encountered unhandled instruction that is not load/store");
  }

  Value *MemoryRefValue = nullptr;

  if (MemRef.BaseType == X86AddressMode::RegBase) {
    // If it is a stack reference, allocate a stack slot in case the current
    // memory reference is new. Else get the stack reference using the
    // stackslot index of the previously known stack ref.

    uint64_t BaseSupReg = find64BitSuperReg(MemRef.Base.Reg);
    if (BaseSupReg == x86RegisterInfo->getStackRegister() ||
        BaseSupReg == x86RegisterInfo->getFramePtr()) {
      MemoryRefValue = getStackAllocatedValue(MI, MemRef, false);

      // If memory operand has an index register with possibly a non-zero scale
      // value, add the value represented by IndexReg*Scale to MemoryRefValue.
      if (MemRef.IndexReg != X86::NoRegister) {
        assert((MemoryRefValue != nullptr) &&
               "Unexpected null value of stack or base pointer register");
        Type *MemRefValTy = MemoryRefValue->getType();
        assert((MemRefValTy->isPointerTy()) &&
               "Unexpected non-pointer type of a stack allocated value");
        // Convert MemRefValue to integer
        LLVMContext &Ctx(MF.getFunction().getContext());
        Type *CastTy = Type::getInt64Ty(Ctx);
        BasicBlock *RaisedBB = getRaisedBasicBlock(MI.getParent());
        PtrToIntInst *MemRefValAddr =
            new PtrToIntInst(MemoryRefValue, CastTy, "", RaisedBB);

        unsigned ScaleAmt = MemRef.Scale;
        // IndexReg * Scale
        Value *IndexVal = getPhysRegValue(MI, MemRef.IndexReg);
        // Cast IndexRegVal as 64-bit integer, if needed.
        IndexVal = getRaisedValues()->castValue(IndexVal, CastTy, RaisedBB);

        // Generate mul instruction based on Scale value
        switch (ScaleAmt) {
        case 0:
          assert(false && "Unexpected zero-value of scale in memory operand");
          break;
        case 1:
          break;
        default: {
          Value *ScaleAmtValue = ConstantInt::get(CastTy, ScaleAmt);
          Instruction *MulInst = BinaryOperator::CreateMul(
              ScaleAmtValue, IndexVal, "sc-m", RaisedBB);
          IndexVal = MulInst;
        } break;
        }

        // MemoryRefValue + IndexReg*Scale
        Instruction *AddInst = BinaryOperator::CreateAdd(
            MemRefValAddr, IndexVal, "idx-a", RaisedBB);
        // Propagate any rodata related metadata
        getRaisedValues()->setInstMetadataRODataIndex(MemoryRefValue, AddInst);
        // Cast the computed address back to MemRefValTy
        MemoryRefValue =
            getRaisedValues()->castValue(AddInst, MemRefValTy, RaisedBB);
      }
    }
    // Handle PC-relative addressing.

    // NOTE: This tool now raises only shared libraries and executables -
    // NOT object files. So, instructions with 0 register (which typically
    // are seen in a relocatable object file for the linker to patch) are
    // not expected to be encountered.
    else if (BaseSupReg == X86::RIP) {
      MemoryRefValue = createPCRelativeAccesssValue(MI);
    }

    // If this is neither a stack reference nor a pc-relative access, get the
    // associated memory address expression value.
    if (MemoryRefValue == nullptr) {
      Value *memrefValue = getMemoryAddressExprValue(MI);
      MemoryRefValue = memrefValue;
    }
  } else {
    // TODO : Memory references with BaseType FrameIndexBase
    // (i.e., not RegBase type)
    outs() << "****** Unhandled memory reference in instruction\n\t";
    LLVM_DEBUG(MI.dump());
    outs() << "****** reference of type FrameIndexBase";
  }

  assert(MemoryRefValue != nullptr &&
         "Unable to construct memory referencing value");

  return MemoryRefValue;
}

Value *X86MachineInstructionRaiser::loadMemoryRefValue(
    const MachineInstr &MI, Value *MemRefValue, unsigned int MemoryRefOpIndex,
    Type *SrcTy) {
  X86AddressMode MemRef = llvm::getAddressFromInstr(&MI, MemoryRefOpIndex);
  uint64_t BaseSupReg = find64BitSuperReg(MemRef.Base.Reg);
  bool IsPCRelMemRef = (BaseSupReg == X86::RIP);

  // Load the value from memory location of memRefValue.
  // memRefVal is either an AllocaInst (stack access), GlobalValue (global
  // data access), an effective address value, element pointer or select
  // instruction.
  assert((isa<AllocaInst>(MemRefValue) || isEffectiveAddrValue(MemRefValue) ||
          isa<GlobalValue>(MemRefValue) || isa<SelectInst>(MemRefValue) ||
          isa<GetElementPtrInst>(MemRefValue) ||
          MemRefValue->getType()->isPointerTy()) &&
         "Unexpected type of memory reference in SSE conversion instruction");

  // Assume that MemRefValue represents a memory reference location and hence
  // needs to be loaded from.
  bool LoadFromMemrefValue = true;
  // Following are the exceptions when MemRefValue needs to be considered as
  // memory content and not as memory reference.
  if (IsPCRelMemRef) {
    // If it is a PC-relative global variable with an initializer, it is memory
    // content and should not be loaded from.
    if (auto GV = dyn_cast<GlobalVariable>(MemRefValue))
      LoadFromMemrefValue = !(GV->hasInitializer());
      // If it is not a PC-relative constant expression accessed using
      // GetElementPtrInst, it is memory content and should not be loaded from.
    else {
      const ConstantExpr *CExpr = dyn_cast<ConstantExpr>(MemRefValue);
      if (CExpr != nullptr) {
        LoadFromMemrefValue =
            (CExpr->getOpcode() == Instruction::GetElementPtr);
      }
    }
  }

  if (LoadFromMemrefValue) {
    BasicBlock *RaisedBB = getRaisedBasicBlock(MI.getParent());

    // If it is an effective address value or a select instruction, convert it
    // to a pointer to load register type.
    PointerType *PtrTy = PointerType::get(SrcTy, 0);
    if ((isEffectiveAddrValue(MemRefValue)) || isa<SelectInst>(MemRefValue)) {
      IntToPtrInst *ConvIntToPtr = new IntToPtrInst(MemRefValue, PtrTy);
      // Set or copy rodata metadata, if any
      getRaisedValues()->setInstMetadataRODataIndex(MemRefValue, ConvIntToPtr);
      RaisedBB->getInstList().push_back(ConvIntToPtr);
      MemRefValue = ConvIntToPtr;
    }
    assert(MemRefValue->getType()->isPointerTy() &&
           "Pointer type expected in SSE conversion instruction");
    // Cast the pointer to match the size of memory being accessed by the
    // instruction, as needed.
    MemRefValue = getRaisedValues()->castValue(MemRefValue, PtrTy, RaisedBB);
    // Load the value from memory location
    Type *LdTy = MemRefValue->getType()->getPointerElementType();
    LoadInst *LdInst =
        new LoadInst(LdTy, MemRefValue, "memload", false, Align());
    LdInst = getRaisedValues()->setInstMetadataRODataContent(LdInst);
    RaisedBB->getInstList().push_back(LdInst);

    return LdInst;
  } else {
    // memRefValue already represents the global value loaded from
    // PC-relative memory location. It is incorrect to generate an
    // additional load of this value. It should be directly used.
    return MemRefValue;
  }
}

// Delete noop instructions
bool X86MachineInstructionRaiser::deleteNOOPInstrMI(
    MachineBasicBlock &MBB, MachineBasicBlock::iterator MBBI) {
  MachineInstr &MI = *MBBI;
  if (isNoop(MI.getOpcode())) {
    MBB.remove(&MI);
    return true;
  }
  return false;
}

bool X86MachineInstructionRaiser::deleteNOOPInstrMF() {
  bool modified = false;
  for (MachineBasicBlock &MBB : MF) {
    // MBBI may be invalidated by the raising operation.
    MachineBasicBlock::iterator MBBI = MBB.begin(), E = MBB.end();
    while (MBBI != E) {
      MachineBasicBlock::iterator NMBBI = std::next(MBBI);
      modified |= deleteNOOPInstrMI(MBB, MBBI);
      MBBI = NMBBI;
    }
  }
  return modified;
}

bool X86MachineInstructionRaiser::unlinkEmptyMBBs() {
  bool modified = false;
  std::set<unsigned> EmptyMBBNos;
  // Collect empty basic block numbers
  for (MachineBasicBlock &MBB : MF) {
    if (MBB.empty())
      EmptyMBBNos.insert(MBB.getNumber());
  }
  // Get rid of any empty MachineBasicBlocks
  if (!EmptyMBBNos.empty()) {
    for (auto MBBNo : EmptyMBBNos) {
      MachineBasicBlock *DelMBB = MF.getBlockNumbered(MBBNo);
      // Transfer all successors of DelMBB as successors of each of the
      // predecessors of DelMBB.
      if (DelMBB->pred_size() > 0) {
        for (auto DelMBBPred : DelMBB->predecessors()) {
          DelMBBPred->transferSuccessors(DelMBB);
        }
      } else {
        // If DelMBB does not have any predecessors, successors of DelMBB would
        // not be deleted since transferAllSuccessors will not be called. So, we
        // need to explicitly delete all successors of DelMBB.
        for (auto DelMBBSucc : DelMBB->successors()) {
          DelMBB->removeSuccessor(DelMBBSucc);
        }
      }
      // Do not delete DelMBB
    }
    modified = true;
  }
  return modified;
}

// Return the Type of the physical register.
Type *X86MachineInstructionRaiser::getPhysRegType(unsigned int PReg) {
  LLVMContext &Ctx(MF.getFunction().getContext());

  if (is64BitPhysReg(PReg))
    return Type::getInt64Ty(Ctx);
  if (is32BitPhysReg(PReg))
    return Type::getInt32Ty(Ctx);
  if (is16BitPhysReg(PReg))
    return Type::getInt16Ty(Ctx);
  if (is8BitPhysReg(PReg))
    return Type::getInt8Ty(Ctx);
  if (isSSE2Reg(PReg)) {
    // Since float- and double types both use the same width SSE registers, we
    // can't check which one is correct. Use getPhysSSERegType with a
    // BitPrecision argument
    return Type::getDoubleTy(Ctx);
  }

  assert(false && "Immediate operand of unknown size");
  return nullptr;
}

Type *X86MachineInstructionRaiser::getPhysSSERegType(unsigned int PhysReg,
                                                     uint8_t BitPrecision) {
  LLVMContext &Ctx(MF.getFunction().getContext());

  assert(isSSE2Reg(PhysReg) && "Expected SSE2 register");

  switch (BitPrecision) {
  case 64:
    return Type::getDoubleTy(Ctx);
  case 32:
    return Type::getFloatTy(Ctx);
  default:
    llvm_unreachable("Unhandled bit precision");
    return nullptr;
  }
}

Type *X86MachineInstructionRaiser::getImmOperandType(const MachineInstr &MI,
                                                     unsigned int OpIndex) {
  LLVMContext &Ctx(MI.getMF()->getFunction().getContext());
  MachineOperand Op = MI.getOperand(OpIndex);
  assert(Op.isImm() && "Attempt to get size of non-immediate operand");

  uint8_t ImmSize = X86II::getSizeOfImm(MI.getDesc().TSFlags);
  switch (ImmSize) {
  case 8:
    return Type::getInt64Ty(Ctx);
  case 4:
    return Type::getInt32Ty(Ctx);
  case 2:
    return Type::getInt16Ty(Ctx);
  case 1:
    return Type::getInt8Ty(Ctx);
  default:
    llvm_unreachable("Immediate operand of unknown size");
  }
}

uint8_t
X86MachineInstructionRaiser::getPhysRegOperandSize(const MachineInstr &MI,
                                                   unsigned int OpIndex) {
  MachineOperand Op = MI.getOperand(OpIndex);
  assert(Op.isReg() && "Attempt to get size of non-register operand");
  return (getPhysRegSizeInBits(Op.getReg()) / sizeof(uint64_t));
}

Type *X86MachineInstructionRaiser::getPhysRegOperandType(const MachineInstr &MI,
                                                         unsigned int OpIndex) {
  MachineOperand Op = MI.getOperand(OpIndex);
  assert(Op.isReg() && "Attempt to get type of non-register operand");

  LLVMContext &Ctx(MI.getMF()->getFunction().getContext());
  auto PReg = Op.getReg();
  if (isGPReg(PReg))
    return Type::getIntNTy(Ctx, getPhysRegSizeInBits(Op.getReg()));
  else if (isSSE2Reg(PReg)) {
    auto Precision = getInstructionBitPrecision(MI.getDesc().TSFlags);
    if (Precision == 32)
      return Type::getFloatTy(Ctx);
    else if (Precision == 64)
      return Type::getDoubleTy(Ctx);
    llvm_unreachable("Unexpected memory operation size of instruction that "
                     "uses SSE register");
  }

  llvm_unreachable("Unhandled register type encountered");
}

bool X86MachineInstructionRaiser::isPushToStack(const MachineInstr &MI) const {
  return instrNameStartsWith(MI, "PUSH") || instrNameStartsWith(MI, "ENTER");
}

bool X86MachineInstructionRaiser::isPopFromStack(const MachineInstr &MI) const {
  return instrNameStartsWith(MI, "POP") || instrNameStartsWith(MI, "LEAVE");
}

bool X86MachineInstructionRaiser::isEffectiveAddrValue(Value *Val) {
  if (isa<LoadInst>(Val))
    return true;

  // A call may return a pointer that can be considered an effective address.
  if (isa<CallInst>(Val))
    return true;

  // An instruction that casts a pointer value may be considered as an effective
  // address.
  if (isa<PtrToIntInst>(Val)) {
    return (dyn_cast<PtrToIntInst>(Val)->getSrcTy()->isPointerTy());
  }

  if (isa<BinaryOperator>(Val)) {
    BinaryOperator *BinOpVal = dyn_cast<BinaryOperator>(Val);
    if (BinOpVal->isBinaryOp(BinaryOperator::Add) ||
        BinOpVal->isBinaryOp(BinaryOperator::Mul)) {
      return true;
    }
  }

  // Consider an argument of integer type to be an address value type.
  if (Val->getType()->isIntegerTy() && (Val->getName().startswith("arg")))
    return true;

  return false;
}

bool X86MachineInstructionRaiser::recordDefsToPromote(unsigned PhysReg,
                                                      unsigned MBBNo,
                                                      Value *Alloca) {
  reachingDefsToPromote.insert(std::make_tuple(PhysReg, MBBNo, Alloca));
  return true;
}

// Return the MachineInstr if MBB has a definition of PhysReg in the instruction
// range [StopInst, StartMI) where StopInst is the last instance of instruction
// with the opcode property StopAtInstProp. For example, if StopAtInstProp is
// MCID::Call, this function returns the instruction that defined PhysReg in the
// range [LCI, StartInst) where LCI is the last call instruction in MBB.
//
// If StartMI is nullptr, the range searched in [StopInst, BlockEndInst].
const MachineInstr *X86MachineInstructionRaiser::getPhysRegDefiningInstInBlock(
    int PhysReg, const MachineInstr *StartMI, const MachineBasicBlock *MBB,
    unsigned StopAtInstProp, bool &HasStopInst) {
  // Walk backwards starting from the instruction before StartMI
  HasStopInst = false; // default value
  unsigned SuperReg = find64BitSuperReg(PhysReg);
  auto InstIter =
      (StartMI == nullptr) ? MBB->rend() : StartMI->getReverseIterator();
  for (const MachineInstr &MI : make_range(++InstIter, MBB->rend())) {
    // Stop after the instruction with the specified property in the block
    if (MI.hasProperty(StopAtInstProp)) {
      HasStopInst = true;
      break;
    }

    // If the instruction has a define
    if (MI.getNumDefs() > 0) {
      for (auto MO : MI.defs()) {
        // If the define operand is a register
        if (MO.isReg()) {
          unsigned MOReg = MO.getReg();
          if (Register::isPhysicalRegister(MOReg)) {
            if (SuperReg == find64BitSuperReg(MOReg))
              return &MI;
          }
        }
      }
    }
  }

  return nullptr;
}

// FPU Access functions
void X86MachineInstructionRaiser::FPURegisterStackPush(Value *val) {
  assert(val->getType()->isFloatingPointTy() &&
         "Attempt to push non-FP type value on FPU register stack");
  assert((FPUStack.TOP < FPUSTACK_SZ) && (FPUStack.TOP >= 0) &&
         "Incorrect initial FPU Register Stack top in push");

  int8_t PushIndex = (FPUSTACK_SZ + FPUStack.TOP - 1) % FPUSTACK_SZ;

  assert((PushIndex < FPUSTACK_SZ) && (PushIndex >= 0) &&
         "Incorrect FPU Register Stack index computed in push");
  FPUStack.Regs[PushIndex] = val;
  FPUStack.TOP = PushIndex;
}

void X86MachineInstructionRaiser::FPURegisterStackPop() {
  assert((FPUStack.TOP < FPUSTACK_SZ) && (FPUStack.TOP >= 0) &&
         "Incorrect initial FPU Register Stack top in pop");

  int8_t PostPopIndex = (FPUSTACK_SZ + FPUStack.TOP + 1) % FPUSTACK_SZ;

  assert((PostPopIndex < FPUSTACK_SZ) && (PostPopIndex >= 0) &&
         "Incorrect FPU Register Stack index computed in pop");
  // Clear the value at current TOP
  FPUStack.Regs[FPUStack.TOP] = nullptr;
  // Adjust TOP value
  FPUStack.TOP = PostPopIndex;
}

// Get value at index
Value *X86MachineInstructionRaiser::FPURegisterStackGetValueAt(int8_t index) {
  assert((FPUStack.TOP < FPUSTACK_SZ) && (FPUStack.TOP >= 0) &&
         "Incorrect initial FPU Register Stack top in FPU register access");

  int8_t AccessIndex = (FPUSTACK_SZ + FPUStack.TOP + index) % FPUSTACK_SZ;

  assert((AccessIndex < FPUSTACK_SZ) && (AccessIndex >= 0) &&
         "Incorrect FPU Register Stack index computed in FPU register access");

  return FPUStack.Regs[AccessIndex];
}

// Set value at index to val
void X86MachineInstructionRaiser::FPURegisterStackSetValueAt(int8_t index,
                                                             Value *val) {
  assert(val->getType()->isFloatingPointTy() &&
         "Attempt to insert non-FP type value in FPU register stack");
  assert((FPUStack.TOP < FPUSTACK_SZ) && (FPUStack.TOP >= 0) &&
         "Incorrect initial FPU Register Stack top in FPU register access");

  int8_t AccessIndex = (FPUSTACK_SZ + FPUStack.TOP + index) % FPUSTACK_SZ;

  assert((AccessIndex < FPUSTACK_SZ) && (AccessIndex >= 0) &&
         "Incorrect FPU Register Stack index computed in FPU register access");

  FPUStack.Regs[AccessIndex] = val;
}

Value *X86MachineInstructionRaiser::FPURegisterStackTop() {
  return FPURegisterStackGetValueAt(0);
}

unsigned int
X86MachineInstructionRaiser::find64BitSuperReg(unsigned int PhysReg) {

  // No super register for 0 register
  if (PhysReg == X86::NoRegister) {
    return X86::NoRegister;
  }

  // Nothing to do if PhysReg is one of EFLAG bits, FPSW, FPCW
  if (isEflagBit(PhysReg))
    return PhysReg;

  if ((PhysReg == X86::FPSW) || (PhysReg == X86::FPCW)) {
    return PhysReg;
  }

  // Nothing to do if PhysReg is a 64-bit register.
  if (is64BitPhysReg(PhysReg)) {
    return PhysReg;
  }

  // Return PhysReg if it is an xmm register
  if (is64BitSSE2Reg(PhysReg))
    return PhysReg;

  // The return value.
  unsigned int SuperReg;

  // Did we find it.
  bool SuperRegFound = false;

  for (MCSuperRegIterator SuperRegsIter(PhysReg, x86RegisterInfo);
       SuperRegsIter.isValid(); ++SuperRegsIter) {
    SuperReg = *SuperRegsIter;
    if (is64BitPhysReg(SuperReg)) {
      assert(SuperRegFound != true && "Expect only one 64-bit super register");
      SuperRegFound = true;
    }
  }

  assert(SuperRegFound && "Unsupported register found");
  return SuperReg;
}

BasicBlock *
X86MachineInstructionRaiser::getRaisedBasicBlock(const MachineBasicBlock *MBB) {
  // Get the BasicBlock corresponding to MachineBasicBlock MBB
  auto MapIter = mbbToBBMap.find(MBB->getNumber());
  assert(MapIter != mbbToBBMap.end() &&
         "Failed to find BasicBlock corresponding to MachineBasicBlock");
  BasicBlock *RaisedBB = MapIter->second;
  assert((RaisedBB != nullptr) &&
         "Encountered null BasicBlock corresponding to MachineBasicBlock");
  return RaisedBB;
}

// Construct and return a Value* corresponding to PC-relative memory address
// access. Insert any intermediate values created in the process into
// curBlock.
Value *X86MachineInstructionRaiser::createPCRelativeAccesssValue(
    const MachineInstr &MI) {
  Value *MemrefValue = nullptr;
  // Get index of memory reference in the instruction.
  int MemoryRefOpIndex = getMemoryRefOpIndex(MI);
  // Should have found the index of the memory reference operand
  assert(MemoryRefOpIndex != -1 &&
         "Unable to find memory reference operand of a load/store instruction");
  X86AddressMode MemRef = llvm::getAddressFromInstr(&MI, MemoryRefOpIndex);

  // LLVM represents memory operands using 5 operands
  //    viz., <opcode> BaseReg, ScaleAmt, IndexReg, Disp, Segment, ...
  // The disassembly in AT&T syntax is shown as
  //      Segment:Disp(BaseReg, IndexReg, ScaleAmt).
  // or as
  //      Segment:[BaseReg + Disp + IndexReg * ScaleAmt]
  // in Intel syntax.
  // effective address is calculated to be Segment:[BaseReg + IndexReg *
  // ScaleAmt + Disp] Segment is typically X86::NoRegister.

  assert(MI.getOperand(MemoryRefOpIndex + X86::AddrSegmentReg).getReg() ==
             X86::NoRegister &&
         "Expect no segment register");

  // Construct non-stack memory referencing value
  unsigned BaseReg = MemRef.Base.Reg;
  unsigned IndexReg = MemRef.IndexReg;
  unsigned ScaleAmt = MemRef.Scale;
  int Disp = MemRef.Disp;
  const MachineOperand &SegRegOperand =
      MI.getOperand(MemoryRefOpIndex + X86::AddrSegmentReg);
  // For now, we assume default segment DS (and hence no specification of
  // Segment register.
  assert(SegRegOperand.isReg() && (SegRegOperand.getReg() == X86::NoRegister) &&
         "Unhandled memory reference instruction with non-zero segment "
         "register");
  // Also assume that PC-relative addressing does not involve index register
  assert(IndexReg == X86::NoRegister &&
         "Unhandled index register in PC-relative memory addressing "
         "instruction");
  assert(ScaleAmt == 1 && "Unhandled value of scale amount in PC-relative "
                          "memory addressing instruction");

  // Non-stack memory address is supported by this function.
  uint64_t BaseSupReg = find64BitSuperReg(BaseReg);
  assert(((BaseSupReg == X86::RIP) || (BaseSupReg == X86::NoRegister)) &&
         "Base register that is not PC encountered in memory access "
         "instruction");

  // 1. Get the text section address
  int64_t TextSectionAddress = MR->getTextSectionAddress();

  assert(TextSectionAddress >= 0 && "Failed to find text section address");

  // 2. Get MCInst offset - the offset of machine instruction in the binary
  // and instruction size
  MCInstRaiser *MCIRaiser = getMCInstRaiser();
  uint64_t MCInstOffset = MCIRaiser->getMCInstIndex(MI);
  uint64_t MCInstSz = MCIRaiser->getMCInstSize(MCInstOffset);

  // 3. Compute the PC-relative offset.

  const ELF64LEObjectFile *Elf64LEObjFile =
      dyn_cast<ELF64LEObjectFile>(MR->getObjectFile());
  assert(Elf64LEObjFile != nullptr &&
         "Only 64-bit ELF binaries supported at present.");

  auto EType = Elf64LEObjFile->getELFFile().getHeader().e_type;
  if ((EType == ELF::ET_DYN) || (EType == ELF::ET_EXEC)) {
    uint64_t PCOffset = TextSectionAddress + MCInstOffset + MCInstSz + Disp;
    const RelocationRef *DynReloc = MR->getDynRelocAtOffset(PCOffset);

    // If there is a dynamic relocation for the PCOffset
    if (DynReloc) {
      auto DynRelocType = DynReloc->getType();
      if ((DynRelocType == ELF::R_X86_64_COPY) ||
          (DynRelocType == ELF::R_X86_64_GLOB_DAT)) {
        Expected<StringRef> Symname = DynReloc->getSymbol()->getName();
        assert(Symname &&
               "Failed to find symbol associated with dynamic relocation.");
        // Find if a global value associated with symbol name is already
        // created
        for (GlobalVariable &GV : MR->getModule()->globals()) {
          if (GV.getName().compare(Symname.get()) == 0) {
            MemrefValue = &GV;
          }
        }
        if (MemrefValue == nullptr) {
          // Get all necessary information about the global symbol.
          llvm::LLVMContext &Ctx(MF.getFunction().getContext());
          DataRefImpl SymbImpl = DynReloc->getSymbol()->getRawDataRefImpl();
          // get symbol
          auto SymbOrErr = Elf64LEObjFile->getSymbol(SymbImpl);
          assert(SymbOrErr && "PC-relative access: Dynamic symbol not found");
          // get symbol size
          auto Symb = SymbOrErr.get();
          uint64_t SymbSize = Symb->st_size;
          GlobalValue::LinkageTypes Lnkg;
          switch (Symb->getBinding()) {
          case ELF::STB_GLOBAL:
            Lnkg = GlobalValue::ExternalLinkage;
            break;
          default:
            assert(false && "Unhandled dynamic symbol");
          }

          // Check that symbol type is data object, representing a variable or
          // array etc.
          assert((Symb->getType() == ELF::STT_OBJECT) &&
                 "Function symbol type expected. Not found");
          Type *GlobalValTy = nullptr;
          switch (SymbSize) {
          case 8:
            GlobalValTy = Type::getInt64Ty(Ctx);
            break;
          case 4:
            GlobalValTy = Type::getInt32Ty(Ctx);
            break;
          case 2:
            GlobalValTy = Type::getInt16Ty(Ctx);
            break;
          case 1:
            GlobalValTy = Type::getInt8Ty(Ctx);
            break;
          default:
            assert(false && "Unexpected symbol size");
          }
          // get symbol value - this is the virtual address of symbol's value
          uint64_t SymVirtualAddr = Symb->st_value;

          // get the initial value of the global data symbol at symVirtualAddr
          // from the section that contains the virtual address
          // symVirtualAddr. In executable and shared object files, st_value
          // holds a virtual address.
          uint64_t SymbVal = 0;
          for (section_iterator SecIter : Elf64LEObjFile->sections()) {
            uint64_t SecStart = SecIter->getAddress();
            uint64_t SecEnd = SecStart + SecIter->getSize();
            if ((SecStart <= SymVirtualAddr) && (SecEnd >= SymVirtualAddr)) {
              // Get the initial symbol value only if this is not a bss
              // section. Else, symVal is already initialized to 0.
              if (SecIter->isBSS()) {
                Lnkg = GlobalValue::CommonLinkage;
              } else {
                StringRef SecData = unwrapOrError(
                    SecIter->getContents(), MR->getObjectFile()->getFileName());
                unsigned Index = SymVirtualAddr - SecStart;
                const unsigned char *Begin = SecData.bytes_begin() + Index;
                char Shift = 0;
                while (SymbSize-- > 0) {
                  // We know this is little-endian
                  SymbVal = ((*Begin++) << Shift) | SymbVal;
                  Shift += 8;
                }
              }
              break;
            }
          }
          Constant *GlobalInit = (DynRelocType == ELF::R_X86_64_GLOB_DAT)
                                     ? ConstantInt::get(GlobalValTy, SymbVal)
                                     : nullptr;
          auto GlobalVal = new GlobalVariable(*(MR->getModule()), GlobalValTy,
                                              false /* isConstant */, Lnkg,
                                              GlobalInit, Symname->data());
          // Don't use symbSize as it was modified.
          GlobalVal->setAlignment(MaybeAlign(Symb->st_size));
          GlobalVal->setDSOLocal(true);
          MemrefValue = GlobalVal;
        }
      } else {
        assert(false && "Unexpected relocation type referenced in PC-relative "
                        "memory access instruction.");
      }
    } else {
      MemrefValue = getGlobalVariableValueAt(MI, PCOffset);
    }
  } else if (EType == ELF::ET_REL) {
    const RelocationRef *TextReloc =
        MR->getTextRelocAtOffset(MCInstOffset, MCInstSz);

    assert(TextReloc &&
           "Failed to get dynamic relocation for pc-relative offset");

    if (TextReloc->getType() == ELF::R_X86_64_32S) {
      Expected<StringRef> Symname = TextReloc->getSymbol()->getName();
      assert(Symname &&
             "Failed to find symbol associated with text relocation.");
      // Find if a global value associated with symbol name is already
      // created
      for (GlobalVariable &GV : MR->getModule()->globals()) {
        if (GV.getName().compare(Symname.get()) == 0) {
          MemrefValue = &GV;
        }
      }
      if (MemrefValue == nullptr) {
        // Get all necessary information about the text relocation symbol
        // which is most likely global.

        llvm::LLVMContext &Ctx(MF.getFunction().getContext());
        DataRefImpl symbImpl = TextReloc->getSymbol()->getRawDataRefImpl();
        // get symbol
        auto SymbOrErr = Elf64LEObjFile->getSymbol(symbImpl);
        assert(SymbOrErr && "PC-relative access: Relocation symbol not found");
        // get symbol size
        auto Symb = SymbOrErr.get();
        uint64_t SymSize = Symb->st_size;
        GlobalValue::LinkageTypes Lnkg;
        switch (Symb->getBinding()) {
        case ELF::STB_GLOBAL:
          Lnkg = GlobalValue::ExternalLinkage;
          break;
        default:
          assert(false && "Unhandled dynamic symbol");
        }

        // get symbol value - this is the offset from the beginning of the
        // section st_shndex identifies.
        uint64_t SymVal = Symb->st_value;

        uint64_t SymValSecIndex = Symb->st_shndx;
        uint8_t SymAlignment = 0;
        uint64_t SymInitVal = 0;
        if (((SymValSecIndex >= ELF::SHN_LORESERVE) &&
             (SymValSecIndex <= ELF::SHN_HIRESERVE)) ||
            (SymValSecIndex == ELF::SHN_UNDEF)) {
          if (SymValSecIndex == ELF::SHN_COMMON) {
            // st_value holds symbol alignment constraints
            SymAlignment = SymVal;
            Lnkg = GlobalValue::CommonLinkage;
          }
        } else {
          // get the initial value of the global data symbol at offset symVal
          // in section with index symValSecIndex

          for (section_iterator SecIter : Elf64LEObjFile->sections()) {
            if (SecIter->getIndex() == SymValSecIndex) {
              StringRef SecData = unwrapOrError(
                  SecIter->getContents(), MR->getObjectFile()->getFileName());
              const unsigned char *Begin = SecData.bytes_begin() + SymVal;
              char Shift = 0;
              while (SymSize-- > 0) {
                // We know this is little-endian
                SymInitVal = ((*Begin++) << Shift) | SymInitVal;
                Shift += 8;
              }
              break;
            }
          }
          // REVISIT : Set symbol alignment to be the same as symbol size
          // NOTE : Do not use symSize since it has been modified in the while
          // loop above.
          SymAlignment = Symb->st_size;
        }
        Type *GlobalValTy = nullptr;

        switch (SymAlignment) {
        case 8:
          GlobalValTy = Type::getInt64Ty(Ctx);
          break;
        case 4:
          GlobalValTy = Type::getInt32Ty(Ctx);
          break;
        case 2:
          GlobalValTy = Type::getInt16Ty(Ctx);
          break;
        case 1:
          GlobalValTy = Type::getInt8Ty(Ctx);
          break;
        default:
          assert(false && "Unexpected symbol size");
        }

        Constant *GlobalInit = ConstantInt::get(GlobalValTy, SymInitVal);
        auto GlobalVal = new GlobalVariable(*(MR->getModule()), GlobalValTy,
                                            false /* isConstant */, Lnkg,
                                            GlobalInit, Symname->data());
        // Don't use symSize as it was modified.
        GlobalVal->setAlignment(MaybeAlign(SymAlignment));
        GlobalVal->setDSOLocal(true);
        MemrefValue = GlobalVal;
      }
    } else {
      assert(false && "Unexpected relocation type referenced in PC-relative "
                      "memory access instruction.");
    }
  } else {
    assert(false && "Unhandled binary type. Only object files and shared "
                    "libraries supported");
  }
  return MemrefValue;
}

// Promote the ReachingValue of PhysReg defined in DefiningMBB to specified
// stack slot Alloca.
StoreInst *X86MachineInstructionRaiser::promotePhysregToStackSlot(
    int PhysReg, Value *ReachingValue, int DefiningMBB, Instruction *Alloca) {
  StoreInst *StInst = nullptr;
  LLVMContext &Ctxt(MF.getFunction().getContext());

  assert((ReachingValue != nullptr) &&
         "Null incoming value of reaching definition found");
  assert(raisedValues->getInBlockRegOrArgDefVal(PhysReg, DefiningMBB).second ==
             ReachingValue &&
         "Inconsistent reaching defined value found");
  assert((ReachingValue->getType()->isIntOrPtrTy() ||
          ReachingValue->getType()->isFloatingPointTy()) &&
         "Unsupported: Stack promotion of non-integer / non-pointer value");
  // Prepare to store this value in stack location.
  // Get the size of defined physical register
  int DefinedPhysRegSzInBits =
      raisedValues->getInBlockPhysRegSize(PhysReg, DefiningMBB);
  assert(((DefinedPhysRegSzInBits == 64) || (DefinedPhysRegSzInBits == 32) ||
          (DefinedPhysRegSzInBits == 16) || (DefinedPhysRegSzInBits == 8) ||
          (DefinedPhysRegSzInBits == 1)) &&
         "Unexpected physical register size of reaching definition ");
  // This could simply be set to 64 because the stack slot allocated is
  // a 64-bit value.
  int StackLocSzInBits =
      Alloca->getType()->getPointerElementType()->getPrimitiveSizeInBits();
  Type *StackLocTy;
  if (ReachingValue->getType()->isIntOrPtrTy()) {
    // Cast the current value to int64 if needed
    StackLocTy = Type::getIntNTy(Ctxt, StackLocSzInBits);
  } else if (ReachingValue->getType()->isFloatingPointTy()) {
    switch (StackLocSzInBits) {
    case 64:
      StackLocTy = Type::getDoubleTy(Ctxt);
      break;
    case 32:
      StackLocTy = Type::getFloatTy(Ctxt);
      break;
    default:
      llvm_unreachable("Unhandled floating point type with unknown size");
    }
  } else {
    llvm_unreachable("Unhandled type");
  }
  BasicBlock *ReachingBB =
      getRaisedBasicBlock(MF.getBlockNumbered(DefiningMBB));
  // get terminating instruction. Add new instructions before
  // terminator instruction if one exists.
  Instruction *TermInst = ReachingBB->getTerminator();
  if (StackLocTy != ReachingValue->getType()) {
    CastInst *CInst = CastInst::Create(
        CastInst::getCastOpcode(ReachingValue, false, StackLocTy, false),
        ReachingValue, StackLocTy);
    if (TermInst == nullptr)
      ReachingBB->getInstList().push_back(CInst);
    else
      CInst->insertBefore(TermInst);
    ReachingValue = CInst;
  }
  if (StackLocTy != Alloca->getType()->getPointerElementType()) {
    CastInst *CInst = CastInst::Create(
        CastInst::getCastOpcode(Alloca, false, StackLocTy->getPointerTo(), false),
        Alloca, StackLocTy->getPointerTo());
    if (TermInst == nullptr)
      ReachingBB->getInstList().push_back(CInst);
    else
      CInst->insertBefore(TermInst);
    Alloca = CInst;
  }
  StInst = new StoreInst(ReachingValue, Alloca, false, Align());
  if (TermInst == nullptr)
    ReachingBB->getInstList().push_back(StInst);
  else
    StInst->insertBefore(TermInst);

  // Construct a list of instructions that use ReachingValue, if it is not a
  // Constant or an argument. This list holds instructions that use
  // ReachingValue that is neither a Constant nor an argument value and are in
  // a basic block other than DefiningMBB.
  SmallVector<Instruction *, 4> UsageInstList;

  // Nothing to do if ReachingValue is either a Constant or an argument value.
  if (isa<Constant>(ReachingValue) ||
      ReachingValue->getName().startswith("arg") ||
      isa<LoadInst>(ReachingValue))
    return StInst;

  // Construct instructions that use ReachingValue and are in a basic block
  // other than DefiningMBB.
  for (auto U : ReachingValue->users()) {
    if (auto I = dyn_cast<Instruction>(U)) {
      if (I->getParent() != ReachingBB)
        UsageInstList.push_back(I);
    }
  }

  // Replace all uses of ReachingValue with that loaded from stack location at
  // which ReachingValue is stored.
  for (auto I : UsageInstList) {
    LoadInst *LdFromStkSlot = new LoadInst(
        Alloca->getType()->getPointerElementType(), Alloca, "ld-stk-prom", I);
    I->replaceUsesOfWith(ReachingValue, LdFromStkSlot);
  }

  return StInst;
}

// Does Val represent a stack location? It does if it is either an AllocaInst or
// a cast of an AllocaInst or a computation of stack location.
static bool isStackLocation(Value *Val) {
  Value *V = Val;
  while (!isa<AllocaInst>(V)) {
    if (isa<CastInst>(V)) {
      CastInst *P = dyn_cast<CastInst>(V);
      V = P->getOperand(0);
    } else if (isa<BinaryOperator>(V)) {
      BinaryOperator *BinaryOp = dyn_cast<BinaryOperator>(V);
      int NumUseOps = BinaryOp->getNumOperands();
      assert((NumUseOps == 2) && "Unexpected operands of binary operands");
      for (int i = 0; i < NumUseOps; i++) {
        auto Op = BinaryOp->getOperand(i);
        if (isa<CastInst>(Op)) {
          CastInst *P = dyn_cast<CastInst>(Op);
          V = P->getOperand(0);
        } else if (isa<AllocaInst>(Op)) {
          V = Op;
        } else
          assert(isa<ConstantInt>(Op) &&
                 "Constant value expected in stack pointer computation");
      }
    }
  }
  return (isa<AllocaInst>(V));
}

// Promote any reaching definitions that remained unpromoted.
bool X86MachineInstructionRaiser::handleUnpromotedReachingDefs() {
  for (auto RDToFix : reachingDefsToPromote) {
    unsigned PReg = std::get<0>(RDToFix);
    unsigned int SuperReg = find64BitSuperReg(PReg);
    unsigned int DefiningMBBNo = std::get<1>(RDToFix);
    Value *Val = std::get<2>(RDToFix);
    assert(isStackLocation(Val) && "Found value that is not a stack location "
                                   "during reaching definition fixup");
    Instruction *StackLoc = dyn_cast<Instruction>(Val);
    Value *ReachingDef =
        raisedValues->getInBlockRegOrArgDefVal(PReg, DefiningMBBNo).second;
    assert((ReachingDef != nullptr) &&
           "Null reaching definition found during reaching definition fixup");
    StoreInst *StInst = promotePhysregToStackSlot(SuperReg, ReachingDef,
                                                  DefiningMBBNo, StackLoc);
    assert(StInst != nullptr && "Failed to promote register to memory");
  }
  return true;
}

// Create a single stack frame based on stack allocations of the Function.
// The single stack frame thus created is expected to preserve the frame layout
// of the source binary - as represented by the various stack allocations. This
// raiser tool makes no attempt to abstract aggregate data, thus requiring the
// layout of any aggregate data stored on the stack to be preserved.
// Additionally, Prolog/Epilog insertion attempts to reorder stack objects when
// the raised LLVM IR is compiled to native code resulting in potentially
// fracturing aggregate data. This function abstracts all stack objects into
// a single frame to ensures the stack layout in source binary is preserved and
// prevent aggregate data fractures on the stack.
bool X86MachineInstructionRaiser::createFunctionStackFrame() {
  // If there are stack objects allocated
  if (ShadowStackIndexedByOffset.size() > 1) {
    MachineFrameInfo &MFrameInfo = MF.getFrameInfo();
    const DataLayout &dataLayout = MR->getModule()->getDataLayout();
    unsigned allocaAddrSpace = dataLayout.getAllocaAddrSpace();

    std::map<int64_t, int>::iterator StackOffsetToIndexMapIter;
    LLVMContext &llvmContext(MF.getFunction().getContext());
    StackOffsetToIndexMapIter = ShadowStackIndexedByOffset.begin();
    // The first non-spill alloca in StackOffsetToIndexMapIter map record
    // represents the alloca corresponding to the top-of-stack offset. Get stack
    // top offset and index.
    int64_t StackTopOffset;
    int StackTopObjIndex;
    while (StackOffsetToIndexMapIter != ShadowStackIndexedByOffset.end()) {
      StackTopObjIndex = StackOffsetToIndexMapIter->second;
      // Stop search at the first non-spill stack object
      if (!MFrameInfo.isSpillSlotObjectIndex(StackTopObjIndex))
        break;
      // Go to next stack object
      StackOffsetToIndexMapIter++;
    }

    // If we reached the end of the shadow stack, there no allocas to
    // consolidate into a single frame.
    if (StackOffsetToIndexMapIter == ShadowStackIndexedByOffset.end())
      return true;

    StackTopOffset = StackOffsetToIndexMapIter->first;

    AllocaInst *TOSAlloca = const_cast<AllocaInst *>(
        MFrameInfo.getObjectAllocation(StackTopObjIndex));
    Type *TOSAllocaOrigType = TOSAlloca->getType();
    auto TOSSzInBytes =
        TOSAlloca->getAllocationSizeInBits(dataLayout).getValue() / 8;
    // Get stack bottom offset and index
    int64_t StackBottomOffset = ShadowStackIndexedByOffset.rbegin()->first;
    int StackBottomObjIndex = ShadowStackIndexedByOffset.rbegin()->second;
    const AllocaInst *BOSAlloca =
        MFrameInfo.getObjectAllocation(StackBottomObjIndex);
    auto BOSSzInBytes =
        BOSAlloca->getAllocationSizeInBits(dataLayout).getValue() / 8;
    // Get stack frame size. Note that stack grows down on x86-64. Need to
    // ensure that stack frame size includes the size of the bottom most
    // object as well.
    int StackFrameSize = StackBottomOffset - StackTopOffset + BOSSzInBytes;
    assert(StackFrameSize > 0 && "Unexpected stack frame size");
    Value *StackFreameSizeVal =
        ConstantInt::get(llvmContext, APInt(32, StackFrameSize));
    // Construct new alloca corresponding to TOS offset with size
    // StackFrameSize bytes and insert it before TOSAlloca (which will be
    // replaced later by the cast of this alloca).
    Type *ByteTy = Type::getInt8Ty(llvmContext);
    AllocaInst *StackFrameAlloca =
        new AllocaInst(ByteTy, allocaAddrSpace, StackFreameSizeVal, Align(),
                       "stktop_" + std::to_string(TOSSzInBytes), TOSAlloca);
    // Cast the StackFrameAlloca instruction to the type of TOSAlloca
    Instruction *CastStackFrameAlloca =
        CastInst::Create(CastInst::getCastOpcode(StackFrameAlloca, false,
                                                 TOSAllocaOrigType, false),
                         StackFrameAlloca, TOSAllocaOrigType);

    // Copy RODataIndex metadata
    raisedValues->setInstMetadataRODataIndex(TOSAlloca, StackFrameAlloca);
    raisedValues->setInstMetadataRODataIndex(TOSAlloca, CastStackFrameAlloca);

    // Update TOSAlloca entries to CastStackFrameAlloca in
    // reachingDefsToPromote. This map is used later while promoting
    // reaching defs that were not promoted.
    for (auto RDToFix : reachingDefsToPromote) {
      Value *Val = std::get<2>(RDToFix);
      if (AllocaInst *A = dyn_cast<AllocaInst>(Val)) {
        if (A == TOSAlloca) {
          unsigned PReg = std::get<0>(RDToFix);
          unsigned int MBBNo = std::get<1>(RDToFix);
          reachingDefsToPromote.erase(std::make_tuple(PReg, MBBNo, A));
          reachingDefsToPromote.insert(
              std::make_tuple(PReg, MBBNo, CastStackFrameAlloca));
        }
      }
    }

    // Finally, replace TOSAlloca with CastStackFrameAlloca
    ReplaceInstWithInst(dyn_cast<Instruction>(TOSAlloca), CastStackFrameAlloca);
    // Cast StackFrameAlloca as int and insert it before StackObjAlloca,
    // which will be replaced later
    Type *Int64Ty = Type::getInt64Ty(llvmContext);
    Instruction *StackFrameAllocaAddr = CastInst::Create(
        CastInst::getCastOpcode(StackFrameAlloca, false, Int64Ty, false),
        StackFrameAlloca, Int64Ty, "tos", CastStackFrameAlloca->getNextNode());

    // Copy RODataIndex metadata
    raisedValues->setInstMetadataRODataIndex(StackFrameAlloca,
                                             StackFrameAllocaAddr);

    // Convert all allocas to offsets from CastStackFrameAlloca
    // Go to next record in ShadowStackIndexedByOffset
    StackOffsetToIndexMapIter++;
    while (StackOffsetToIndexMapIter != ShadowStackIndexedByOffset.end()) {
      auto Entry = *StackOffsetToIndexMapIter;
      int64_t MCStackOffset = Entry.first;
      int StackIndex = Entry.second;
      // Skip spill allocas
      if (MFrameInfo.isSpillSlotObjectIndex(StackIndex))
        continue;

      AllocaInst *StackObjAlloca =
          const_cast<AllocaInst *>(MFrameInfo.getObjectAllocation(StackIndex));
      int IRStackOffset = (MCStackOffset < 0) ? (StackFrameSize + MCStackOffset)
                                              : MCStackOffset;
      assert(IRStackOffset >= 0 &&
             "Non-negative IR stack offset expected to be computed");

      // Add IRStackOffset instruction before StackObjAlloca
      Value *StackObjOffsetVal =
          ConstantInt::get(StackFrameAllocaAddr->getType(), IRStackOffset);

      Instruction *StackObjOffset = BinaryOperator::CreateAdd(
          StackFrameAllocaAddr, StackObjOffsetVal, "", StackObjAlloca);
      // Copy RODataIndex metadata
      raisedValues->setInstMetadataRODataIndex(StackObjAlloca, StackObjOffset);
      // Cast the value to the type of StackObjAlloca; do not insert it into
      // the block. It will be done when we replace StackObjAlloca.
      Type *DstTy = StackObjAlloca->getType();
      Instruction *CastStackObjAlloca = CastInst::Create(
          CastInst::getCastOpcode(StackObjOffset, false, DstTy, false),
          StackObjOffset, DstTy);

      // Copy RODataIndex metadata
      raisedValues->setInstMetadataRODataIndex(StackObjAlloca,
                                               CastStackObjAlloca);

      // Replace StackObjAlloca entries in reachingDefsToPromote
      for (auto RDToFix : reachingDefsToPromote) {
        Value *Val = std::get<2>(RDToFix);
        if (AllocaInst *A = dyn_cast<AllocaInst>(Val)) {
          if (A == StackObjAlloca) {
            unsigned PReg = std::get<0>(RDToFix);
            unsigned int MBBNo = std::get<1>(RDToFix);
            reachingDefsToPromote.erase(std::make_tuple(PReg, MBBNo, A));
            reachingDefsToPromote.insert(
                std::make_tuple(PReg, MBBNo, CastStackObjAlloca));
          }
        }
      }

      // Finally, replace StackObjAlloca with CastStackObjAlloca
      ReplaceInstWithInst(StackObjAlloca, CastStackObjAlloca);
      // Go to next entry
      StackOffsetToIndexMapIter++;
    }
  }
  return true;
}

Value *X86MachineInstructionRaiser::getStackAllocatedValue(
    const MachineInstr &MI, X86AddressMode &MemRef, bool IsStackPointerAdjust) {
  unsigned int stackFrameIndex;

  assert((MemRef.BaseType == X86AddressMode::RegBase) &&
         "Register type operand expected for stack allocated value lookup");
  unsigned PReg = find64BitSuperReg(MemRef.Base.Reg);
  assert(((PReg == X86::RSP) || (PReg == X86::RBP)) &&
         "Stack or base pointer expected for stack allocated value lookup");
  Value *CurSPVal = getRegOrArgValue(PReg, MI.getParent()->getNumber());
  Type *MemOpTy = nullptr;
  LLVMContext &llvmContext(MF.getFunction().getContext());
  const DataLayout &dataLayout = MR->getModule()->getDataLayout();
  unsigned allocaAddrSpace = dataLayout.getAllocaAddrSpace();
  unsigned stackObjectSize = getInstructionMemOpSize(MI.getOpcode());
  if (IsStackPointerAdjust && (stackObjectSize == 0)) {
    stackObjectSize = 8;
  }
  InstructionKind InstrKind = getInstructionKind(MI.getOpcode());
  bool SSE2MemOp = ((InstrKind == InstructionKind::SSE_MOV_FROM_MEM) ||
                    (InstrKind == InstructionKind::SSE_MOV_TO_MEM));
  switch (stackObjectSize) {
  case 8:
    MemOpTy = SSE2MemOp ? Type::getDoubleTy(llvmContext)
                        : Type::getInt64Ty(llvmContext);
    break;
  case 4:
    MemOpTy = SSE2MemOp ? Type::getFloatTy(llvmContext)
                        : Type::getInt32Ty(llvmContext);
    break;
  case 2: {
    assert(!SSE2MemOp && "Unexpected memory access sized SSE2 instruction");
    MemOpTy = Type::getInt16Ty(llvmContext);
  } break;
  case 1: {
    assert(!SSE2MemOp && "Unexpected memory access sized SSE2 instruction");
    MemOpTy = Type::getInt8Ty(llvmContext);
  } break;
  default:
    llvm_unreachable("Unexpected access size of memory ref instruction");
  }

  assert(stackObjectSize != 0 && MemOpTy != nullptr &&
         "Unknown type of operand in memory referencing instruction");
  BasicBlock *RaisedBB = getRaisedBasicBlock(MI.getParent());

  // If the memory reference offset is 0 i.e., not different from the current sp
  // reference and there is already a stack allocation, just return that value
  if ((MemRef.Disp == 0) && (CurSPVal != nullptr)) {
    if (Instruction *I = dyn_cast<Instruction>(CurSPVal)) {
      if (hasRODataAccess(I))
        // Refers to rodata; so has no sp allocation;
        return nullptr;
    }
    // Ensure the type of CurSPVal matches that of pointer to MemOpTy
    Type *MemOpPtrTy = MemOpTy->getPointerTo();
    if (CurSPVal->getType() != MemOpPtrTy) {
      CurSPVal = CastInst::Create(
          CastInst::getCastOpcode(CurSPVal, false, MemOpPtrTy, false), CurSPVal,
          MemOpPtrTy, "", RaisedBB);
    }
    return CurSPVal;
  }
  // At this point, the stack offset specified in the memory operand is
  // different from that of the alloca corresponding to sp or there is no
  // stack allocation corresponding to sp.
  // If there is no allocation corresponding to sp, set the offset of new
  // allocation to be that specified in memory operand.
  if (CurSPVal != nullptr) {
    // Unwrap a bitcast instruction to get to the base stack allocation value.
    while (isa<CastInst>(CurSPVal)) {
      CastInst *B = dyn_cast<CastInst>(CurSPVal);
      CurSPVal = B->getOperand(0);
    }

    // If the sp/bp do not reference a stack allocation, return nullptr
    if (!isa<AllocaInst>(CurSPVal)) {
      // Check if this is an instruction that loads from stack (i.e., alloc)
      LoadInst *LoadAllocInst = dyn_cast<LoadInst>(CurSPVal);
      if (LoadAllocInst) {
        if (hasRODataAccess(LoadAllocInst))
          // Refers to rodata; so has no sp allocation;
          return nullptr;
      } else {
        return nullptr;
      }
    }
  }
  int MIStackOffset = MemRef.Disp;
  // Look for alloc with offset MIStackOffset
  MachineFrameInfo &MFrameInfo = MF.getFrameInfo();
  // Find and return an already existing stack slot for stack offset
  // MIStackOffset.
  auto SSIter = ShadowStackIndexedByOffset.find(MIStackOffset);
  if (SSIter != ShadowStackIndexedByOffset.end())
    return const_cast<AllocaInst *>(
        MFrameInfo.getObjectAllocation(SSIter->second));

  // If this is a stack pinter adjustment, find the corresponding adjustment
  // slot and return it. There is no need for a new slot to be created.
  if (IsStackPointerAdjust) {
    auto SSIter = ShadowStackIndexedByOffset.find(-MIStackOffset);
    if (SSIter != ShadowStackIndexedByOffset.end())
      return const_cast<AllocaInst *>(
          MFrameInfo.getObjectAllocation(SSIter->second));
  }

  // Find if there exists a stack slot that includes the offset MIStackSlot

  for (auto StackSlot : ShadowStackIndexedByOffset) {
    int64_t StackSlotOffset = StackSlot.first;
    int StackSlotIndex = StackSlot.second;
    if ((StackSlotOffset < MIStackOffset) &&
        ((StackSlotOffset + MFrameInfo.getObjectSize(StackSlotIndex)) >
         MIStackOffset)) {
      AllocaInst *StackSlotAllocaInst = const_cast<AllocaInst *>(
          MFrameInfo.getObjectAllocation(StackSlotIndex));
      int Stride = MIStackOffset - StackSlotOffset;
      assert(Stride > 0 && "Unexpected stack slot stride");
      // Convert pointer to int with size of the source binary ISA pointer
      Type *PtrCastIntTy =
          Type::getIntNTy(llvmContext, dataLayout.getPointerSizeInBits());

      PtrToIntInst *AllocaAsInt =
          new PtrToIntInst(StackSlotAllocaInst, PtrCastIntTy, "", RaisedBB);
      Instruction *AddStride = BinaryOperator::CreateAdd(
          AllocaAsInt, ConstantInt::get(PtrCastIntTy, Stride), "", RaisedBB);
      return AddStride;
    }
  }
  // No stack object found with offset MIStackOffset. Create one.

  std::string RegName(x86RegisterInfo->getName(PReg));
  std::string BaseName =
      IsStackPointerAdjust ? RegName + "Adj_" : RegName + "_";
  std::string SPStr = (MIStackOffset < 0) ? BaseName + "N." : BaseName + "P.";
  auto ByteAlign = Align();
  // Create alloca instruction to allocate stack slot
  AllocaInst *alloca =
      new AllocaInst(MemOpTy, allocaAddrSpace, 0, ByteAlign,
                     SPStr + std::to_string(abs(MIStackOffset)));

  // Create a stack slot associated with the alloca instruction
  stackFrameIndex = MF.getFrameInfo().CreateStackObject(
      stackObjectSize, ByteAlign, false /* isSpillSlot */, alloca);

  // Set MIStackOffset as the offset for stack frame object created.
  MF.getFrameInfo().setObjectOffset(stackFrameIndex, MIStackOffset);

  // Add the alloca instruction to entry block
  insertAllocaInEntryBlock(alloca, MIStackOffset, stackFrameIndex);

  return alloca;
}

// Return the Function * referenced by the PLT entry at offset
Function *X86MachineInstructionRaiser::getTargetFunctionAtPLTOffset(
    const MachineInstr &mi, uint64_t pltEntOff) {
  Function *CalledFunc = nullptr;
  const ELF64LEObjectFile *Elf64LEObjFile =
      dyn_cast<ELF64LEObjectFile>(MR->getObjectFile());
  assert(Elf64LEObjFile != nullptr &&
         "Only 64-bit ELF binaries supported at present.");
  unsigned char ExecType = Elf64LEObjFile->getELFFile().getHeader().e_type;
  assert((ExecType == ELF::ET_DYN) || (ExecType == ELF::ET_EXEC));
  // Find the section that contains the offset. That must be the PLT section
  for (section_iterator SecIter : Elf64LEObjFile->sections()) {
    uint64_t SecStart = SecIter->getAddress();
    uint64_t SecEnd = SecStart + SecIter->getSize();
    if ((SecStart <= pltEntOff) && (SecEnd > pltEntOff)) {
      StringRef SecName;
      if (auto NameOrErr = SecIter->getName())
        SecName = *NameOrErr;
      else {
        consumeError(NameOrErr.takeError());
        assert(false && "Failed to get section name with PLT offset");
      }
      if (!SecName.startswith(".plt"))
        continue;
      StringRef SecData = unwrapOrError(SecIter->getContents(),
                                        MR->getObjectFile()->getFileName());
      ArrayRef<uint8_t> Bytes(reinterpret_cast<const uint8_t *>(SecData.data()),
                              SecData.size());
      // Disassemble the first instruction at the offset
      MCInst Inst;
      uint64_t jmpInstSz;
      uint64_t jmpInstOff = pltEntOff;
      bool Success = MR->getMCDisassembler()->getInstruction(
          Inst, jmpInstSz, Bytes.slice(jmpInstOff - SecStart), pltEntOff,
          nulls());
      assert(Success && "Failed to disassemble instruction in PLT");
      unsigned int Opcode = Inst.getOpcode();
      // If the first instruction of the PLT stub is ENDBR32/ENDBR64 - the
      // instructions used for Indirect Branch Tracking - get to the next
      // instruction that is expected to be the jump to target.
      if ((Opcode == X86::ENDBR32) || (Opcode == X86::ENDBR64)) {
        jmpInstOff += jmpInstSz;
        Success = MR->getMCDisassembler()->getInstruction(
            Inst, jmpInstSz, Bytes.slice(jmpInstOff - SecStart), jmpInstOff,
            nulls());
        assert(Success && "Failed to disassemble instruction in PLT");
        Opcode = Inst.getOpcode();
      }
      MCInstrDesc MCID = MR->getMCInstrInfo()->get(Opcode);
      if ((Opcode != X86::JMP64m) || (MCID.getNumOperands() != 5)) {
        assert(false && "Unexpected non-jump instruction or number of operands "
                        "of jmp instruction in PLT entry");
      }
      MCOperand Oprnd = Inst.getOperand(0);
      int64_t PCOffset = 0;

      // First operand should be PC
      if (Oprnd.isReg()) {
        if (Oprnd.getReg() != X86::RIP) {
          assert(false && "PC-relative jmp instruction expected in PLT entry");
        }
      } else {
        assert(false && "PC operand expected in jmp instruction of PLT entry");
      }

      Oprnd = Inst.getOperand(1);
      // Second operand should be 1
      if (Oprnd.isImm()) {
        if (Oprnd.getImm() != 1) {
          assert(false && "Unexpected immediate second operand in jmp "
                          "instruction of PLT entry");
        }
      } else {
        assert(false && "Unexpected non-immediate second operand in jmp "
                        "instruction of PLT entry");
      }

      Oprnd = Inst.getOperand(2);
      // Third operand should be X86::No_Register
      if (Oprnd.isReg()) {
        if (Oprnd.getReg() != X86::NoRegister) {
          assert(false && "Unexpected third operand - non-zero register in jmp "
                          "instruction of PLT entry");
        }
      } else {
        assert(false && "Unexpected third operand - non-register in jmp "
                        "instruction of PLT entry");
      }

      Oprnd = Inst.getOperand(3);
      // Fourth operand should be an immediate
      if (!Oprnd.isImm()) {
        assert(false && "Unexpected non-immediate fourth operand in jmp "
                        "instruction of PLT entry");
      }
      // Get the pc offset
      PCOffset = Oprnd.getImm();

      Oprnd = Inst.getOperand(4);
      // Fifth operand should be X86::No_Register
      if (Oprnd.isReg()) {
        if (Oprnd.getReg() != X86::NoRegister) {
          assert(false && "Unexpected fifth operand - non-zero register in jmp "
                          "instruction of PLT entry");
        }
      } else {
        assert(false && "Unexpected fifth operand - non-register in jmp "
                        "instruction of PLT entry");
      }

      // Get dynamic relocation in .got.plt section corresponding to the PLT
      // entry. The relocation offset is calculated by adding the following:
      //    a) offset of jmp instruction + size of the instruction
      //    (representing pc-related addressing) b) jmp target offset in the
      //    instruction
      uint64_t GotPltRelocOffset = jmpInstOff + jmpInstSz + PCOffset;
      const RelocationRef *GotPltReloc =
          MR->getDynRelocAtOffset(GotPltRelocOffset);
      assert(GotPltReloc != nullptr &&
             "Failed to get dynamic relocation for jmp target of PLT entry");

      assert((GotPltReloc->getType() == ELF::R_X86_64_JUMP_SLOT) &&
             "Unexpected relocation type for PLT jmp instruction");
      symbol_iterator CalledFuncSym = GotPltReloc->getSymbol();
      assert(CalledFuncSym != Elf64LEObjFile->symbol_end() &&
             "Failed to find relocation symbol for PLT entry");
      Expected<StringRef> CalledFuncSymName = CalledFuncSym->getName();
      assert(CalledFuncSymName &&
             "Failed to find symbol associated with dynamic "
             "relocation of PLT jmp target.");
      Expected<uint64_t> CalledFuncSymAddr = CalledFuncSym->getAddress();
      assert(CalledFuncSymAddr &&
             "Failed to get called function address of PLT entry");
      CalledFunc = MR->getRaisedFunctionAt(CalledFuncSymAddr.get());

      if (CalledFunc == nullptr) {
        // This is an undefined function symbol. Look through the list of
        // user provided function prototypes and construct a Function
        // accordingly.
        CalledFunc = ExternalFunctions::Create(*CalledFuncSymName,
                                               *const_cast<ModuleRaiser *>(MR));
        // Bail out if function prototype is not available
        if (!CalledFunc)
          exit(-1);
      }
      // Found the section we are looking for
      break;
    }
  }
  return CalledFunc;
}

// Return the element pointer to global rodata array corresponding at Offset.
// This returns a Value of type GetElementPtrConstantExpr. However, this type
// can not be used explicitly since it is private to Constants.cpp (See comment
// in llvm/lib/IR/ConstantsContext.h)
Value *X86MachineInstructionRaiser::getOrCreateGlobalRODataValueAtOffset(
    int64_t Offset, BasicBlock *InsertBB) {
  // A negative offset implies that this is not an offset into ro-data
  // section. Just return nullptr.
  if (Offset < 0) {
    return nullptr;
  }
  Value *RODataValue = nullptr;
  const ELF64LEObjectFile *Elf64LEObjFile =
      dyn_cast<ELF64LEObjectFile>(MR->getObjectFile());
  assert(Elf64LEObjFile != nullptr &&
         "Only 64-bit ELF binaries supported at present.");
  LLVMContext &llvmContext(MF.getFunction().getContext());
  // Check if this is an address in .rodata
  for (section_iterator SecIter : Elf64LEObjFile->sections()) {
    uint64_t SecStart = SecIter->getAddress();
    uint64_t SecEnd = SecStart + SecIter->getSize();
    // We know that Offset is a positive value. So, casting it is OK.
    if ((SecStart <= (uint64_t)Offset) && (SecEnd >= (uint64_t)Offset)) {
      if (SecIter->isData()) {
        // Get the associated global value if one exists
        uint64_t SecIndex = SecIter->getIndex();
        std::string RODataSecValueName;
        if (auto NameOrErr = SecIter->getName())
          // Drop the leading '.' from section name
          RODataSecValueName.append((*NameOrErr).substr(1).data());
        else {
          consumeError(NameOrErr.takeError());
          RODataSecValueName.append("AnonDataSec");
        }

        RODataSecValueName.append("_").append(std::to_string(SecIndex));
        Constant *RODataSecValue = MR->getModule()->getGlobalVariable(
            RODataSecValueName, true /* AllowInternal */);
        // If ROData Value representing the contents of this section was not
        // materialized yet, create one.
        if (RODataSecValue == nullptr) {
          // Create the global variable corresponding to the content of
          // .rodata
          StringRef SecData = unwrapOrError(SecIter->getContents(),
                                            MR->getObjectFile()->getFileName());
          unsigned DataSize = SecIter->getSize();
          auto DataStr = makeArrayRef(SecData.bytes_begin(), DataSize);
          Constant *StrConstant = ConstantDataArray::get(llvmContext, DataStr);
          auto GlobalStrConstVal = new GlobalVariable(
              *(MR->getModule()), StrConstant->getType(), true /* isConstant */,
              GlobalValue::PrivateLinkage, StrConstant, RODataSecValueName);
          GlobalStrConstVal->setAlignment(MaybeAlign(SecIter->getAlignment()));
          // Address is not significant
          GlobalStrConstVal->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);
          // Add metadata that indicates the section start
          getRaisedValues()->setGVMetadataRODataInfo(GlobalStrConstVal,
                                                     SecStart);
          RODataSecValue = GlobalStrConstVal;
        }
        unsigned DataOffset = (Offset - SecStart);
        // Construct index array for a GEP instruction that accesses
        // byte array
        Value *Zero32Value = ConstantInt::get(Type::getInt32Ty(llvmContext), 0);
        Value *DataOffsetIndex =
            ConstantInt::get(Type::getInt32Ty(llvmContext), DataOffset);
        Constant *GetElem = ConstantExpr::getInBoundsGetElementPtr(
            RODataSecValue->getType()->getPointerElementType(), RODataSecValue,
            {Zero32Value, DataOffsetIndex});
        RODataValue = GetElem;
      }
      break;
    }
  }
  return RODataValue;
}

// Return a value corresponding to global symbol at Offset referenced in
// MachineInst MI. This function returns a data variable or a function variable
// depending on the symbol at the Offset being STT_OBJECT or STT_FUNC.
Value *
X86MachineInstructionRaiser::getGlobalVariableValueAt(const MachineInstr &MI,
                                                      uint64_t Offset) {
  Value *GlobalVariableValue = nullptr;
  const ELF64LEObjectFile *Elf64LEObjFile =
      dyn_cast<ELF64LEObjectFile>(MR->getObjectFile());
  assert(Elf64LEObjFile != nullptr &&
         "Only 64-bit ELF binaries supported at present.");
  assert((Offset > 0) &&
         "Unhandled non-positive displacement global variable value");
  // Find symbol at Offset
  SymbolRef GlobalSymRef;
  bool GlobalSymFound = false;
  unsigned GlobalSymOffset = 0;
  uint8_t GlobalSymType = ELF::STT_NOTYPE;
  llvm::LLVMContext &Ctx(MF.getFunction().getContext());

  // Get the BasicBlock corresponding to MachineBasicBlock of MI.
  // Raised instruction is added to this BasicBlock.
  BasicBlock *RaisedBB = getRaisedBasicBlock(MI.getParent());

  for (auto Symbol : Elf64LEObjFile->symbols()) {
    auto SymNameOrErr = Symbol.getName();
    if (!SymNameOrErr) {
      // No need to report. Just consume it.
      consumeError(SymNameOrErr.takeError());
    } else {
      GlobalSymType = Symbol.getELFType();

      if ((GlobalSymType == ELF::STT_OBJECT) ||
          (GlobalSymType == ELF::STT_FUNC)) {
        auto SymAddr = Symbol.getAddress();
        auto SymSize = Symbol.getSize();

        if (!SymAddr)
          report_error(SymAddr.takeError(),
                       "Failed to lookup symbol for global address");
        uint64_t SymAddrVal = SymAddr.get();
        // We have established that Offset is not negative above. So, OK to
        // cast.
        // Check if the memory address Offset is in the range [SymAddrVal,
        // SymAddrVal+SymSize)
        if ((SymAddrVal <= (unsigned)Offset) &&
            ((SymAddrVal + SymSize) > (unsigned)Offset)) {
          GlobalSymRef = Symbol;
          GlobalSymOffset = Offset - SymAddrVal;
          GlobalSymFound = true;
          break;
        }
      }
    }
  }

  if (!GlobalSymFound) {
    // If Offset does not correspond to a global symbol, get the corresponding
    // rodata value.
    GlobalVariableValue =
        getOrCreateGlobalRODataValueAtOffset(Offset, RaisedBB);
  } else {
    // If Offset corresponds to a function symbol, get the called function
    // value.
    if (GlobalSymType == ELF::STT_FUNC) {
      GlobalVariableValue = MR->getRaisedFunctionAt(Offset);
    } else {
      // If Offset corresponds to a global symbol, materialize a global
      // variable.
      Expected<StringRef> GlobalDataSymName = GlobalSymRef.getName();
      if (!GlobalDataSymName)
        report_error(GlobalDataSymName.takeError(),
                     "Failed to find global symbol name.");
      // Find if a global value associated with symbol name is already
      // created
      StringRef GlobalDataSymNameIndexStrRef(GlobalDataSymName.get());
      for (GlobalVariable &GV : MR->getModule()->globals()) {
        if (GV.getName().compare(GlobalDataSymNameIndexStrRef) == 0) {
          GlobalVariableValue = &GV;
        }
      }
      // By default, the symbol alignment is the symbol section alignment.
      // Will be adjusted as needed based on the size of the symbol later.
      auto GlobalDataSymSection = GlobalSymRef.getSection();
      assert(GlobalDataSymSection && "No section for global symbol found");
      uint64_t GlobDataSymAlignment =
          GlobalDataSymSection.get()->getAlignment();
      // Make sure the alignment is a power of 2
      assert(((GlobDataSymAlignment & (GlobDataSymAlignment - 1)) == 0) &&
             "Section alignment not a power of 2");

      // Get memory access size
      unsigned MemAccessSizeInBytes = getInstructionMemOpSize(MI.getOpcode());

      // If MI is not a memory accessing instruction, determine the access size
      // by the size of destination register.
      if (MemAccessSizeInBytes == 0) {
        MachineOperand MO = MI.getOperand(0);
        assert(MI.getNumExplicitDefs() == 1 && MO.isReg() &&
               "Expect one explicit register def operand");
        MemAccessSizeInBytes =
            getPhysRegSizeInBits(MO.getReg()) / sizeof(uint64_t);
      }

      assert((MemAccessSizeInBytes != 0) && "Unknown memory access size");

      if (GlobalVariableValue == nullptr) {
        Type *GlobalValTy = nullptr;
        // Get all necessary information about the global symbol.
        DataRefImpl SymbImpl = GlobalSymRef.getRawDataRefImpl();
        // get symbol
        auto SymbOrErr = Elf64LEObjFile->getSymbol(SymbImpl);
        assert(SymbOrErr && "Global symbol not found");
        auto Symb = SymbOrErr.get();
        // get symbol size
        uint64_t SymbSize = Symb->st_size;
        // If symbol size is less than symbol section size, set alignment to
        // symbol size.
        if (SymbSize < GlobDataSymAlignment) {
          GlobDataSymAlignment = SymbSize;
        }
        GlobalValue::LinkageTypes Lnkg;
        switch (Symb->getBinding()) {
        case ELF::STB_GLOBAL:
          Lnkg = GlobalValue::ExternalLinkage;
          break;
        case ELF::STB_LOCAL:
          Lnkg = GlobalValue::InternalLinkage;
          break;
        default:
          assert(false && "Unhandled global symbol binding type");
        }

        // Check that symbol type is data object, representing a variable or
        // array etc.
        assert(((Symb->getType() == ELF::STT_OBJECT) ||
                (Symb->getType() == ELF::STT_FUNC)) &&
               "Object symbol type expected. Not found");

        // Memory access is in bytes. So, need to multiply the alignment by 8
        // for the number of bits.
        GlobalValTy = Type::getIntNTy(Ctx, MemAccessSizeInBytes * 8);

        // get symbol value - this is the virtual address of symbol's value
        uint64_t SymVirtualAddr = Symb->st_value;

        // get the initial value of the global data symbol at SymVirtualAddr
        // from the section that contains the virtual address SymVirtualAddr.
        // In executable and shared object files, st_value holds a virtual
        // address.
        SmallVector<Constant *, 32> ConstantVec;
        bool isBSSSymbol = false;
        for (section_iterator SecIter : Elf64LEObjFile->sections()) {
          uint64_t SecStart = SecIter->getAddress();
          uint64_t SecEnd = SecStart + SecIter->getSize();
          if ((SecStart <= SymVirtualAddr) && (SecEnd > SymVirtualAddr)) {
            // Get the initial symbol value only if this is not a bss section.
            // Else, symVal is already initialized to 0.
            if (SecIter->isBSS()) {
              Lnkg = GlobalValue::CommonLinkage;
              isBSSSymbol = true;
            } else {
              StringRef SecData = unwrapOrError(
                  SecIter->getContents(), MR->getObjectFile()->getFileName());
              unsigned Index = SymVirtualAddr - SecStart;
              const char *beg =
                  reinterpret_cast<const char *>(SecData.bytes_begin() + Index);

              // Symbol size should at least be the same as memory access size
              // of the instruction.
              assert(
                  MemAccessSizeInBytes <= SymbSize &&
                  "Inconsistent values of memory access size and symbol size");
              // Read MemAccesssSize number of bytes and check if they represent
              // addresses in .rodata.
              StringRef SymbolBytes(beg, SymbSize);
              unsigned BytesRead = 0;
              // Symbol represents addresses into .rodata section.
              bool SymHasRODataAddrs = false;
              // Symbol array values greater that 8 bytes are not yet supported.
              uint64_t SymArrayElem = 0;
              for (unsigned char B : SymbolBytes) {
                unsigned ByteNum = ++BytesRead % MemAccessSizeInBytes;
                if (ByteNum == 0) {
                  // Finish reading one symbol data item of size.
                  SymArrayElem |= B << (MemAccessSizeInBytes - 1) * 8;
                  // Get the value representing .rodata content if it is .rodata
                  // section address.
                  Value *RODataValue = getOrCreateGlobalRODataValueAtOffset(
                      SymArrayElem, RaisedBB);
                  // Note if the first unit of data read is an address of
                  // .rodata content.
                  if (BytesRead == MemAccessSizeInBytes)
                    SymHasRODataAddrs = (RODataValue != nullptr);
                  // If the SymArrElem does not correspond to an .rodata address
                  // consider it to be data.
                  if (!SymHasRODataAddrs) {
                    Constant *ConstVal = ConstantInt::get(
                        Ctx, APInt(MemAccessSizeInBytes * 8, SymArrayElem));
                    ConstantVec.push_back(ConstVal);
                  } else {
                    // SymArrElem corresponds to an .rodata address,
                    if (isa<ConstantExpr>(RODataValue)) {
                      ConstantVec.push_back(dyn_cast<Constant>(RODataValue));
                    } else {
                      assert(false && "Unhandled global value");
                    }
                  }
                  // Clear symbol element value
                  SymArrayElem = 0;
                } else
                  SymArrayElem |= B << (ByteNum - 1) * 8;
              }
              // Ensure that all SymSize bytes were read.
              assert(BytesRead == SymbSize &&
                     "Incorrect number of symbol bytes read");
            }
            break;
          }
        }

        // Check for consistency of the types of symbol data.
        if (ConstantVec.size()) {
          auto Ty = ConstantVec[0]->getType();
          for (auto V : ConstantVec) {
            assert((V->getType() == Ty) &&
                   "Inconsistent types in constant array of global variable.");
          }
        }

        // If symbol size is greater than memory access size of the instruction,
        // the symbol must be referencing an array whose elements were collected
        Constant *GlobalInit = nullptr;
        if (SymbSize > MemAccessSizeInBytes) {
          if (ConstantVec.size()) {
            Constant *ConstArray = ConstantArray::get(
                ArrayType::get(ConstantVec[0]->getType(), ConstantVec.size()),
                ConstantVec);
            GlobalInit = ConstArray;
            GlobalValTy = ConstArray->getType();
            if (ConstantVec[0]->getType()->isIntegerTy()) {
              GlobDataSymAlignment = 4;
            }
          } else {
            // This is an aggregate array whose size is symbSize bytes,
            // initialized by BSS.
            assert(isBSSSymbol && "Unexpected non-BSS symbol encountered");
            Type *ByteType = Type::getInt8Ty(Ctx);
            Type *GlobalArrValTy = ArrayType::get(ByteType, SymbSize);
            GlobalInit = ConstantAggregateZero::get(GlobalArrValTy);

            // Change the global value type to byte type to indicate that the
            // data is interpreted as bytes.
            GlobalValTy = GlobalArrValTy;
          }
        } else {
          // Default initial value of global variable
          uint64_t SV = 0;
          assert(SymbSize == MemAccessSizeInBytes &&
                 "Inconsistent symbol sizes");

          if (ConstantVec.size() > 0) {
            // Get type of data value
            Type *CVType = ConstantVec[0]->getType();
            if (CVType->isIntegerTy()) {
              assert(ConstantVec.size() == 1 &&
                     "Inconsistent symbol values of global symbol found");
              // Global value is an integer. So, cast the global value that was
              // read accordingly.
              ConstantInt *CIV = dyn_cast<ConstantInt>(ConstantVec[0]);
              assert(CIV != nullptr && "Unexpected global value type");
              // Set the type of global value according to the based on the type
              // of the cast value.
              SV = CIV->getValue().getSExtValue();
              GlobalInit = ConstantInt::get(GlobalValTy, SV);
            } else if (CVType->isPointerTy()) {
              // ConstantVec[0] is the initial global value and global value
              // type is its type.
              GlobalInit = ConstantVec[0];
              GlobalValTy = CVType;
            } else {
              assert(false && "Unexpected global value type");
            }
          } else
            GlobalInit = ConstantInt::get(GlobalValTy, SV);
        }

        // Now, create the global variable for the symbol at given Offset.
        auto GlobalVal = new GlobalVariable(
            *(MR->getModule()), GlobalValTy, false /* isConstant */, Lnkg,
            GlobalInit, GlobalDataSymNameIndexStrRef);
        GlobalVal->setAlignment(MaybeAlign(GlobDataSymAlignment));
        GlobalVal->setDSOLocal(true);
        GlobalVariableValue = GlobalVal;
      }
      assert(GlobalVariableValue->getType()->isPointerTy() &&
             "Unexpected non-pointer type value in global data offset access");

      // If the global variable is of array type, ensure its type is correct.
      if (GlobalVariableValue->getType()
              ->getPointerElementType()
              ->isArrayTy()) {
        // First index - is 0
        Value *FirstIndex =
            ConstantInt::get(MF.getFunction().getContext(), APInt(32, 0));
        // Find the size of array element
        size_t ArrayElemByteSz = GlobalVariableValue->getType()
                                     ->getPointerElementType()
                                     ->getArrayElementType()
                                     ->getScalarSizeInBits() /
                                 8;

        unsigned ScaledOffset = GlobalSymOffset / MemAccessSizeInBytes;

        // Offset index
        Value *OffsetIndex = ConstantInt::get(MF.getFunction().getContext(),
                                              APInt(32, ScaledOffset));
        // If the array element size (in bytes) is not equal to that of the
        // access size of the instructions, cast the array accordingly.
        if (MemAccessSizeInBytes != ArrayElemByteSz) {
          // Note the scaled offset is already calculated appropriately.
          // Get the size of global array
          uint64_t GlobalArraySize = GlobalVariableValue->getType()
                                         ->getPointerElementType()
                                         ->getArrayNumElements();
          // Construct integer type of size memAccessSize bytes. Note that It
          // has been asserted that array element is of integral type.
          PointerType *CastToArrTy = PointerType::get(
              ArrayType::get(Type::getIntNTy(Ctx, MemAccessSizeInBytes * 8),
                             GlobalArraySize / MemAccessSizeInBytes),
              0);

          CastInst *CInst = CastInst::Create(
              CastInst::getCastOpcode(GlobalVariableValue, false, CastToArrTy,
                                      false),
              GlobalVariableValue, CastToArrTy);
          RaisedBB->getInstList().push_back(CInst);
          GlobalVariableValue = CInst;
        }
        // Get the element
        Instruction *GetElem = GetElementPtrInst::CreateInBounds(
            GlobalVariableValue->getType()->getPointerElementType(),
            GlobalVariableValue, {FirstIndex, OffsetIndex}, "", RaisedBB);
        GlobalVariableValue = GetElem;
      }
    }
  }

  return GlobalVariableValue;
}

// Construct and return a Value* corresponding to non-stack memory address
// expression in MachineInstr mi. Insert any intermediate values created in
// the process into curBlock. NOTE: This returns a value that may need to be
// loaded from if the expression does not involve global variable or
// dereferencing the global variable if expression involves global variable.
Value *
X86MachineInstructionRaiser::getMemoryAddressExprValue(const MachineInstr &MI) {
  Value *MemrefValue = nullptr;
  // Get index of memory reference in the instruction.
  int MemoryRefOpIndex = getMemoryRefOpIndex(MI);
  // Should have found the index of the memory reference operand
  assert(MemoryRefOpIndex != -1 && "Unable to find memory reference "
                                   "operand of a load/store instruction");
  X86AddressMode MemRef = llvm::getAddressFromInstr(&MI, MemoryRefOpIndex);

  // LLVM represents memory operands using 5 operands
  //    viz., <opcode> BaseReg, ScaleAmt, IndexReg, Disp, Segment, ...
  // The disassembly in AT&T syntax is shown as
  //      Segment:Disp(BaseReg, IndexReg, ScaleAmt).
  // or as
  //      Segment:[BaseReg + Disp + IndexReg * ScaleAmt]
  // in Intel syntax.
  // effective address is calculated to be Segment:[BaseReg + IndexReg *
  // ScaleAmt + Disp] Segment is typically X86::NoRegister.

  assert(MI.getOperand(MemoryRefOpIndex + X86::AddrSegmentReg).getReg() ==
             X86::NoRegister &&
         "Expect no segment register");
  // Get the BasicBlock corresponding to MachineBasicBlock of MI.
  // Raised instruction is added to this BasicBlock.
  BasicBlock *RaisedBB = getRaisedBasicBlock(MI.getParent());

  llvm::LLVMContext &Ctx(MF.getFunction().getContext());
  X86RaisedValueTracker *RVT = getRaisedValues();
  // Construct non-stack memory referencing value
  unsigned BaseReg = MemRef.Base.Reg;
  unsigned IndexReg = MemRef.IndexReg;
  unsigned ScaleAmt = MemRef.Scale;
  int Disp = MemRef.Disp;
  const MachineOperand &SegRegOperand =
      MI.getOperand(MemoryRefOpIndex + X86::AddrSegmentReg);
  // For now, we assume default segment DS (and hence no specification of
  // Segment register.
  assert(SegRegOperand.isReg() && (SegRegOperand.getReg() == X86::NoRegister) &&
         "Unhandled memory reference instruction with non-zero segment "
         "register");

  // IndexReg * ScaleAmt
  // Generate mul scaleAmt, IndexRegVal, if IndexReg is not 0.
  if (IndexReg != X86::NoRegister) {
    Value *IndexRegVal = getPhysRegValue(MI, IndexReg);
    if (IndexRegVal->getType()->isPointerTy()) {
      Type *LdTy = IndexRegVal->getType()->getPointerElementType();
      LoadInst *LdInst =
        new LoadInst(LdTy, IndexRegVal, "memload", false, Align());
      RaisedBB->getInstList().push_back(LdInst);
      IndexRegVal = LdInst;
    }
    switch (ScaleAmt) {
    case 0:
      assert(false && "Unexpected zero-value of scale in memory operand");
      break;
    case 1:
      MemrefValue = IndexRegVal;
      break;
    default: {
      Type *MulValTy = IndexRegVal->getType();
      Value *ScaleAmtValue = ConstantInt::get(MulValTy, ScaleAmt);
      Instruction *MulInst = BinaryOperator::CreateMul(
          ScaleAmtValue, IndexRegVal, "memref-idxreg");
      RaisedBB->getInstList().push_back(MulInst);
      MemrefValue = MulInst;
    } break;
    }
  }

  // BaseReg + IndexReg*ScaleAmt
  // Generate add BaseRegVal, memrefVal (if IndexReg*ScaleAmt was computed)

  if (BaseReg != X86::NoRegister) {
    Value *BaseRegVal = getRegOrArgValue(BaseReg, MI.getParent()->getNumber());
    if (MemrefValue != nullptr) {
      assert((BaseRegVal != nullptr) &&
             "Unexpected null value of base reg while constructing memory "
             "address expression");
      // Ensure the type of BaseRegVal matched that of MemrefValue.
      BaseRegVal = getRaisedValues()->castValue(
          BaseRegVal, MemrefValue->getType(), RaisedBB);
      Instruction *AddInst =
          BinaryOperator::CreateAdd(BaseRegVal, MemrefValue, "memref-basereg");
      // Propagate rodata related metadata
      RVT->setInstMetadataRODataIndex(BaseRegVal, AddInst);
      RaisedBB->getInstList().push_back(AddInst);
      MemrefValue = AddInst;
    } else {
      MemrefValue = BaseRegVal;
    }
  }

  // BaseReg + Index*ScaleAmt + Disp
  //
  if (Disp != 0) {
    if (MemrefValue != nullptr) {
      Type *DispTy = MemrefValue->getType();
      Value *DispValue = ConstantInt::get(DispTy, Disp);

      // Get a global symbol that represents the displacement, Disp.
      Value *GV = getGlobalVariableValueAt(MI, Disp);
      // If Disp represents a global symbol, generate correct instructions for
      // byte sized access, since displacement is always in terms of bytes. If
      // Disp does not represent a global symbol, consider Disp as a plain
      // integer value.
      if (GV != nullptr) {
        // If it is a global array construct GEP
        if (isa<GetElementPtrInst>(GV)) {
          bool Inbounds = false;
          if (auto *GlobGEP = dyn_cast<GetElementPtrInst>(GV)) {
            Inbounds = GlobGEP->isInBounds();
            if (Inbounds) {
              Type *GlobGEPSrcTy = GlobGEP->getSourceElementType();
              if (GlobGEPSrcTy->isArrayTy()) {
                // If it is not a byte-array
                Type *ByteTy = Type::getInt8Ty(Ctx);
                if (GlobGEPSrcTy->getArrayElementType() != ByteTy) {
                  // Create global byte array type based on the size of
                  // GlobalGEPSrc.
                  unsigned int GlobGEPSrcTySzInBytes =
                      GlobGEPSrcTy->getArrayElementType()
                          ->getScalarSizeInBits() /
                      8;
                  uint64_t SymbSize = GlobGEPSrcTy->getArrayNumElements() *
                                      GlobGEPSrcTySzInBytes;
                  Type *ByteArrValTy = ArrayType::get(ByteTy, SymbSize);

                  // Cast array operand of GlobalGEP to ByteArrTy
                  PointerType *ByteArrValPtrTy = ByteArrValTy->getPointerTo();
                  CastInst *CastToArrInst = CastInst::Create(
                      CastInst::getCastOpcode(GlobGEP->getPointerOperand(),
                                              false, ByteArrValPtrTy, false),
                      GlobGEP->getPointerOperand(), ByteArrValPtrTy);
                  // Propagate rodata related metadata
                  RVT->setInstMetadataRODataIndex(GV, CastToArrInst);
                  RaisedBB->getInstList().push_back(CastToArrInst);

                  // Construct index array for a GEP instruction that accesses
                  // byte array
                  std::vector<Value *> ByteAccessGEPIdxArr;
                  for (auto IdxIter = GlobGEP->idx_begin();
                       IdxIter != GlobGEP->idx_end(); IdxIter++) {
                    Value *IdxVal = IdxIter->get();
                    // Special case for index value of 0
                    if (isa<ConstantInt>(IdxVal)) {
                      ConstantInt *ConstIdxVal = dyn_cast<ConstantInt>(IdxVal);
                      if (ConstIdxVal->getSExtValue() == 0) {
                        ByteAccessGEPIdxArr.push_back(IdxVal);
                        continue;
                      }
                    }
                    // Index value not zero. So, scale it up by multiplying
                    // with GlobGEPSrcTySzInBytes, since the we are changing
                    // the access to byte array access.
                    Constant *ScaleVal = ConstantInt::get(IdxVal->getType(),
                                                          GlobGEPSrcTySzInBytes,
                                                          false /* isSigned */);
                    Instruction *IdxMulInst =
                        BinaryOperator::CreateNSWMul(ScaleVal, IdxVal);
                    // Insert the new instruction
                    RaisedBB->getInstList().push_back(IdxMulInst);
                    // Add the value to array used to construct new GEP
                    ByteAccessGEPIdxArr.push_back(IdxVal);
                  }
                  // Create new GEP.
                  Instruction *ByteAccessGEP =
                      GetElementPtrInst::CreateInBounds(
                          ByteArrValTy, CastToArrInst,
                          ArrayRef<Value *>(ByteAccessGEPIdxArr), "", RaisedBB);
                  DispValue = ByteAccessGEP;
                } else {
                  // Global GEP is already a byte array.
                  DispValue = GlobGEP;
                }
                assert(isa<Instruction>(DispValue) &&
                       "Expect Instruction - memory address expression "
                       "abstraction");
                // Cast the byte access GEP to MemrefValue type as needed using
                // dyn_cast<Instruction> to cast the result of castValue is
                // correct as we know that DispValue is an instruction;
                // castValue returns ByteAccessGEP (an Instruction) if no cast
                // is done or a value of type CastInst, if cast is done.
                DispValue = dyn_cast<Instruction>(getRaisedValues()->castValue(
                    DispValue, MemrefValue->getType(), RaisedBB));
              } else {
                assert(false && "Unhandled situation where global symbol GEP "
                                "is not an array");
              }
            } else {
              assert(false && "Unhandled situation where global symbol GEP is "
                              "not inbounds");
            }
          }
        } else if (GV->getType()->isPointerTy()) {
          // Global value is expected to be an pointer type to an integer
          // type. Cast GV in accordance with the type of MemrefValue to
          // facilitate the addition performed later to construct the address
          // expression.
          if (GV->getType()->getPointerElementType()->isIntegerTy()) {

            DispValue = getRaisedValues()->castValue(GV, MemrefValue->getType(),
                                                     RaisedBB);
          } else {
            assert(false && "Unhandled non-integer pointer global symbol type "
                            "while computing memory address expression");
          }
        } else {
          assert(false && "Unhandled global symbol type while computing "
                          "memory address expression");
        }
      }
      // Generate add memrefVal, Disp.
      Instruction *AddInst =
          BinaryOperator::CreateAdd(MemrefValue, DispValue, "memref-disp");
      getRaisedValues()->setInstMetadataRODataIndex(MemrefValue, AddInst);
      getRaisedValues()->setInstMetadataRODataIndex(DispValue, AddInst);
      RaisedBB->getInstList().push_back(AddInst);
      MemrefValue = AddInst;
    } else {
      // Check that this is an instruction of the kind
      // mov %rax, 0x605798 which in reality is
      // mov %rax, 0x605798(X86::NoRegister, X86::NoRegister, 1)
      if (BaseReg == X86::NoRegister) {
        assert(((IndexReg == X86::NoRegister) && (ScaleAmt == 1)) &&
               "Unhandled index register in memory addr expression "
               "calculation");
        MemrefValue = getGlobalVariableValueAt(MI, Disp);
        // Construct a PC-relative value if base register is RIP
      } else if (BaseReg == X86::RIP) {
        MemrefValue = createPCRelativeAccesssValue(MI);
      } else {
        assert(false && "Unhandled addressing mode in memory addr "
                        "expression calculation");
      }
    }
  }
  assert((MemrefValue != nullptr) && "Failed to get memory reference value");
  return MemrefValue;
}

// Find SSA value associated with physical register PReg.
// If the PReg is an argument register and hence does not have a previous
// definition, function prototype is consulted to return the corresponding
// value. In that case, return argument value associated with physical
// register PReg according to C calling convention. This function simply
// returns the value of PReg.

// NOTE : This is the preferred API to get the SSA value associated
//        with PReg. It does not make any attempt to cast it to match
//        the PReg type.
Value *X86MachineInstructionRaiser::getRegOrArgValue(unsigned PReg, int MBBNo) {
  Value *PRegValue = raisedValues->getReachingDef(PReg, MBBNo);

  // Just return the value associated with PReg, if one exists.
  if (PRegValue == nullptr) {
    int pos = getArgumentNumber(PReg);

    // If PReg is an argument register, get its value from function
    // argument list.
    if (pos > 0) {
      // Get the value only if the function has an argument at
      // pos.
      if (pos <= (int)raisedFunction->arg_size()) {
        bool isRegFloatingPointType = isSSE2Reg(PReg);
        int actualPos = 0; // SSE regs and int regs are scrambled
        int i = 0;

        while (actualPos < (int)raisedFunction->arg_size() && i < pos) {
          bool isArgFloatingPointType =
              raisedFunction->getArg(i)->getType()->isFloatingPointTy();

          if (isArgFloatingPointType == isRegFloatingPointType) {
            i++;
          }
          actualPos++;
        }

        Function::arg_iterator argIter =
            raisedFunction->arg_begin() + actualPos - 1;
        PRegValue = argIter;
      }
    }
  }
  return PRegValue;
}
// Find SSA value associated with operand at OpIndex, if it is a physical
// register. This function calls getRegOrArgValue() and generates a cast
// instruction to match the type of operand register.

Value *X86MachineInstructionRaiser::getRegOperandValue(const MachineInstr &MI,
                                                       unsigned OpIndex) {
  const MachineOperand &MO = MI.getOperand(OpIndex);
  Value *PRegValue = nullptr; // Unknown, to start with.
  assert(MO.isReg() && "Register operand expected");
  PRegValue = getRegOrArgValue(MO.getReg(), MI.getParent()->getNumber());

  if (PRegValue != nullptr) {
    // Cast the value in accordance with the register size of the operand,
    // as needed.
    Type *PRegTy = getPhysRegOperandType(MI, OpIndex);
    // Get the BasicBlock corresponding to MachineBasicBlock of MI.
    BasicBlock *RaisedBB = getRaisedBasicBlock(MI.getParent());
    PRegValue = getRaisedValues()->castValue(PRegValue, PRegTy, RaisedBB);
  }
  return PRegValue;
}

// Check the sizes of the operand register PReg and that of the
// corresponding SSA value. Return an appropriately cast value to match with
// the size of PReg. This is handles the situation following pattern of
// instructions
//   rax <- ...
//   edx <- opcode eax, ...
Value *X86MachineInstructionRaiser::getPhysRegValue(const MachineInstr &MI,
                                                    unsigned PReg) {
  assert(Register::isPhysicalRegister(PReg) &&
         "Expect physical register to get SSA value");
  unsigned SrcOpSize = getPhysRegSizeInBits(PReg);
  Value *SrcOpValue = getRegOrArgValue(PReg, MI.getParent()->getNumber());
  const DataLayout &dataLayout = MR->getModule()->getDataLayout();

  if (SrcOpValue) {
    // Generate the appropriate cast instruction if the sizes of the current
    // source value and that of the source register do not match.
    uint64_t SrcValueSize = dataLayout.getTypeSizeInBits(SrcOpValue->getType());
    if (SrcOpSize != SrcValueSize) {
      // Get the BasicBlock corresponding to MachineBasicBlock of MI.
      BasicBlock *RaisedBB = getRaisedBasicBlock(MI.getParent());
      Type *CastTy = Type::getIntNTy(MF.getFunction().getContext(), SrcOpSize);
      CastInst *CInst = CastInst::Create(
          CastInst::getCastOpcode(SrcOpValue, false, CastTy, false), SrcOpValue,
          CastTy);
      RaisedBB->getInstList().push_back(CInst);
      SrcOpValue = CInst;
    }
  } else {
    dbgs() << "***** Uninitialized register usage found\n";
    dbgs() << "*****" << MR->getModule()->getSourceFileName() << ": "
           << MF.getName().data() << "\n\t";
    MI.print(dbgs());
  }
  return SrcOpValue;
}

// Find the index of the first memory reference operand.
int X86MachineInstructionRaiser::getMemoryRefOpIndex(const MachineInstr &mi) {
  const MCInstrDesc &Desc = mi.getDesc();
  int memOperandNo = X86II::getMemoryOperandNo(Desc.TSFlags);
  if (memOperandNo >= 0)
    memOperandNo += X86II::getOperandBias(Desc);
  return memOperandNo;
}

// Insert a newly created alloca instruction representing stack location at
// offset StackOffset and with MachineFrame index MFIndex. It is assumed that
// MachineFrameInfo of Machine function already has the stack slot created for
// offset StackOffset at MFIndex
bool X86MachineInstructionRaiser::insertAllocaInEntryBlock(Instruction *alloca,
                                                           int StackOffset,
                                                           int MFIndex) {
  // Avoid using BasicBlock InstrList iterators so that the tool can use LLVM
  // built with LLVM_ABI_BREAKING_CHECKS ON or OFF.
  BasicBlock &EntryBlock = getRaisedFunction()->getEntryBlock();
  BasicBlock::InstListType &InstList = EntryBlock.getInstList();
  // Ensure that stack slot corresponding to StackOffset is not in shadow
  // stack i.e., not generated.
  assert((ShadowStackIndexedByOffset.find(StackOffset) ==
          ShadowStackIndexedByOffset.end()) &&
         "Alloca at stack slot already exists");

  // Record alloca in ShadowStack
  auto InserResult = ShadowStackIndexedByOffset.emplace(
      std::pair<int64_t, unsigned>(StackOffset, MFIndex));
  // The order of alloca instructions should match the order of shadow stack -
  // i.e., in descending order of stack offset. So, we utilize the fact that the
  // map is ordered by stack offset value and leverage the insertion point
  // returned by emplace.
  assert(InserResult.second && "Shadow stack insertion failed");
  auto InsertAtIter = InserResult.first;
  // If this insertion point is at the beginning of the map, insert the alloca
  // instruction at the beginning of the block.
  if (InsertAtIter == ShadowStackIndexedByOffset.begin()) {
    InstList.push_front(alloca);
  } else {
    // Insert alloca after the alloca instruction corresponding to the prior
    // stack slot.
    MachineFrameInfo &MFInfo = MF.getFrameInfo();
    InsertAtIter--;
    AllocaInst *Inst = const_cast<AllocaInst *>(
        MFInfo.getObjectAllocation(InsertAtIter->second));
    InstList.insertAfter(Inst->getIterator(), alloca);
  }

  return true;
}

// Record information to raise a terminator instruction in a later pass.
bool X86MachineInstructionRaiser::recordMachineInstrInfo(
    const MachineInstr &MI) {
  // Return instruction is a Terminator. There is nothing to record.
  // Its raising is handled as a normal instruction. This function should
  // not be called when mi is a call instruction.
  assert(MI.isTerminator() && "Not a terminator instruction - can not record "
                              "control transfer information");
  assert(!MI.isReturn() &&
         "Unexpected attempt to record info for a return instruction");

  // Get the BasicBlock corresponding to MachineBasicBlock of MI.
  // Raised instruction is added to this BasicBlock.
  BasicBlock *RaisedBB = getRaisedBasicBlock(MI.getParent());

  // Check if this is jmp instruction that is in reality a tail call.
  bool TailCall = false;
  if (MI.isBranch()) {
    const MCInstrDesc &MCID = MI.getDesc();

    if ((MI.getNumOperands() > 0) && MI.getOperand(0).isImm()) {
      // Only if this is a direct branch instruction with an immediate
      // offset
      if (X86II::isImmPCRel(MCID.TSFlags)) {
        // Get branch offset of the branch instruction
        const MachineOperand &MO = MI.getOperand(0);
        assert(MO.isImm() && "Expected immediate operand not found");
        int64_t BranchOffset = MO.getImm();
        MCInstRaiser *MCIR = getMCInstRaiser();
        // Get MCInst offset - the offset of machine instruction in the
        // binary
        uint64_t MCInstOffset = MCIR->getMCInstIndex(MI);

        assert(MCIR != nullptr && "MCInstRaiser not initialized");
        int64_t BranchTargetOffset =
            MCInstOffset + MCIR->getMCInstSize(MCInstOffset) + BranchOffset;
        const int64_t TgtMBBNo =
            MCIR->getMBBNumberOfMCInstOffset(BranchTargetOffset, MF);

        // If the target is not a known target basic block, attempt to raise
        // this instruction as a call.
        if (TgtMBBNo == -1) {
          TailCall = raiseCallMachineInstr(MI);
        }
      }
    }
  }
  // If the instruction is not a tail-call record instruction info for
  // processing at a later stage.
  if (!TailCall) {
    // Set common info of the record
    ControlTransferInfo *CurCTInfo = new ControlTransferInfo;
    CurCTInfo->CandidateMachineInstr = &MI;
    CurCTInfo->CandidateBlock = RaisedBB;

    const MCInstrDesc &MCID = MI.getDesc();
    // Save all values of implicitly used operands
    unsigned ImplUsesCount = MCID.getNumImplicitUses();
    if (ImplUsesCount > 0) {
      const MCPhysReg *ImplUses = MCID.getImplicitUses();
      for (unsigned i = 0; i < ImplUsesCount; i++) {
        // Get the reaching definition of the implicit use register.
        if (ImplUses[i] == X86::EFLAGS) {
          for (auto FlgBit : EFlagBits) {
            Value *Val = getRegOrArgValue(FlgBit, MI.getParent()->getNumber());
            assert((Val != nullptr) &&
                   "Unexpected null value of implicit eflags bits");
            CurCTInfo->RegValues.push_back(Val);
          }
        } else {
          Value *Val =
              getRegOrArgValue(ImplUses[i], MI.getParent()->getNumber());
          assert((Val != nullptr) &&
                 "Unexpected null value of implicit defined registers");
          CurCTInfo->RegValues.push_back(Val);
        }
      }
    }
    CurCTInfo->Raised = false;
    CTInfo.push_back(CurCTInfo);
  }
  return true;
}

bool X86MachineInstructionRaiser::instrNameStartsWith(const MachineInstr &MI,
                                                      StringRef name) const {
  return x86InstrInfo->getName(MI.getOpcode()).startswith(name);
}

Value *X86MachineInstructionRaiser::resizeFPValue(const MachineInstr &MI,
                                                    Value *Val, uint8_t Bits) {
  BasicBlock *RaisedBB = getRaisedBasicBlock(MI.getParent());
  LLVMContext &Ctx(MF.getFunction().getContext());
  assert(Val->getType()->isFloatingPointTy() && "Expected floating point type");

  Type *DstType;
  switch (Bits) {
  case 32:
    DstType = Type::getFloatTy(Ctx);
    break;
  case 64:
    DstType = Type::getDoubleTy(Ctx);
    break;
  default:
    llvm_unreachable("Unhandled bit precision");
  }

  Instruction *BitCastToFP =
      CastInst::CreateFPCast(Val, DstType, "cast", RaisedBB);

  return BitCastToFP;
}

#undef DEBUG_TYPE
