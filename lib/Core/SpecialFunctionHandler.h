//===-- SpecialFunctionHandler.h --------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_SPECIALFUNCTIONHANDLER_H
#define KLEE_SPECIALFUNCTIONHANDLER_H

#include "klee/Config/config.h"

#include <cstdint>
#include <map>
#include <vector>
#include <string>

namespace llvm {
  class Function;
}

namespace klee {
  class Executor;
  class Expr;
  class ExecutionState;
  struct KInstruction;
  template<typename T> class ref;
  
  class SpecialFunctionHandler {
  public:
    typedef void (SpecialFunctionHandler::*Handler)(ExecutionState &state,
                                                    KInstruction *target, 
                                                    std::vector<ref<Expr> > 
                                                      &arguments);
    typedef std::map<const llvm::Function*,
                     std::pair<Handler,bool> > handlers_ty;

    handlers_ty handlers;
    class Executor &executor;

    struct HandlerInfo {
      const char *name;
      SpecialFunctionHandler::Handler handler;
      bool doesNotReturn; /// Intrinsic terminates the process
      bool hasReturnValue; /// Intrinsic has a return value
      bool doNotOverride; /// Intrinsic should not be used if already defined
    };

  public:
    SpecialFunctionHandler(Executor &_executor);

    /// Perform any modifications on the LLVM module before it is
    /// prepared for execution. At the moment this involves deleting
    /// unused function bodies and marking intrinsics with appropriate
    /// flags for use in optimizations.
    ///
    /// @param preservedFunctions contains all the function names which should
    /// be preserved during optimization
    void prepare(std::vector<const char *> &preservedFunctions);

    /// Initialize the internal handler map after the module has been
    /// prepared for execution.
    void bind();

    bool handle(ExecutionState &state, 
                llvm::Function *f,
                KInstruction *target,
                std::vector< ref<Expr> > &arguments);

    /* Convenience routines */

    std::string readStringAtAddress(ExecutionState &state, ref<Expr> address);
    bool getConcreteConcurrencyLocation(ExecutionState &state,
                                        ref<Expr> argument, const char *name,
                                        std::uint64_t &object,
                                        std::uint64_t &offset);
    void handleConcurrencyAccess(ExecutionState &state,
                                 std::vector<ref<Expr>> &arguments,
                                 bool write);
    /* Scheduling-interface gates: a state is driven either by the harness
     * intrinsics or by the native pthread model, never both. */
    bool enterHarnessScheduling(ExecutionState &state, const char *name);
    bool enterNativeThreads(ExecutionState &state, const char *name,
                            bool preserveBusyTrylock = false);
    bool getConcreteThreadId(ExecutionState &state, ref<Expr> argument,
                             const char *name, std::uint64_t &thread);
    bool writeConcreteWord(ExecutionState &state, ref<Expr> address,
                           ref<Expr> value, const char *name);
    void reportModelError(ExecutionState &state, const std::string &error);
    /* Re-execute the blocking call once the thread is resumed, then hand
     * control to the scheduler. */
    void blockAndReschedule(ExecutionState &state);
    /* Shared pthread/trace condition-variable protocol. bindResult binds
     * the pthread int return value; the trace intrinsics return void. */
    void conditionWait(ExecutionState &state, KInstruction *target,
                       const char *name, std::uint64_t condObject,
                       std::uint64_t condOffset, std::uint64_t mutexObject,
                       std::uint64_t mutexOffset, bool bindResult);
    void conditionSignal(ExecutionState &state, KInstruction *target,
                         std::uint64_t object, std::uint64_t offset,
                         bool bindResult, bool mergeNotifierClock);
    void conditionBroadcast(ExecutionState &state, KInstruction *target,
                            std::uint64_t object, std::uint64_t offset,
                            bool bindResult, bool mergeNotifierClock);
    
    /* Handlers */

#define HANDLER(name) void name(ExecutionState &state, \
                                KInstruction *target, \
                                std::vector< ref<Expr> > &arguments)
    HANDLER(handleAbort);
    HANDLER(handleAssert);
    HANDLER(handleAssertFail);
    HANDLER(handleAssume);
    HANDLER(handleCalloc);
    HANDLER(handleCheckMemoryAccess);
    HANDLER(handleConcurrencyBlock);
    HANDLER(handleConcurrencyCondBroadcast);
    HANDLER(handleConcurrencyCondSignal);
    HANDLER(handleConcurrencyCondWait);
    HANDLER(handleConcurrencyCreateThread);
    HANDLER(handleConcurrencyDeclare);
    HANDLER(handleConcurrencyDeadlock);
    HANDLER(handleConcurrencyFinishThread);
    HANDLER(handleConcurrencyJoinThread);
    HANDLER(handleConcurrencyMutexLock);
    HANDLER(handleConcurrencyMutexUnlock);
    HANDLER(handleConcurrencyRead);
    HANDLER(handleConcurrencyResetScheduler);
    HANDLER(handleConcurrencySchedule);
    HANDLER(handleConcurrencySetThread);
    HANDLER(handleConcurrencyUnblock);
    HANDLER(handleConcurrencyWrite);
    HANDLER(handleConcurrencyYield);
    HANDLER(handlePthreadCondBroadcast);
    HANDLER(handlePthreadCondDestroy);
    HANDLER(handlePthreadCondInit);
    HANDLER(handlePthreadCondSignal);
    HANDLER(handlePthreadCondWait);
    HANDLER(handlePthreadCreate);
    HANDLER(handlePthreadDetach);
    HANDLER(handlePthreadEqual);
    HANDLER(handlePthreadExit);
    HANDLER(handlePthreadJoin);
    HANDLER(handlePthreadMutexDestroy);
    HANDLER(handlePthreadMutexInit);
    HANDLER(handlePthreadMutexLock);
    HANDLER(handlePthreadMutexTrylock);
    HANDLER(handlePthreadMutexUnlock);
    HANDLER(handlePthreadSelf);
    HANDLER(handleSchedYield);
    HANDLER(handleDefineFixedObject);
    HANDLER(handleDelete);    
    HANDLER(handleDeleteArray);
#ifdef SUPPORT_KLEE_EH_CXX
    HANDLER(handleEhUnwindRaiseExceptionImpl);
    HANDLER(handleEhTypeid);
#endif
    HANDLER(handleErrnoLocation);
    HANDLER(handleExit);
    HANDLER(handleFree);
    HANDLER(handleGetErrno);
    HANDLER(handleGetObjSize);
    HANDLER(handleGetValue);
    HANDLER(handleIsSymbolic);
    HANDLER(handleMakeSymbolic);
    HANDLER(handleMalloc);
    HANDLER(handleMemalign);
    HANDLER(handleMarkGlobal);
    HANDLER(handleMarkInteresting);
    HANDLER(handleOpenMerge);
    HANDLER(handleCloseMerge);
    HANDLER(handleNew);
    HANDLER(handleNewArray);
    HANDLER(handlePreferCex);
    HANDLER(handlePosixPreferCex);
    HANDLER(handlePrintExpr);
    HANDLER(handlePrintRange);
    HANDLER(handleRange);
    HANDLER(handleRealloc);
    HANDLER(handleReportError);
    HANDLER(handleRevirtObjects);
    HANDLER(handleSetForking);
    HANDLER(handleSilentExit);
    HANDLER(handleStackTrace);
    HANDLER(handleUnderConstrained);
    HANDLER(handleWarning);
    HANDLER(handleWarningOnce);
#undef HANDLER
  };
} // End klee namespace

#endif /* KLEE_SPECIALFUNCTIONHANDLER_H */
