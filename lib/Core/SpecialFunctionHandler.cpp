//===-- SpecialFunctionHandler.cpp ----------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "SpecialFunctionHandler.h"

#include "ExecutionState.h"
#include "Executor.h"
#include "Memory.h"
#include "MemoryManager.h"
#include "MergeHandler.h"
#include "Searcher.h"
#include "StatsTracker.h"
#include "TimingSolver.h"

#include "klee/Config/config.h"
#include "klee/Module/KInstruction.h"
#include "klee/Module/KModule.h"
#include "klee/Solver/SolverCmdLine.h"
#include "klee/Support/Casting.h"
#include "klee/Support/Debug.h"
#include "klee/Support/ErrorHandling.h"
#include "klee/Support/OptionCategories.h"

#include "klee/Support/CompilerWarning.h"
DISABLE_WARNING_PUSH
DISABLE_WARNING_DEPRECATED_DECLARATIONS
#include "llvm/ADT/Twine.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
DISABLE_WARNING_POP

#include <array>
#include <cerrno>
#include <sstream>

using namespace llvm;
using namespace klee;

namespace {
cl::opt<bool>
    ReadablePosix("readable-posix-inputs", cl::init(false),
                  cl::desc("Prefer creation of POSIX inputs (command-line "
                           "arguments, files, etc.) with human readable bytes. "
                           "Note: option is expensive when creating lots of "
                           "tests (default=false)"),
                  cl::cat(TestGenCat));

cl::opt<bool>
    SilentKleeAssume("silent-klee-assume", cl::init(false),
                     cl::desc("Silently terminate paths with an infeasible "
                              "condition given to klee_assume rather than "
                              "emitting an error (default=false)"),
                     cl::cat(TerminationCat));
} // namespace

/// \todo Almost all of the demands in this file should be replaced
/// with terminateState calls.

///

// FIXME: We are more or less committed to requiring an intrinsic
// library these days. We can move some of this stuff there,
// especially things like realloc which have complicated semantics
// w.r.t. forking. Among other things this makes delayed query
// dispatch easier to implement.
static constexpr std::array handlerInfo = {
#define add(name, handler, ret) SpecialFunctionHandler::HandlerInfo{ name, \
                                  &SpecialFunctionHandler::handler, \
                                  false, ret, false }
#define addDNR(name, handler) SpecialFunctionHandler::HandlerInfo{ name, \
                                &SpecialFunctionHandler::handler, \
                                true, false, false }
  addDNR("__assert_rtn", handleAssertFail),
  addDNR("__assert_fail", handleAssertFail),
  addDNR("__assert", handleAssertFail),
  addDNR("_assert", handleAssert),
  addDNR("abort", handleAbort),
  addDNR("_exit", handleExit),
  addDNR("_Exit", handleExit),
  SpecialFunctionHandler::HandlerInfo{ "exit", &SpecialFunctionHandler::handleExit, true, false, true },
  addDNR("klee_abort", handleAbort),
  addDNR("klee_silent_exit", handleSilentExit),
  addDNR("klee_report_error", handleReportError),
  add("aligned_alloc", handleMemalign, true),
  add("calloc", handleCalloc, true),
  add("free", handleFree, false),
  add("klee_assume", handleAssume, false),
  add("klee_check_memory_access", handleCheckMemoryAccess, false),
  add("klee_concurrency_block", handleConcurrencyBlock, false),
  add("klee_concurrency_cond_broadcast", handleConcurrencyCondBroadcast,
      false),
  add("klee_concurrency_cond_signal", handleConcurrencyCondSignal, false),
  add("klee_concurrency_cond_wait", handleConcurrencyCondWait, false),
  add("klee_concurrency_create_thread", handleConcurrencyCreateThread, false),
  add("klee_concurrency_declare", handleConcurrencyDeclare, false),
  addDNR("klee_concurrency_deadlock", handleConcurrencyDeadlock),
  add("klee_concurrency_finish_thread", handleConcurrencyFinishThread, false),
  add("klee_concurrency_join_thread", handleConcurrencyJoinThread, false),
  add("klee_concurrency_mutex_lock", handleConcurrencyMutexLock, false),
  add("klee_concurrency_mutex_unlock", handleConcurrencyMutexUnlock, false),
  add("klee_concurrency_read", handleConcurrencyRead, false),
  add("klee_concurrency_reset_scheduler", handleConcurrencyResetScheduler,
      false),
  add("klee_concurrency_schedule", handleConcurrencySchedule, true),
  add("klee_concurrency_set_thread", handleConcurrencySetThread, false),
  add("klee_concurrency_unblock", handleConcurrencyUnblock, false),
  add("klee_concurrency_write", handleConcurrencyWrite, false),
  add("klee_concurrency_yield", handleConcurrencyYield, false),
  add("pthread_cond_broadcast", handlePthreadCondBroadcast, true),
  add("pthread_cond_destroy", handlePthreadCondDestroy, true),
  add("pthread_cond_init", handlePthreadCondInit, true),
  add("pthread_cond_signal", handlePthreadCondSignal, true),
  add("pthread_cond_wait", handlePthreadCondWait, true),
  add("pthread_create", handlePthreadCreate, true),
  add("pthread_detach", handlePthreadDetach, true),
  add("pthread_equal", handlePthreadEqual, true),
  addDNR("pthread_exit", handlePthreadExit),
  add("pthread_join", handlePthreadJoin, true),
  add("pthread_mutex_destroy", handlePthreadMutexDestroy, true),
  add("pthread_mutex_init", handlePthreadMutexInit, true),
  add("pthread_mutex_lock", handlePthreadMutexLock, true),
  add("pthread_mutex_trylock", handlePthreadMutexTrylock, true),
  add("pthread_mutex_unlock", handlePthreadMutexUnlock, true),
  add("pthread_self", handlePthreadSelf, true),
  add("sched_yield", handleSchedYield, true),
  add("klee_get_valuef", handleGetValue, true),
  add("klee_get_valued", handleGetValue, true),
  add("klee_get_valuel", handleGetValue, true),
  add("klee_get_valuell", handleGetValue, true),
  add("klee_get_value_i32", handleGetValue, true),
  add("klee_get_value_i64", handleGetValue, true),
  add("klee_define_fixed_object", handleDefineFixedObject, false),
  add("klee_get_obj_size", handleGetObjSize, true),
  add("klee_get_errno", handleGetErrno, true),
#ifndef __APPLE__
  add("__errno_location", handleErrnoLocation, true),
#else
  add("__error", handleErrnoLocation, true),
#endif
  add("klee_is_symbolic", handleIsSymbolic, true),
  add("klee_make_symbolic", handleMakeSymbolic, false),
  add("klee_mark_global", handleMarkGlobal, false),
  add("klee_mark_interesting", handleMarkInteresting, false),
  add("klee_open_merge", handleOpenMerge, false),
  add("klee_close_merge", handleCloseMerge, false),
  add("klee_prefer_cex", handlePreferCex, false),
  add("klee_posix_prefer_cex", handlePosixPreferCex, false),
  add("klee_print_expr", handlePrintExpr, false),
  add("klee_print_range", handlePrintRange, false),
  add("klee_set_forking", handleSetForking, false),
  add("klee_stack_trace", handleStackTrace, false),
  add("klee_warning", handleWarning, false),
  add("klee_warning_once", handleWarningOnce, false),
  add("malloc", handleMalloc, true),
  add("memalign", handleMemalign, true),
  add("realloc", handleRealloc, true),

#ifdef SUPPORT_KLEE_EH_CXX
  add("_klee_eh_Unwind_RaiseException_impl", handleEhUnwindRaiseExceptionImpl, false),
  add("klee_eh_typeid_for", handleEhTypeid, true),
#endif

  // operator delete[](void*)
  add("_ZdaPv", handleDeleteArray, false),
  // operator delete(void*)
  add("_ZdlPv", handleDelete, false),

  // operator new[](unsigned int)
  add("_Znaj", handleNewArray, true),
  // operator new(unsigned int)
  add("_Znwj", handleNew, true),

  // FIXME-64: This is wrong for 64-bit long...

  // operator new[](unsigned long)
  add("_Znam", handleNewArray, true),
  // operator new(unsigned long)
  add("_Znwm", handleNew, true),

#undef addDNR
#undef add
};

SpecialFunctionHandler::SpecialFunctionHandler(Executor &_executor) 
  : executor(_executor) {}

void SpecialFunctionHandler::prepare(
    std::vector<const char *> &preservedFunctions) {
  for (auto &hi : handlerInfo) {
    Function *f = executor.kmodule->module->getFunction(hi.name);

    // No need to create if the function doesn't exist, since it cannot
    // be called in that case.
    if (f && (!hi.doNotOverride || f->isDeclaration())) {
      preservedFunctions.push_back(hi.name);
      // Make sure NoReturn attribute is set, for optimization and
      // coverage counting.
      if (hi.doesNotReturn)
        f->addFnAttr(Attribute::NoReturn);

      // Change to a declaration since we handle internally (simplifies
      // module and allows deleting dead code).
      if (!f->isDeclaration())
        f->deleteBody();
    }
  }
}

void SpecialFunctionHandler::bind() {
  for (auto &hi : handlerInfo) {
    Function *f = executor.kmodule->module->getFunction(hi.name);

    if (f && (!hi.doNotOverride || f->isDeclaration()))
      handlers[f] = std::make_pair(hi.handler, hi.hasReturnValue);
  }
}


bool SpecialFunctionHandler::handle(ExecutionState &state, 
                                    Function *f,
                                    KInstruction *target,
                                    std::vector< ref<Expr> > &arguments) {
  handlers_ty::iterator it = handlers.find(f);
  if (it != handlers.end()) {    
    Handler h = it->second.first;
    bool hasReturnValue = it->second.second;
     // FIXME: Check this... add test?
    if (!hasReturnValue && !target->inst->use_empty()) {
      executor.terminateStateOnExecError(state, 
                                         "expected return value from void special function");
    } else {
      (this->*h)(state, target, arguments);
    }
    return true;
  } else {
    return false;
  }
}

/****/

// reads a concrete string from memory
std::string 
SpecialFunctionHandler::readStringAtAddress(ExecutionState &state, 
                                            ref<Expr> addressExpr) {
  ObjectPair op;
  addressExpr = executor.toUnique(state, addressExpr);
  if (!isa<ConstantExpr>(addressExpr)) {
    executor.terminateStateOnUserError(
        state, "Symbolic string pointer passed to one of the klee_ functions");
    return "";
  }
  ref<ConstantExpr> address = cast<ConstantExpr>(addressExpr);
  if (!state.addressSpace.resolveOne(address, op)) {
    executor.terminateStateOnUserError(
        state, "Invalid string pointer passed to one of the klee_ functions");
    return "";
  }
  const MemoryObject *mo = op.first;
  const ObjectState *os = op.second;

  auto relativeOffset = mo->getOffsetExpr(address);
  // the relativeOffset must be concrete as the address is concrete
  size_t offset = cast<ConstantExpr>(relativeOffset)->getZExtValue();

  std::ostringstream buf;
  char c = 0;
  for (size_t i = offset; i < mo->size; ++i) {
    ref<Expr> cur = os->read8(i);
    cur = executor.toUnique(state, cur);
    assert(isa<ConstantExpr>(cur) && 
           "hit symbolic char while reading concrete string");
    c = cast<ConstantExpr>(cur)->getZExtValue(8);
    if (c == '\0') {
      // we read the whole string
      break;
    }

    buf << c;
  }

  if (c != '\0') {
      klee_warning_once(0, "String not terminated by \\0 passed to "
                           "one of the klee_ functions");
  }

  return buf.str();
}

/****/

void SpecialFunctionHandler::handleAbort(ExecutionState &state,
                                         KInstruction *target,
                                         std::vector<ref<Expr>> &arguments) {
  assert(arguments.size() == 0 && "invalid number of arguments to abort");
  executor.terminateStateOnProgramError(state, "abort failure",
                                        StateTerminationType::Abort);
}

void SpecialFunctionHandler::handleExit(ExecutionState &state,
                                        KInstruction *target,
                                        std::vector<ref<Expr>> &arguments) {
  assert(arguments.size() == 1 && "invalid number of arguments to exit");
  executor.terminateStateOnExit(state);
}

void SpecialFunctionHandler::handleSilentExit(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  assert(arguments.size() == 1 && "invalid number of arguments to exit");
  executor.terminateStateEarlyUser(state, "");
}

void SpecialFunctionHandler::handleAssert(ExecutionState &state,
                                          KInstruction *target,
                                          std::vector<ref<Expr>> &arguments) {
  assert(arguments.size() == 3 && "invalid number of arguments to _assert");
  executor.terminateStateOnProgramError(
      state, "ASSERTION FAIL: " + readStringAtAddress(state, arguments[0]),
      StateTerminationType::Assert);
}

void SpecialFunctionHandler::handleAssertFail(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  assert(arguments.size() == 4 &&
         "invalid number of arguments to __assert_fail");
  executor.terminateStateOnProgramError(
      state, "ASSERTION FAIL: " + readStringAtAddress(state, arguments[0]),
      StateTerminationType::Assert);
}

void SpecialFunctionHandler::handleReportError(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  assert(arguments.size() == 4 &&
         "invalid number of arguments to klee_report_error");

  // arguments[0,1,2,3] are file, line, message, suffix
  executor.terminateStateOnProgramError(
      state, readStringAtAddress(state, arguments[2]),
      StateTerminationType::ReportError, "",
      readStringAtAddress(state, arguments[3]).c_str());
}

void SpecialFunctionHandler::handleOpenMerge(ExecutionState &state,
    KInstruction *target,
    std::vector<ref<Expr> > &arguments) {
  if (!UseMerge) {
    klee_warning_once(0, "klee_open_merge ignored, use '-use-merge'");
    return;
  }

  state.openMergeStack.push_back(
      ref<MergeHandler>(new MergeHandler(&executor, &state)));

  if (DebugLogMerge)
    llvm::errs() << "open merge: " << &state << "\n";
}

void SpecialFunctionHandler::handleCloseMerge(ExecutionState &state,
    KInstruction *target,
    std::vector<ref<Expr> > &arguments) {
  if (!UseMerge) {
    klee_warning_once(0, "klee_close_merge ignored, use '-use-merge'");
    return;
  }
  Instruction *i = target->inst;

  if (DebugLogMerge)
    llvm::errs() << "close merge: " << &state << " at [" << *i << "]\n";

  if (state.openMergeStack.empty()) {
    std::ostringstream warning;
    warning << &state << " ran into a close at " << i << " without a preceding open";
    klee_warning("%s", warning.str().c_str());
  } else {
    assert(executor.mergingSearcher->inCloseMerge.find(&state) ==
               executor.mergingSearcher->inCloseMerge.end() &&
           "State cannot run into close_merge while being closed");
    executor.mergingSearcher->inCloseMerge.insert(&state);
    state.openMergeStack.back()->addClosedState(&state, i);
    state.openMergeStack.pop_back();
  }
}

void SpecialFunctionHandler::handleNew(ExecutionState &state,
                         KInstruction *target,
                         std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==1 && "invalid number of arguments to new");

  executor.executeAlloc(state, arguments[0], false, target);
}

void SpecialFunctionHandler::handleDelete(ExecutionState &state,
                            KInstruction *target,
                            std::vector<ref<Expr> > &arguments) {
  // FIXME: Should check proper pairing with allocation type (malloc/free,
  // new/delete, new[]/delete[]).

  // XXX should type check args
  assert(arguments.size()==1 && "invalid number of arguments to delete");
  executor.executeFree(state, arguments[0]);
}

void SpecialFunctionHandler::handleNewArray(ExecutionState &state,
                              KInstruction *target,
                              std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==1 && "invalid number of arguments to new[]");
  executor.executeAlloc(state, arguments[0], false, target);
}

void SpecialFunctionHandler::handleDeleteArray(ExecutionState &state,
                                 KInstruction *target,
                                 std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==1 && "invalid number of arguments to delete[]");
  executor.executeFree(state, arguments[0]);
}

void SpecialFunctionHandler::handleMalloc(ExecutionState &state,
                                  KInstruction *target,
                                  std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==1 && "invalid number of arguments to malloc");
  executor.executeAlloc(state, arguments[0], false, target);
}

void SpecialFunctionHandler::handleMemalign(ExecutionState &state,
                                            KInstruction *target,
                                            std::vector<ref<Expr>> &arguments) {
  if (arguments.size() != 2) {
    executor.terminateStateOnUserError(state,
      "Incorrect number of arguments to memalign(size_t alignment, size_t size)");
    return;
  }

  std::pair<ref<Expr>, ref<Expr>> alignmentRangeExpr =
      executor.solver->getRange(state.constraints, arguments[0],
                                state.queryMetaData);
  ref<Expr> alignmentExpr = alignmentRangeExpr.first;
  auto alignmentConstExpr = dyn_cast<ConstantExpr>(alignmentExpr);

  if (!alignmentConstExpr) {
    executor.terminateStateOnUserError(state, "Could not determine size of symbolic alignment");
    return;
  }

  uint64_t alignment = alignmentConstExpr->getZExtValue();

  // Warn, if the expression has more than one solution
  if (alignmentRangeExpr.first != alignmentRangeExpr.second) {
    klee_warning_once(
        0, "Symbolic alignment for memalign. Choosing smallest alignment");
  }

  executor.executeAlloc(state, arguments[1], false, target, false, 0,
                        alignment);
}

#ifdef SUPPORT_KLEE_EH_CXX
void SpecialFunctionHandler::handleEhUnwindRaiseExceptionImpl(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  assert(arguments.size() == 1 &&
         "invalid number of arguments to _klee_eh_Unwind_RaiseException_impl");

  ref<ConstantExpr> exceptionObject = dyn_cast<ConstantExpr>(arguments[0]);
  if (!exceptionObject.get()) {
    executor.terminateStateOnExecError(state, "Internal error: Symbolic exception pointer");
    return;
  }

  if (isa_and_nonnull<SearchPhaseUnwindingInformation>(
          state.unwindingInformation.get())) {
    executor.terminateStateOnExecError(
        state,
        "Internal error: Unwinding restarted during an ongoing search phase");
    return;
  }

  state.unwindingInformation =
      std::make_unique<SearchPhaseUnwindingInformation>(exceptionObject,
                                                        state.stack.size() - 1);

  executor.unwindToNextLandingpad(state);
}

void SpecialFunctionHandler::handleEhTypeid(ExecutionState &state,
                                            KInstruction *target,
                                            std::vector<ref<Expr>> &arguments) {
  assert(arguments.size() == 1 &&
         "invalid number of arguments to klee_eh_typeid_for");

  executor.bindLocal(target, state, executor.getEhTypeidFor(arguments[0]));
}
#endif // SUPPORT_KLEE_EH_CXX

void SpecialFunctionHandler::handleAssume(ExecutionState &state,
                            KInstruction *target,
                            std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 && "invalid number of arguments to klee_assume");
  
  ref<Expr> e = arguments[0];
  
  if (e->getWidth() != Expr::Bool)
    e = NeExpr::create(e, ConstantExpr::create(0, e->getWidth()));
  
  bool res;
  bool success __attribute__((unused)) = executor.solver->mustBeFalse(
      state.constraints, e, res, state.queryMetaData);
  assert(success && "FIXME: Unhandled solver failure");
  if (res) {
    executor.terminateStateOnUserError(
        state, "invalid klee_assume call (provably false)", !SilentKleeAssume);
  } else {
    executor.addConstraint(state, e);
  }
}

void SpecialFunctionHandler::handleIsSymbolic(ExecutionState &state,
                                KInstruction *target,
                                std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 && "invalid number of arguments to klee_is_symbolic");

  executor.bindLocal(target, state, 
                     ConstantExpr::create(!isa<ConstantExpr>(arguments[0]),
                                          Expr::Int32));
}

void SpecialFunctionHandler::handlePreferCex(ExecutionState &state,
                                             KInstruction *target,
                                             std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==2 &&
         "invalid number of arguments to klee_prefex_cex");

  ref<Expr> cond = arguments[1];
  if (cond->getWidth() != Expr::Bool)
    cond = NeExpr::create(cond, ConstantExpr::alloc(0, cond->getWidth()));

  state.addCexPreference(cond);
}

void SpecialFunctionHandler::handlePosixPreferCex(ExecutionState &state,
                                             KInstruction *target,
                                             std::vector<ref<Expr> > &arguments) {
  if (ReadablePosix)
    return handlePreferCex(state, target, arguments);
}

void SpecialFunctionHandler::handlePrintExpr(ExecutionState &state,
                                  KInstruction *target,
                                  std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==2 &&
         "invalid number of arguments to klee_print_expr");

  std::string msg_str = readStringAtAddress(state, arguments[0]);
  llvm::errs() << msg_str << ":" << arguments[1] << "\n";
}

void SpecialFunctionHandler::handleSetForking(ExecutionState &state,
                                              KInstruction *target,
                                              std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 &&
         "invalid number of arguments to klee_set_forking");
  ref<Expr> value = executor.toUnique(state, arguments[0]);
  
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(value)) {
    state.forkDisabled = CE->isZero();
  } else {
    executor.terminateStateOnUserError(state, "klee_set_forking requires a constant arg");
  }
}

void SpecialFunctionHandler::handleStackTrace(ExecutionState &state,
                                              KInstruction *target,
                                              std::vector<ref<Expr> > &arguments) {
  state.dumpStack(outs());
}

void SpecialFunctionHandler::handleWarning(ExecutionState &state,
                                           KInstruction *target,
                                           std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 && "invalid number of arguments to klee_warning");

  std::string msg_str = readStringAtAddress(state, arguments[0]);
  klee_warning("%s: %s", state.stack.back().kf->function->getName().data(), 
               msg_str.c_str());
}

void SpecialFunctionHandler::handleWarningOnce(ExecutionState &state,
                                               KInstruction *target,
                                               std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 &&
         "invalid number of arguments to klee_warning_once");

  std::string msg_str = readStringAtAddress(state, arguments[0]);
  klee_warning_once(0, "%s: %s", state.stack.back().kf->function->getName().data(),
                    msg_str.c_str());
}

void SpecialFunctionHandler::handlePrintRange(ExecutionState &state,
                                  KInstruction *target,
                                  std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==2 &&
         "invalid number of arguments to klee_print_range");

  std::string msg_str = readStringAtAddress(state, arguments[0]);
  llvm::errs() << msg_str << ":" << arguments[1];
  if (!isa<ConstantExpr>(arguments[1])) {
    // FIXME: Pull into a unique value method?
    ref<ConstantExpr> value;
    bool success __attribute__((unused)) = executor.solver->getValue(
        state.constraints, arguments[1], value, state.queryMetaData);
    assert(success && "FIXME: Unhandled solver failure");
    bool res;
    success = executor.solver->mustBeTrue(state.constraints,
                                          EqExpr::create(arguments[1], value),
                                          res, state.queryMetaData);
    assert(success && "FIXME: Unhandled solver failure");
    if (res) {
      llvm::errs() << " == " << value;
    } else { 
      llvm::errs() << " ~= " << value;
      std::pair<ref<Expr>, ref<Expr>> res = executor.solver->getRange(
          state.constraints, arguments[1], state.queryMetaData);
      llvm::errs() << " (in [" << res.first << ", " << res.second <<"])";
    }
  }
  llvm::errs() << "\n";
}

void SpecialFunctionHandler::handleGetObjSize(ExecutionState &state,
                                  KInstruction *target,
                                  std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==1 &&
         "invalid number of arguments to klee_get_obj_size");
  Executor::ExactResolutionList rl;
  executor.resolveExact(state, arguments[0], rl, "klee_get_obj_size");
  for (Executor::ExactResolutionList::iterator it = rl.begin(), 
         ie = rl.end(); it != ie; ++it) {
    executor.bindLocal(
        target, *it->second,
        ConstantExpr::create(it->first.first->size,
                             executor.kmodule->targetData->getTypeSizeInBits(
                                 target->inst->getType())));
  }
}

void SpecialFunctionHandler::handleGetErrno(ExecutionState &state,
                                            KInstruction *target,
                                            std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==0 &&
         "invalid number of arguments to klee_get_errno");
#ifndef WINDOWS
  int *errno_addr = executor.getErrnoLocation(state);
#else
  int *errno_addr = nullptr;
#endif

  // Retrieve the memory object of the errno variable
  ObjectPair result;
  bool resolved = state.addressSpace.resolveOne(
      ConstantExpr::create((uint64_t)errno_addr, Expr::Int64), result);
  if (!resolved)
    executor.terminateStateOnUserError(state, "Could not resolve address for errno");
  executor.bindLocal(target, state, result.second->read(0, Expr::Int32));
}

void SpecialFunctionHandler::handleErrnoLocation(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr> > &arguments) {
  // Returns the address of the errno variable
  assert(arguments.size() == 0 &&
         "invalid number of arguments to __errno_location/__error");

#ifndef WINDOWS
  int *errno_addr = executor.getErrnoLocation(state);
#else
  int *errno_addr = nullptr;
#endif

  executor.bindLocal(
      target, state,
      ConstantExpr::create((uint64_t)errno_addr,
                           executor.kmodule->targetData->getTypeSizeInBits(
                               target->inst->getType())));
}
void SpecialFunctionHandler::handleCalloc(ExecutionState &state,
                            KInstruction *target,
                            std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==2 &&
         "invalid number of arguments to calloc");

  ref<Expr> size = MulExpr::create(arguments[0],
                                   arguments[1]);
  executor.executeAlloc(state, size, false, target, true);
}

void SpecialFunctionHandler::handleRealloc(ExecutionState &state,
                            KInstruction *target,
                            std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==2 &&
         "invalid number of arguments to realloc");
  ref<Expr> address = arguments[0];
  ref<Expr> size = arguments[1];

  Executor::StatePair zeroSize =
      executor.fork(state, Expr::createIsZero(size), true, BranchType::Realloc);

  if (zeroSize.first) { // size == 0
    executor.executeFree(*zeroSize.first, address, target);   
  }
  if (zeroSize.second) { // size != 0
    Executor::StatePair zeroPointer =
        executor.fork(*zeroSize.second, Expr::createIsZero(address), true,
                      BranchType::Realloc);

    if (zeroPointer.first) { // address == 0
      executor.executeAlloc(*zeroPointer.first, size, false, target);
    } 
    if (zeroPointer.second) { // address != 0
      Executor::ExactResolutionList rl;
      executor.resolveExact(*zeroPointer.second, address, rl, "realloc");
      
      for (Executor::ExactResolutionList::iterator it = rl.begin(), 
             ie = rl.end(); it != ie; ++it) {
        executor.executeAlloc(*it->second, size, false, target, false, 
                              it->first.second);
      }
    }
  }
}

void SpecialFunctionHandler::handleFree(ExecutionState &state,
                          KInstruction *target,
                          std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==1 &&
         "invalid number of arguments to free");
  executor.executeFree(state, arguments[0]);
}

void SpecialFunctionHandler::handleCheckMemoryAccess(ExecutionState &state,
                                                     KInstruction *target,
                                                     std::vector<ref<Expr> > 
                                                       &arguments) {
  assert(arguments.size()==2 &&
         "invalid number of arguments to klee_check_memory_access");

  ref<Expr> address = executor.toUnique(state, arguments[0]);
  ref<Expr> size = executor.toUnique(state, arguments[1]);
  if (!isa<ConstantExpr>(address) || !isa<ConstantExpr>(size)) {
    executor.terminateStateOnUserError(state, "check_memory_access requires constant args");
  } else {
    ObjectPair op;

    if (!state.addressSpace.resolveOne(cast<ConstantExpr>(address), op)) {
      executor.terminateStateOnProgramError(
          state, "check_memory_access: memory error", StateTerminationType::Ptr,
          executor.getAddressInfo(state, address));
    } else {
      ref<Expr> chk = 
        op.first->getBoundsCheckPointer(address, 
                                        cast<ConstantExpr>(size)->getZExtValue());
      if (!chk->isTrue()) {
        executor.terminateStateOnProgramError(
            state, "check_memory_access: memory error",
            StateTerminationType::Ptr, executor.getAddressInfo(state, address));
      }
    }
  }
}

static const char *concurrencyAccessName(bool write) {
  return write ? "write" : "read";
}

void SpecialFunctionHandler::handleConcurrencyCreateThread(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  if (!enterHarnessScheduling(state, "klee_concurrency_create_thread"))
    return;
  assert(arguments.size() == 1 &&
         "invalid number of arguments to klee_concurrency_create_thread");
  ref<Expr> value = executor.toUnique(state, arguments[0]);
  auto *constant = dyn_cast<ConstantExpr>(value);
  if (!constant) {
    executor.terminateStateOnUserError(
        state, "klee_concurrency_create_thread requires a concrete thread id");
    return;
  }
  std::string error;
  if (!state.concurrency.createThread(constant->getZExtValue(), error))
    executor.terminateStateOnProgramError(
        state, "concurrency model error: " + error,
        StateTerminationType::Model);
}

void SpecialFunctionHandler::handleConcurrencyDeclare(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  if (!enterHarnessScheduling(state, "klee_concurrency_declare"))
    return;
  assert(arguments.size() == 4 &&
         "invalid number of arguments to klee_concurrency_declare");
  ref<Expr> threadExpr = executor.toUnique(state, arguments[0]);
  ref<Expr> kindExpr = executor.toUnique(state, arguments[1]);
  ref<Expr> addressExpr = executor.toUnique(state, arguments[2]);
  ref<Expr> sizeExpr = executor.toUnique(state, arguments[3]);
  auto *thread = dyn_cast<ConstantExpr>(threadExpr);
  auto *kind = dyn_cast<ConstantExpr>(kindExpr);
  auto *address = dyn_cast<ConstantExpr>(addressExpr);
  auto *size = dyn_cast<ConstantExpr>(sizeExpr);
  if (!thread || !kind || !address || !size) {
    executor.terminateStateOnUserError(
        state, "klee_concurrency_declare requires concrete arguments");
    return;
  }

  const std::uint32_t kindValue = kind->getZExtValue();
  const std::uint64_t addressValue = address->getZExtValue();
  const std::uint64_t sizeValue = size->getZExtValue();
  std::uint64_t objectValue = 0;
  std::uint64_t offsetValue = addressValue;
  if ((kindValue ==
           static_cast<std::uint32_t>(ConcurrencyTransitionKind::Read) ||
       kindValue ==
           static_cast<std::uint32_t>(ConcurrencyTransitionKind::Write)) &&
      sizeValue != 0) {
    ObjectPair op;
    if (!state.addressSpace.resolveOne(address, op)) {
      executor.terminateStateOnProgramError(
          state, "klee_concurrency_declare: memory error",
          StateTerminationType::Ptr,
          executor.getAddressInfo(state, addressExpr));
      return;
    }
    ref<Expr> bounds = op.first->getBoundsCheckPointer(addressExpr, sizeValue);
    if (!bounds->isTrue()) {
      executor.terminateStateOnProgramError(
          state, "klee_concurrency_declare: memory error",
          StateTerminationType::Ptr,
          executor.getAddressInfo(state, addressExpr));
      return;
    }
    objectValue = op.first->id;
    offsetValue = addressValue - op.first->address;
  } else if (kindValue ==
             static_cast<std::uint32_t>(
                 ConcurrencyTransitionKind::Mutex)) {
    ObjectPair op;
    if (!state.addressSpace.resolveOne(address, op)) {
      executor.terminateStateOnProgramError(
          state, "klee_concurrency_declare: mutex memory error",
          StateTerminationType::Ptr,
          executor.getAddressInfo(state, addressExpr));
      return;
    }
    objectValue = op.first->id;
    offsetValue = addressValue - op.first->address;
  }

  std::string error;
  if (!state.concurrency.declareTransition(
          thread->getZExtValue(), kindValue, objectValue, offsetValue,
          sizeValue, error))
    executor.terminateStateOnProgramError(
        state, "concurrency model error: " + error,
        StateTerminationType::Model);
}

void SpecialFunctionHandler::handleConcurrencySetThread(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  if (!enterHarnessScheduling(state, "klee_concurrency_set_thread"))
    return;
  assert(arguments.size() == 1 &&
         "invalid number of arguments to klee_concurrency_set_thread");
  ref<Expr> value = executor.toUnique(state, arguments[0]);
  auto *constant = dyn_cast<ConstantExpr>(value);
  if (!constant) {
    executor.terminateStateOnUserError(
        state, "klee_concurrency_set_thread requires a concrete thread id");
    return;
  }
  std::string error;
  if (!state.concurrency.setThread(constant->getZExtValue(), error))
    executor.terminateStateOnProgramError(
        state, "concurrency model error: " + error,
        StateTerminationType::Model);
}

void SpecialFunctionHandler::handleConcurrencyDeadlock(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  if (!enterHarnessScheduling(state, "klee_concurrency_deadlock"))
    return;
  assert(arguments.size() == 1 &&
         "invalid number of arguments to klee_concurrency_deadlock");
  ref<Expr> value = executor.toUnique(state, arguments[0]);
  auto *constant = dyn_cast<ConstantExpr>(value);
  if (!constant) {
    executor.terminateStateOnUserError(
        state, "klee_concurrency_deadlock requires a concrete blocked mask");
    return;
  }
  const std::uint64_t blockedMask = constant->getZExtValue();
  std::string error;
  bool verified = false;
  if (!state.concurrency.completePendingTransition(error)) {
    executor.terminateStateOnProgramError(
        state, "concurrency model error: " + error,
        StateTerminationType::Model);
    return;
  }
  if (!state.concurrency.validateDeadlock(blockedMask, verified, error)) {
    executor.terminateStateOnProgramError(
        state, "concurrency model error: " + error,
        StateTerminationType::Model);
    return;
  }
  std::ostringstream message;
  message << "logical-thread deadlock: blocked mask 0x" << std::hex
          << blockedMask << std::dec
          << (verified ? "; verified: every blocked thread waits on a mutex, "
                         "join, or condition that no runnable thread can "
                         "release"
                       : "; harness-declared: at least one blocking reason "
                         "is not engine-verified");
  executor.terminateStateOnProgramError(
      state, message.str(), StateTerminationType::Deadlock);
}

void SpecialFunctionHandler::handleConcurrencyBlock(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  if (!enterHarnessScheduling(state, "klee_concurrency_block"))
    return;
  assert(arguments.size() == 3 &&
         "invalid number of arguments to klee_concurrency_block");
  ref<Expr> threadExpr = executor.toUnique(state, arguments[0]);
  ref<Expr> kindExpr = executor.toUnique(state, arguments[1]);
  auto *thread = dyn_cast<ConstantExpr>(threadExpr);
  auto *kind = dyn_cast<ConstantExpr>(kindExpr);
  if (!thread || !kind) {
    executor.terminateStateOnUserError(
        state, "klee_concurrency_block requires concrete arguments");
    return;
  }
  std::uint64_t object = 0;
  std::uint64_t offset = 0;
  if (kind->getZExtValue() ==
          static_cast<std::uint32_t>(ConcurrencyBlockKind::Mutex) &&
      !getConcreteConcurrencyLocation(state, arguments[2],
                                      "klee_concurrency_block", object,
                                      offset))
    return;
  std::string error;
  if (!state.concurrency.blockThread(thread->getZExtValue(),
                                     kind->getZExtValue(), object, offset,
                                     error))
    executor.terminateStateOnProgramError(
        state, "concurrency model error: " + error,
        StateTerminationType::Model);
}

void SpecialFunctionHandler::handleConcurrencyUnblock(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  if (!enterHarnessScheduling(state, "klee_concurrency_unblock"))
    return;
  assert(arguments.size() == 1 &&
         "invalid number of arguments to klee_concurrency_unblock");
  ref<Expr> value = executor.toUnique(state, arguments[0]);
  auto *constant = dyn_cast<ConstantExpr>(value);
  if (!constant) {
    executor.terminateStateOnUserError(
        state, "klee_concurrency_unblock requires a concrete thread id");
    return;
  }
  std::string error;
  if (!state.concurrency.unblockThread(constant->getZExtValue(), error))
    executor.terminateStateOnProgramError(
        state, "concurrency model error: " + error,
        StateTerminationType::Model);
}

void SpecialFunctionHandler::handleConcurrencyFinishThread(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  if (!enterHarnessScheduling(state, "klee_concurrency_finish_thread"))
    return;
  assert(arguments.empty() &&
         "invalid arguments to klee_concurrency_finish_thread");
  std::string error;
  if (!state.concurrency.finishThread(error))
    executor.terminateStateOnProgramError(
        state, "concurrency model error: " + error,
        StateTerminationType::Model);
}

void SpecialFunctionHandler::handleConcurrencyJoinThread(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  if (!enterHarnessScheduling(state, "klee_concurrency_join_thread"))
    return;
  assert(arguments.size() == 1 &&
         "invalid number of arguments to klee_concurrency_join_thread");
  ref<Expr> value = executor.toUnique(state, arguments[0]);
  auto *constant = dyn_cast<ConstantExpr>(value);
  if (!constant) {
    executor.terminateStateOnUserError(
        state, "klee_concurrency_join_thread requires a concrete thread id");
    return;
  }
  std::string error;
  if (!state.concurrency.joinThread(constant->getZExtValue(), error))
    executor.terminateStateOnProgramError(
        state, "concurrency model error: " + error,
        StateTerminationType::Model);
}

bool SpecialFunctionHandler::getConcreteConcurrencyLocation(
    ExecutionState &state, ref<Expr> argument, const char *name,
    std::uint64_t &object, std::uint64_t &offset) {
  ref<Expr> value = executor.toUnique(state, argument);
  auto *constant = dyn_cast<ConstantExpr>(value);
  if (!constant) {
    executor.terminateStateOnUserError(
        state, std::string(name) + " requires a concrete address");
    return false;
  }
  ObjectPair op;
  if (!state.addressSpace.resolveOne(constant, op)) {
    executor.terminateStateOnProgramError(
        state, std::string(name) + ": memory error",
        StateTerminationType::Ptr, executor.getAddressInfo(state, value));
    return false;
  }
  const std::uint64_t address = constant->getZExtValue();
  object = op.first->id;
  offset = address - op.first->address;
  return true;
}

void SpecialFunctionHandler::handleConcurrencyMutexLock(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  assert(arguments.size() == 1 &&
         "invalid number of arguments to klee_concurrency_mutex_lock");
  std::uint64_t object = 0;
  std::uint64_t offset = 0;
  if (!getConcreteConcurrencyLocation(state, arguments[0],
                                      "klee_concurrency_mutex_lock", object,
                                      offset))
    return;
  std::string error;
  if (state.concurrency.inNativeMode()) {
    state.lastBusyTrylock = nullptr;
    std::uint64_t owner = 0;
    if (state.concurrency.mutexOwner(object, offset, owner)) {
      const std::uint64_t self = state.runningThread;
      if (owner == self) {
        reportModelError(state, "klee_concurrency_mutex_lock: the calling "
                                "thread already owns this non-recursive "
                                "mutex");
        return;
      }
      if (!state.concurrency.blockThread(
              self, static_cast<std::uint32_t>(ConcurrencyBlockKind::Mutex),
              object, offset, error)) {
        reportModelError(state, error);
        return;
      }
      blockAndReschedule(state);
      return;
    }
  }
  if (!state.concurrency.mutexLock(object, offset, error)) {
    executor.terminateStateOnProgramError(
        state, "concurrency model error: " + error,
        StateTerminationType::Model);
    return;
  }
  if (state.concurrency.inNativeMode())
    executor.scheduleNativeThreads(state);
}

void SpecialFunctionHandler::handleConcurrencyMutexUnlock(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  assert(arguments.size() == 1 &&
         "invalid number of arguments to klee_concurrency_mutex_unlock");
  std::uint64_t object = 0;
  std::uint64_t offset = 0;
  if (!getConcreteConcurrencyLocation(state, arguments[0],
                                      "klee_concurrency_mutex_unlock", object,
                                      offset))
    return;
  std::string error;
  if (!state.concurrency.mutexUnlock(object, offset, error))
    executor.terminateStateOnProgramError(
        state, "concurrency model error: " + error,
        StateTerminationType::Model);
  else if (state.concurrency.inNativeMode()) {
    state.lastBusyTrylock = nullptr;
    std::vector<std::uint64_t> waiters;
    state.concurrency.collectBlocked(ConcurrencyBlockKind::Mutex, object,
                                     offset, waiters);
    for (std::uint64_t waiter : waiters) {
      if (!state.concurrency.unblockThread(waiter, error)) {
        reportModelError(state, error);
        return;
      }
    }
    executor.scheduleNativeThreads(state);
  }
}

void SpecialFunctionHandler::handleConcurrencyAccess(
    ExecutionState &state, std::vector<ref<Expr>> &arguments, bool write) {
  assert(arguments.size() == 3 &&
         "invalid number of arguments to a KLEE concurrency access");
  ref<Expr> addressExpr = executor.toUnique(state, arguments[0]);
  ref<Expr> sizeExpr = executor.toUnique(state, arguments[1]);
  ref<Expr> siteExpr = executor.toUnique(state, arguments[2]);
  auto *addressConstant = dyn_cast<ConstantExpr>(addressExpr);
  auto *sizeConstant = dyn_cast<ConstantExpr>(sizeExpr);
  auto *siteConstant = dyn_cast<ConstantExpr>(siteExpr);
  if (!addressConstant || !sizeConstant || !siteConstant) {
    executor.terminateStateOnUserError(
        state, "KLEE concurrency accesses require concrete address, size, and site id");
    return;
  }

  ObjectPair op;
  if (!state.addressSpace.resolveOne(addressConstant, op)) {
    executor.terminateStateOnProgramError(
        state, "KLEE concurrency access: memory error",
        StateTerminationType::Ptr,
        executor.getAddressInfo(state, addressExpr));
    return;
  }
  const std::uint64_t size = sizeConstant->getZExtValue();
  ref<Expr> bounds = op.first->getBoundsCheckPointer(addressExpr, size);
  if (!bounds->isTrue()) {
    executor.terminateStateOnProgramError(
        state, "KLEE concurrency access: memory error",
        StateTerminationType::Ptr,
        executor.getAddressInfo(state, addressExpr));
    return;
  }

  ConcurrencyRace race;
  std::string error;
  const std::uint64_t address = addressConstant->getZExtValue();
  const ConcurrencyAccessResult result = state.concurrency.recordAccess(
      op.first->id, address - op.first->address, address, size, write,
      siteConstant->getZExtValue(), race, error);
  if (result == ConcurrencyAccessResult::Error) {
    executor.terminateStateOnProgramError(
        state, "concurrency model error: " + error,
        StateTerminationType::Model);
    return;
  }
  if (result == ConcurrencyAccessResult::Race) {
    std::ostringstream message;
    message << "data race: thread " << race.currentThread << " site "
            << race.currentSite << ' '
            << concurrencyAccessName(race.currentWrite)
            << " conflicts with thread " << race.previousThread << " site "
            << race.previousSite << ' '
            << concurrencyAccessName(race.previousWrite);
    std::ostringstream info;
    info << "overlap address: 0x" << std::hex << race.address << std::dec
         << "\noverlap size: " << race.size << " byte(s)\n";
    executor.terminateStateOnProgramError(
        state, message.str(), StateTerminationType::Race, info.str());
  }
}

void SpecialFunctionHandler::handleConcurrencyRead(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  handleConcurrencyAccess(state, arguments, false);
}

void SpecialFunctionHandler::handleConcurrencyWrite(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  handleConcurrencyAccess(state, arguments, true);
}

void SpecialFunctionHandler::handleConcurrencyResetScheduler(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  if (!enterHarnessScheduling(state, "klee_concurrency_reset_scheduler"))
    return;
  assert(arguments.empty() &&
         "invalid arguments to klee_concurrency_reset_scheduler");
  std::string error;
  if (!state.concurrency.resetScheduler(error))
    executor.terminateStateOnProgramError(
        state, "concurrency model error: " + error,
        StateTerminationType::Model);
}

void SpecialFunctionHandler::handleConcurrencySchedule(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  if (!enterHarnessScheduling(state, "klee_concurrency_schedule"))
    return;
  assert(arguments.size() == 3 &&
         "invalid number of arguments to klee_concurrency_schedule");

  ref<Expr> runnableExpr = executor.toUnique(state, arguments[0]);
  ref<Expr> choiceExpr = arguments[1];
  ref<Expr> maxSwitchesExpr = executor.toUnique(state, arguments[2]);
  auto *runnable = dyn_cast<ConstantExpr>(runnableExpr);
  auto *maxSwitches = dyn_cast<ConstantExpr>(maxSwitchesExpr);
  if (!runnable || !maxSwitches) {
    executor.terminateStateOnUserError(
        state, "klee_concurrency_schedule requires concrete runnable mask and switch bound");
    return;
  }

  std::vector<std::uint64_t> candidates;
  std::string error;
  if (!state.concurrency.scheduleCandidates(
          runnable->getZExtValue(), maxSwitches->getZExtValue(), candidates,
          error)) {
    executor.terminateStateOnProgramError(
        state, "concurrency model error: " + error,
        StateTerminationType::Model);
    return;
  }
  if (candidates.empty()) {
    executor.terminateStateEarly(
        state, "concurrency schedule context-switch bound exhausted",
        StateTerminationType::MaxDepth);
    return;
  }

  const Expr::Width width = choiceExpr->getWidth();
  ref<Expr> ordinal;
  if (candidates.size() == 1)
    ordinal = ConstantExpr::create(0, width);
  else
    ordinal = URemExpr::create(
        choiceExpr, ConstantExpr::create(candidates.size(), width));
  std::vector<ref<Expr>> conditions;
  std::vector<std::uint64_t> feasibleCandidates;
  for (std::size_t index = 0; index < candidates.size(); ++index) {
    ref<Expr> condition =
        EqExpr::create(ordinal, ConstantExpr::create(index, width));
    bool feasible = false;
    if (!executor.solver->mayBeTrue(state.constraints, condition, feasible,
                                    state.queryMetaData)) {
      executor.terminateStateOnSolverError(
          state, "Query timed out (concurrency schedule).");
      return;
    }
    if (feasible) {
      conditions.push_back(condition);
      feasibleCandidates.push_back(candidates[index]);
    }
  }
  if (conditions.empty()) {
    executor.terminateStateOnSolverError(
        state, "Concurrency schedule has no feasible choice.");
    return;
  }

  std::vector<ExecutionState *> branches;
  if (conditions.size() == 1) {
    executor.addConstraint(state, conditions.front());
    branches.push_back(&state);
  } else {
    executor.branch(state, conditions, branches, BranchType::Schedule);
  }

  for (std::size_t index = 0; index < branches.size(); ++index) {
    ExecutionState *branch = branches[index];
    if (!branch)
      continue;
    if (!branch->concurrency.scheduleThread(
            feasibleCandidates[index], runnable->getZExtValue(),
            maxSwitches->getZExtValue(), error)) {
      executor.terminateStateOnProgramError(
          *branch, "concurrency model error: " + error,
          StateTerminationType::Model);
      continue;
    }
    executor.bindLocal(target, *branch,
                       ConstantExpr::create(feasibleCandidates[index],
                                            Expr::Int64));
  }
}

/* Native pthread model ----------------------------------------------------*/

bool SpecialFunctionHandler::enterHarnessScheduling(ExecutionState &state,
                                                    const char *name) {
  std::string error;
  if (!state.concurrency.enterHarnessMode(name, error)) {
    reportModelError(state, error);
    return false;
  }
  return true;
}

bool SpecialFunctionHandler::enterNativeThreads(ExecutionState &state,
                                                const char *name,
                                                bool preserveBusyTrylock) {
  std::string error;
  if (!state.concurrency.enterNativeMode(name, error)) {
    reportModelError(state, error);
    return false;
  }
  if (!preserveBusyTrylock)
    state.lastBusyTrylock = nullptr;
  return true;
}

void SpecialFunctionHandler::reportModelError(ExecutionState &state,
                                              const std::string &error) {
  executor.terminateStateOnProgramError(state,
                                        "concurrency model error: " + error,
                                        StateTerminationType::Model);
}

bool SpecialFunctionHandler::getConcreteThreadId(ExecutionState &state,
                                                 ref<Expr> argument,
                                                 const char *name,
                                                 std::uint64_t &thread) {
  ref<Expr> value = executor.toUnique(state, argument);
  auto *constant = dyn_cast<ConstantExpr>(value);
  if (!constant) {
    executor.terminateStateOnUserError(
        state, std::string(name) + " requires a concrete thread identifier");
    return false;
  }
  thread = constant->getZExtValue();
  return true;
}

bool SpecialFunctionHandler::writeConcreteWord(ExecutionState &state,
                                               ref<Expr> addressExpr,
                                               ref<Expr> value,
                                               const char *name) {
  ref<Expr> address = executor.toUnique(state, addressExpr);
  auto *constant = dyn_cast<ConstantExpr>(address);
  if (!constant) {
    executor.terminateStateOnUserError(
        state, std::string(name) + " requires a concrete output pointer");
    return false;
  }
  const unsigned bytes = Expr::getMinBytesForWidth(value->getWidth());
  ObjectPair op;
  if (!state.addressSpace.resolveOne(constant, op) ||
      !op.first->getBoundsCheckPointer(constant, bytes)->isTrue()) {
    executor.terminateStateOnProgramError(
        state, std::string(name) + ": memory error",
        StateTerminationType::Ptr, executor.getAddressInfo(state, address));
    return false;
  }
  if (op.second->readOnly) {
    executor.terminateStateOnProgramError(
        state, std::string(name) + ": memory error: object read only",
        StateTerminationType::ReadOnly);
    return false;
  }
  ObjectState *wos = state.addressSpace.getWriteable(op.first, op.second);
  wos->write(constant->getZExtValue() - op.first->address, value);
  return true;
}

void SpecialFunctionHandler::blockAndReschedule(ExecutionState &state) {
  /* The call instruction is re-executed when the thread is next selected,
   * so the handler re-evaluates the condition it blocked on. */
  state.pc = state.prevPC;
  executor.scheduleNativeThreads(state);
}

void SpecialFunctionHandler::handleConcurrencyYield(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  assert(arguments.empty() && "invalid arguments to klee_concurrency_yield");
  /* Harness-driven states own their scheduling; a yield there is inert so
   * automatically instrumented code can run under either interface. */
  if (!state.concurrency.inNativeMode())
    return;
  executor.scheduleNativeThreads(state, Executor::NativeBoundary::Preemption);
}

void SpecialFunctionHandler::handleSchedYield(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  assert(arguments.empty() && "invalid arguments to sched_yield");
  if (!enterNativeThreads(state, "sched_yield"))
    return;
  executor.bindLocal(target, state, ConstantExpr::create(0, Expr::Int32));
  /* The caller asked to be descheduled: it is not offered again while
   * another thread is runnable (yield fairness), so spin-waits on another
   * thread's progress terminate. */
  executor.scheduleNativeThreads(state, Executor::NativeBoundary::Yield);
}

void SpecialFunctionHandler::handlePthreadCreate(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  if (arguments.size() != 4) {
    executor.terminateStateOnUserError(
        state, "invalid number of arguments to pthread_create");
    return;
  }
  if (!enterNativeThreads(state, "pthread_create"))
    return;
  ref<Expr> attr = executor.toUnique(state, arguments[1]);
  if (!attr->isZero()) {
    /* Detach state, stack size, and scheduling attributes are not modeled;
     * silently treating a detached thread as joinable would accept an
     * invalid pthread_join, so fail closed. */
    reportModelError(state, "pthread_create: thread attributes are not "
                            "modeled; pass a null attribute");
    return;
  }
  ref<Expr> startExpr = executor.toUnique(state, arguments[2]);
  auto *startAddress = dyn_cast<ConstantExpr>(startExpr);
  if (!startAddress) {
    executor.terminateStateOnUserError(
        state, "pthread_create requires a concrete start routine");
    return;
  }
  auto it = executor.legalFunctions.find(startAddress->getZExtValue());
  if (it == executor.legalFunctions.end()) {
    executor.terminateStateOnExecError(
        state, "pthread_create: invalid start routine pointer");
    return;
  }
  std::uint64_t thread = 0;
  if (!executor.startNativeThread(state, it->second, arguments[3], thread))
    return;
  if (!writeConcreteWord(state, arguments[0],
                         ConstantExpr::create(thread, Expr::Int64),
                         "pthread_create"))
    return;
  executor.bindLocal(target, state, ConstantExpr::create(0, Expr::Int32));
  executor.scheduleNativeThreads(state);
}

void SpecialFunctionHandler::handlePthreadJoin(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  if (arguments.size() != 2) {
    executor.terminateStateOnUserError(
        state, "invalid number of arguments to pthread_join");
    return;
  }
  if (!enterNativeThreads(state, "pthread_join"))
    return;
  std::uint64_t thread = 0;
  if (!getConcreteThreadId(state, arguments[0], "pthread_join", thread))
    return;
  const std::uint64_t self = state.runningThread;
  std::string error;
  if (thread == self) {
    reportModelError(state, "pthread_join on the calling thread");
    return;
  }
  if (!state.concurrency.threadExists(thread) ||
      !state.hasThreadContext(thread)) {
    reportModelError(state, "pthread_join on an unknown thread");
    return;
  }
  ThreadContext &context = state.threadContext(thread);
  if (context.detached) {
    reportModelError(state, "pthread_join on a detached thread");
    return;
  }
  if (state.concurrency.threadJoined(thread)) {
    reportModelError(state, "pthread_join on a thread that was already joined");
    return;
  }
  if (!state.concurrency.threadFinished(thread)) {
    if (!state.concurrency.blockOnJoin(self, thread, error)) {
      reportModelError(state, error);
      return;
    }
    blockAndReschedule(state);
    return;
  }
  if (!state.concurrency.joinThread(thread, error)) {
    reportModelError(state, error);
    return;
  }
  ref<Expr> retval = executor.toUnique(state, arguments[1]);
  if (!retval->isZero()) {
    ref<Expr> result = context.result;
    if (result.isNull())
      result = ConstantExpr::create(0, Context::get().getPointerWidth());
    if (!writeConcreteWord(state, arguments[1], result, "pthread_join"))
      return;
  }
  executor.bindLocal(target, state, ConstantExpr::create(0, Expr::Int32));
  executor.scheduleNativeThreads(state);
}

void SpecialFunctionHandler::handlePthreadExit(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  if (arguments.size() != 1) {
    executor.terminateStateOnUserError(
        state, "invalid number of arguments to pthread_exit");
    return;
  }
  if (!enterNativeThreads(state, "pthread_exit"))
    return;
  executor.finishNativeThread(state, arguments[0]);
}

void SpecialFunctionHandler::handlePthreadSelf(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  assert(arguments.empty() && "invalid arguments to pthread_self");
  if (!enterNativeThreads(state, "pthread_self"))
    return;
  /* An identity query touches no shared state and commutes with every
   * other thread's step, so it is a mode gate but not a scheduling
   * boundary. */
  executor.bindLocal(target, state,
                     ConstantExpr::create(state.runningThread, Expr::Int64));
}

void SpecialFunctionHandler::handlePthreadEqual(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  if (arguments.size() != 2) {
    executor.terminateStateOnUserError(
        state, "invalid number of arguments to pthread_equal");
    return;
  }
  if (!enterNativeThreads(state, "pthread_equal"))
    return;
  executor.bindLocal(target, state,
                     ZExtExpr::create(EqExpr::create(arguments[0], arguments[1]),
                                      Expr::Int32));
}

void SpecialFunctionHandler::handlePthreadDetach(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  if (arguments.size() != 1) {
    executor.terminateStateOnUserError(
        state, "invalid number of arguments to pthread_detach");
    return;
  }
  if (!enterNativeThreads(state, "pthread_detach"))
    return;
  std::uint64_t thread = 0;
  if (!getConcreteThreadId(state, arguments[0], "pthread_detach", thread))
    return;
  if (!state.concurrency.threadExists(thread) ||
      !state.hasThreadContext(thread)) {
    reportModelError(state, "pthread_detach on an unknown thread");
    return;
  }
  state.threadContext(thread).detached = true;
  executor.bindLocal(target, state, ConstantExpr::create(0, Expr::Int32));
  executor.scheduleNativeThreads(state);
}

void SpecialFunctionHandler::handlePthreadMutexInit(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  if (arguments.size() != 2) {
    executor.terminateStateOnUserError(
        state, "invalid number of arguments to pthread_mutex_init");
    return;
  }
  if (!enterNativeThreads(state, "pthread_mutex_init"))
    return;
  std::uint64_t object = 0, offset = 0;
  if (!getConcreteConcurrencyLocation(state, arguments[0],
                                      "pthread_mutex_init", object, offset))
    return;
  ref<Expr> attr = executor.toUnique(state, arguments[1]);
  if (!attr->isZero()) {
    /* Only the default (non-recursive, non-errorcheck) type is modeled; a
     * recursive mutex treated as non-recursive would report a legitimate
     * relock as a model error, so fail closed instead. */
    reportModelError(state, "pthread_mutex_init: mutex attributes are not "
                            "modeled; pass a null attribute");
    return;
  }
  std::string error;
  if (!state.concurrency.initializeMutex(object, offset, error)) {
    reportModelError(state, error);
    return;
  }
  executor.bindLocal(target, state, ConstantExpr::create(0, Expr::Int32));
  executor.scheduleNativeThreads(state);
}

void SpecialFunctionHandler::handlePthreadMutexDestroy(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  if (arguments.size() != 1) {
    executor.terminateStateOnUserError(
        state, "invalid number of arguments to pthread_mutex_destroy");
    return;
  }
  if (!enterNativeThreads(state, "pthread_mutex_destroy"))
    return;
  std::uint64_t object = 0, offset = 0;
  if (!getConcreteConcurrencyLocation(state, arguments[0],
                                      "pthread_mutex_destroy", object, offset))
    return;
  if (state.concurrency.mutexHasWaiters(object, offset)) {
    reportModelError(state, "pthread_mutex_destroy on a mutex with waiters");
    return;
  }
  std::string error;
  if (!state.concurrency.destroyMutex(object, offset, error)) {
    reportModelError(state, error);
    return;
  }
  executor.bindLocal(target, state, ConstantExpr::create(0, Expr::Int32));
  executor.scheduleNativeThreads(state);
}

void SpecialFunctionHandler::handlePthreadMutexLock(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  if (arguments.size() != 1) {
    executor.terminateStateOnUserError(
        state, "invalid number of arguments to pthread_mutex_lock");
    return;
  }
  if (!enterNativeThreads(state, "pthread_mutex_lock"))
    return;
  std::uint64_t object = 0, offset = 0, owner = 0;
  if (!getConcreteConcurrencyLocation(state, arguments[0],
                                      "pthread_mutex_lock", object, offset))
    return;
  const std::uint64_t self = state.runningThread;
  std::string error;
  if (state.concurrency.mutexOwner(object, offset, owner)) {
    if (owner == self) {
      reportModelError(state, "pthread_mutex_lock: the calling thread already "
                              "owns this non-recursive mutex");
      return;
    }
    if (!state.concurrency.blockThread(
            self, static_cast<std::uint32_t>(ConcurrencyBlockKind::Mutex),
            object, offset, error)) {
      reportModelError(state, error);
      return;
    }
    blockAndReschedule(state);
    return;
  }
  if (!state.concurrency.mutexLock(object, offset, error)) {
    reportModelError(state, error);
    return;
  }
  executor.bindLocal(target, state, ConstantExpr::create(0, Expr::Int32));
  executor.scheduleNativeThreads(state);
}

void SpecialFunctionHandler::handlePthreadMutexTrylock(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  if (arguments.size() != 1) {
    executor.terminateStateOnUserError(
        state, "invalid number of arguments to pthread_mutex_trylock");
    return;
  }
  if (!enterNativeThreads(state, "pthread_mutex_trylock", true))
    return;
  std::uint64_t object = 0, offset = 0, owner = 0;
  if (!getConcreteConcurrencyLocation(state, arguments[0],
                                      "pthread_mutex_trylock", object,
                                      offset))
    return;
  std::string error;
  if (state.concurrency.mutexOwner(object, offset, owner)) {
    /* EBUSY is nonblocking: the first failure at a call site must preserve
     * the legal immediate caller continuation. If that continuation loops
     * back to the same site without another modeled pthread operation, the
     * repeated failure requests fairness so a runnable owner can progress. */
    const bool repeated = state.lastBusyTrylock == target;
    state.lastBusyTrylock = target;
    executor.bindLocal(target, state, ConstantExpr::create(16, Expr::Int32));
    executor.scheduleNativeThreads(
        state, repeated ? Executor::NativeBoundary::Yield
                        : Executor::NativeBoundary::Preemption);
    return;
  }
  state.lastBusyTrylock = nullptr;
  if (!state.concurrency.mutexLock(object, offset, error)) {
    reportModelError(state, error);
    return;
  }
  executor.bindLocal(target, state, ConstantExpr::create(0, Expr::Int32));
  executor.scheduleNativeThreads(state);
}

void SpecialFunctionHandler::handlePthreadMutexUnlock(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  if (arguments.size() != 1) {
    executor.terminateStateOnUserError(
        state, "invalid number of arguments to pthread_mutex_unlock");
    return;
  }
  if (!enterNativeThreads(state, "pthread_mutex_unlock"))
    return;
  std::uint64_t object = 0, offset = 0;
  if (!getConcreteConcurrencyLocation(state, arguments[0],
                                      "pthread_mutex_unlock", object, offset))
    return;
  std::string error;
  if (!state.concurrency.mutexUnlock(object, offset, error)) {
    reportModelError(state, error);
    return;
  }
  /* Every waiter becomes runnable and re-executes its lock; the scheduler
   * decides which one acquires first. */
  std::vector<std::uint64_t> waiters;
  state.concurrency.collectBlocked(ConcurrencyBlockKind::Mutex, object,
                                   offset, waiters);
  for (std::uint64_t waiter : waiters) {
    if (!state.concurrency.unblockThread(waiter, error)) {
      reportModelError(state, error);
      return;
    }
  }
  executor.bindLocal(target, state, ConstantExpr::create(0, Expr::Int32));
  executor.scheduleNativeThreads(state);
}

void SpecialFunctionHandler::handlePthreadCondInit(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  if (arguments.size() != 2) {
    executor.terminateStateOnUserError(
        state, "invalid number of arguments to pthread_cond_init");
    return;
  }
  if (!enterNativeThreads(state, "pthread_cond_init"))
    return;
  std::uint64_t object = 0, offset = 0;
  if (!getConcreteConcurrencyLocation(state, arguments[0],
                                      "pthread_cond_init", object, offset))
    return;
  ref<Expr> attr = executor.toUnique(state, arguments[1]);
  if (!attr->isZero()) {
    reportModelError(state, "pthread_cond_init: condition attributes are "
                            "not modeled; pass a null attribute");
    return;
  }
  executor.bindLocal(target, state, ConstantExpr::create(0, Expr::Int32));
  executor.scheduleNativeThreads(state);
}

void SpecialFunctionHandler::handlePthreadCondDestroy(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  if (arguments.size() != 1) {
    executor.terminateStateOnUserError(
        state, "invalid number of arguments to pthread_cond_destroy");
    return;
  }
  if (!enterNativeThreads(state, "pthread_cond_destroy"))
    return;
  std::uint64_t object = 0, offset = 0;
  if (!getConcreteConcurrencyLocation(state, arguments[0],
                                      "pthread_cond_destroy", object, offset))
    return;
  std::vector<std::uint64_t> waiters;
  state.concurrency.collectBlocked(ConcurrencyBlockKind::Cond, object, offset,
                                   waiters);
  if (!waiters.empty()) {
    reportModelError(state,
                     "pthread_cond_destroy on a condition with waiters");
    return;
  }
  executor.bindLocal(target, state, ConstantExpr::create(0, Expr::Int32));
  executor.scheduleNativeThreads(state);
}

void SpecialFunctionHandler::conditionWait(
    ExecutionState &state, KInstruction *target, const char *name,
    std::uint64_t condObject, std::uint64_t condOffset,
    std::uint64_t mutexObject, std::uint64_t mutexOffset, bool bindResult) {
  const std::uint64_t self = state.runningThread;
  ThreadContext &context = state.threadContext(self);
  std::string error;
  std::uint64_t owner = 0;
  if (context.condPhase == 1) {
    /* Woken: reacquire the mutex, blocking on it if necessary. */
    if (state.concurrency.mutexOwner(mutexObject, mutexOffset, owner)) {
      if (owner == self) {
        reportModelError(state, std::string(name) +
                                    ": woken waiter already owns the mutex");
        return;
      }
      if (!state.concurrency.blockThread(
              self, static_cast<std::uint32_t>(ConcurrencyBlockKind::Mutex),
              mutexObject, mutexOffset, error)) {
        reportModelError(state, error);
        return;
      }
      blockAndReschedule(state);
      return;
    }
    if (!state.concurrency.mutexLock(mutexObject, mutexOffset, error)) {
      reportModelError(state, error);
      return;
    }
    context.condPhase = 0;
    if (bindResult)
      executor.bindLocal(target, state, ConstantExpr::create(0, Expr::Int32));
    executor.scheduleNativeThreads(state);
    return;
  }
  if (!state.concurrency.mutexOwner(mutexObject, mutexOffset, owner) ||
      owner != self) {
    reportModelError(state, std::string(name) +
                                " without owning the associated mutex");
    return;
  }
  if (!state.concurrency.mutexUnlock(mutexObject, mutexOffset, error)) {
    reportModelError(state, error);
    return;
  }
  std::vector<std::uint64_t> waiters;
  state.concurrency.collectBlocked(ConcurrencyBlockKind::Mutex, mutexObject,
                                   mutexOffset, waiters);
  for (std::uint64_t waiter : waiters) {
    if (!state.concurrency.unblockThread(waiter, error)) {
      reportModelError(state, error);
      return;
    }
  }
  if (!state.concurrency.blockOnCondition(self, condObject, condOffset,
                                          mutexObject, mutexOffset, error)) {
    reportModelError(state, error);
    return;
  }
  blockAndReschedule(state);
}

void SpecialFunctionHandler::conditionSignal(ExecutionState &state,
                                             KInstruction *target,
                                             std::uint64_t object,
                                             std::uint64_t offset,
                                             bool bindResult,
                                             bool mergeNotifierClock) {
  std::vector<std::uint64_t> waiters;
  state.concurrency.collectBlocked(ConcurrencyBlockKind::Cond, object, offset,
                                   waiters);
  if (bindResult)
    executor.bindLocal(target, state, ConstantExpr::create(0, Expr::Int32));
  if (waiters.empty()) {
    executor.scheduleNativeThreads(state);
    return;
  }
  /* POSIX leaves the woken waiter unspecified: fork over the choice. */
  std::vector<ExecutionState *> branches;
  if (waiters.size() == 1) {
    branches.push_back(&state);
  } else if (!executor.branchOnScheduleChoice(state, waiters.size(),
                                              branches)) {
    return;
  }
  for (std::size_t index = 0; index < branches.size(); ++index) {
    ExecutionState *branch = branches[index];
    if (!branch)
      continue;
    std::string error;
    std::uint64_t mutexObject = 0, mutexOffset = 0;
    if (!branch->concurrency.wakeConditionWaiter(waiters[index], mutexObject,
                                                 mutexOffset,
                                                 mergeNotifierClock, error)) {
      reportModelError(*branch, error);
      continue;
    }
    branch->threadContext(waiters[index]).condPhase = 1;
    executor.scheduleNativeThreads(*branch);
  }
}

void SpecialFunctionHandler::conditionBroadcast(ExecutionState &state,
                                                KInstruction *target,
                                                std::uint64_t object,
                                                std::uint64_t offset,
                                                bool bindResult,
                                                bool mergeNotifierClock) {
  std::vector<std::uint64_t> waiters;
  state.concurrency.collectBlocked(ConcurrencyBlockKind::Cond, object, offset,
                                   waiters);
  std::string error;
  for (std::uint64_t waiter : waiters) {
    std::uint64_t mutexObject = 0, mutexOffset = 0;
    if (!state.concurrency.wakeConditionWaiter(waiter, mutexObject,
                                               mutexOffset,
                                               mergeNotifierClock, error)) {
      reportModelError(state, error);
      return;
    }
    state.threadContext(waiter).condPhase = 1;
  }
  if (bindResult)
    executor.bindLocal(target, state, ConstantExpr::create(0, Expr::Int32));
  executor.scheduleNativeThreads(state);
}

void SpecialFunctionHandler::handlePthreadCondWait(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  if (arguments.size() != 2) {
    executor.terminateStateOnUserError(
        state, "invalid number of arguments to pthread_cond_wait");
    return;
  }
  if (!enterNativeThreads(state, "pthread_cond_wait"))
    return;
  std::uint64_t condObject = 0, condOffset = 0;
  std::uint64_t mutexObject = 0, mutexOffset = 0;
  const bool reacquiring =
      state.threadContext(state.runningThread).condPhase == 1;
  if ((!reacquiring &&
       !getConcreteConcurrencyLocation(state, arguments[0],
                                       "pthread_cond_wait", condObject,
                                       condOffset)) ||
      !getConcreteConcurrencyLocation(state, arguments[1],
                                      "pthread_cond_wait", mutexObject,
                                      mutexOffset))
    return;
  conditionWait(state, target, "pthread_cond_wait", condObject, condOffset,
                mutexObject, mutexOffset, true);
}

void SpecialFunctionHandler::handlePthreadCondSignal(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  if (arguments.size() != 1) {
    executor.terminateStateOnUserError(
        state, "invalid number of arguments to pthread_cond_signal");
    return;
  }
  if (!enterNativeThreads(state, "pthread_cond_signal"))
    return;
  std::uint64_t object = 0, offset = 0;
  if (!getConcreteConcurrencyLocation(state, arguments[0],
                                      "pthread_cond_signal", object, offset))
    return;
  conditionSignal(state, target, object, offset, true, true);
}

void SpecialFunctionHandler::handlePthreadCondBroadcast(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  if (arguments.size() != 1) {
    executor.terminateStateOnUserError(
        state, "invalid number of arguments to pthread_cond_broadcast");
    return;
  }
  if (!enterNativeThreads(state, "pthread_cond_broadcast"))
    return;
  std::uint64_t object = 0, offset = 0;
  if (!getConcreteConcurrencyLocation(state, arguments[0],
                                      "pthread_cond_broadcast", object,
                                      offset))
    return;
  conditionBroadcast(state, target, object, offset, true, true);
}

/* Trace condition operations emitted by the std::condition_variable model.
 * They share the pthread condition protocol and the traced mutex table, so a
 * wait releases the mutex the source instrumentation locked, blocks until a
 * notification, and reacquires it. A wait outside the native pthread model
 * could never be woken and is a model error; a notification there finds no
 * waiter and is a no-op. */
void SpecialFunctionHandler::handleConcurrencyCondWait(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  assert(arguments.size() == 2 &&
         "invalid number of arguments to klee_concurrency_cond_wait");
  if (!state.concurrency.inNativeMode()) {
    reportModelError(state, "klee_concurrency_cond_wait requires the native "
                            "pthread model");
    return;
  }
  std::uint64_t condObject = 0, condOffset = 0;
  std::uint64_t mutexObject = 0, mutexOffset = 0;
  const bool reacquiring =
      state.threadContext(state.runningThread).condPhase == 1;
  if ((!reacquiring &&
       !getConcreteConcurrencyLocation(state, arguments[0],
                                       "klee_concurrency_cond_wait",
                                       condObject, condOffset)) ||
      !getConcreteConcurrencyLocation(state, arguments[1],
                                      "klee_concurrency_cond_wait",
                                      mutexObject, mutexOffset))
    return;
  state.lastBusyTrylock = nullptr;
  conditionWait(state, target, "klee_concurrency_cond_wait", condObject,
                condOffset, mutexObject, mutexOffset, false);
}

void SpecialFunctionHandler::handleConcurrencyCondSignal(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  assert(arguments.size() == 1 &&
         "invalid number of arguments to klee_concurrency_cond_signal");
  std::uint64_t object = 0, offset = 0;
  if (!getConcreteConcurrencyLocation(state, arguments[0],
                                      "klee_concurrency_cond_signal", object,
                                      offset))
    return;
  if (!state.concurrency.inNativeMode())
    return;
  state.lastBusyTrylock = nullptr;
  conditionSignal(state, target, object, offset, false, false);
}

void SpecialFunctionHandler::handleConcurrencyCondBroadcast(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  assert(arguments.size() == 1 &&
         "invalid number of arguments to klee_concurrency_cond_broadcast");
  std::uint64_t object = 0, offset = 0;
  if (!getConcreteConcurrencyLocation(state, arguments[0],
                                      "klee_concurrency_cond_broadcast",
                                      object, offset))
    return;
  if (!state.concurrency.inNativeMode())
    return;
  state.lastBusyTrylock = nullptr;
  conditionBroadcast(state, target, object, offset, false, false);
}

void SpecialFunctionHandler::handleGetValue(ExecutionState &state,
                                            KInstruction *target,
                                            std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 &&
         "invalid number of arguments to klee_get_value");

  executor.executeGetValue(state, arguments[0], target);
}

void SpecialFunctionHandler::handleDefineFixedObject(ExecutionState &state,
                                                     KInstruction *target,
                                                     std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==2 &&
         "invalid number of arguments to klee_define_fixed_object");
  assert(isa<ConstantExpr>(arguments[0]) &&
         "expect constant address argument to klee_define_fixed_object");
  assert(isa<ConstantExpr>(arguments[1]) &&
         "expect constant size argument to klee_define_fixed_object");
  
  uint64_t address = cast<ConstantExpr>(arguments[0])->getZExtValue();
  uint64_t size = cast<ConstantExpr>(arguments[1])->getZExtValue();
  MemoryObject *mo = executor.memory->allocateFixed(address, size, state.prevPC->inst);
  executor.bindObjectInState(state, mo, false);
  mo->isUserSpecified = true; // XXX hack;
}

void SpecialFunctionHandler::handleMakeSymbolic(ExecutionState &state,
                                                KInstruction *target,
                                                std::vector<ref<Expr> > &arguments) {
  std::string name;

  if (arguments.size() != 3) {
    executor.terminateStateOnUserError(state,
        "Incorrect number of arguments to klee_make_symbolic(void*, size_t, char*)");
    return;
  }

  name = arguments[2]->isZero() ? "" : readStringAtAddress(state, arguments[2]);

  if (name.length() == 0) {
    name = "unnamed";
    klee_warning("klee_make_symbolic: renamed empty name to \"unnamed\"");
  }

  Executor::ExactResolutionList rl;
  executor.resolveExact(state, arguments[0], rl, "make_symbolic");
  
  for (Executor::ExactResolutionList::iterator it = rl.begin(), 
         ie = rl.end(); it != ie; ++it) {
    const MemoryObject *mo = it->first.first;
    mo->setName(name);
    
    const ObjectState *old = it->first.second;
    ExecutionState *s = it->second;
    
    if (old->readOnly) {
      executor.terminateStateOnUserError(*s, "cannot make readonly object symbolic");
      return;
    }

    // Prefix symbolication: a concrete size strictly smaller than the
    // object size symbolicates only the first `size` bytes (bytes beyond
    // keep their current contents). size == mo->size keeps the original
    // whole-object path (also when the size is symbolic but provably
    // equal). Larger sizes remain a user error.
    if (ConstantExpr *CE = dyn_cast<ConstantExpr>(arguments[1])) {
      uint64_t requested = CE->getZExtValue();
      if (requested < mo->size) {
        executor.executeMakeSymbolic(*s, mo, name, requested);
        continue;
      }
    }

    // FIXME: Type coercion should be done consistently somewhere.
    bool res;
    bool success __attribute__((unused)) = executor.solver->mustBeTrue(
        s->constraints,
        EqExpr::create(
            ZExtExpr::create(arguments[1], Context::get().getPointerWidth()),
            mo->getSizeExpr()),
        res, s->queryMetaData);
    assert(success && "FIXME: Unhandled solver failure");

    if (res) {
      executor.executeMakeSymbolic(*s, mo, name);
    } else {
      executor.terminateStateOnUserError(*s, "Wrong size given to klee_make_symbolic");
    }
  }
}

void SpecialFunctionHandler::handleMarkInteresting(
    ExecutionState &state, KInstruction *target,
    std::vector<ref<Expr>> &arguments) {
  assert(arguments.empty() &&
         "invalid number of arguments to klee_mark_interesting");
  (void) target;
  // Repeated calls before the next fork coalesce into one preference lease.
  state.interesting = true;
}

void SpecialFunctionHandler::handleMarkGlobal(ExecutionState &state,
                                              KInstruction *target,
                                              std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 &&
         "invalid number of arguments to klee_mark_global");  

  Executor::ExactResolutionList rl;
  executor.resolveExact(state, arguments[0], rl, "mark_global");
  
  for (Executor::ExactResolutionList::iterator it = rl.begin(), 
         ie = rl.end(); it != ie; ++it) {
    const MemoryObject *mo = it->first.first;
    assert(!mo->isLocal);
    mo->isGlobal = true;
  }
}
