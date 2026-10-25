//===-- Concurrency.h ------------------------------------------*- C++ -*-===//
//
// Bounded logical-thread happens-before model for targeted KLEE harnesses.
// This is not an operating-system thread runtime: a harness supplies an
// explicit interleaving by selecting a logical thread before each event.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_CONCURRENCY_H
#define KLEE_CONCURRENCY_H

#include <cstdint>
#include <map>
#include <set>
#include <string>
#include <vector>

namespace klee {

enum class ConcurrencyAccessResult {
  Ok,
  Race,
  Error,
};

enum class ConcurrencyTransitionKind : std::uint32_t {
  Opaque = 0,
  Local = 1,
  Read = 2,
  Write = 3,
  Mutex = 4,
};

enum class ConcurrencyBlockKind : std::uint32_t {
  /* The harness asserts the thread is blocked for a reason the engine cannot
   * verify (condition wait, join on an unfinished thread, ...). */
  Harness = 0,
  /* The thread waits for a modeled mutex that another thread owns. */
  Mutex = 1,
  /* Native-thread mode only: the thread waits in pthread_join for an
   * unfinished thread. */
  Join = 2,
  /* Native-thread mode only: the thread waits in pthread_cond_wait and must
   * reacquire the recorded mutex once it is woken. */
  Cond = 3,
};

struct ConcurrencyRace {
  std::uint64_t currentThread = 0;
  std::uint64_t currentSite = 0;
  bool currentWrite = false;
  std::uint64_t previousThread = 0;
  std::uint64_t previousSite = 0;
  bool previousWrite = false;
  std::uint64_t address = 0;
  std::uint64_t size = 0;
};

class ConcurrencyState {
  using VectorClock = std::map<std::uint64_t, std::uint64_t>;

  struct ThreadState {
    VectorClock clock;
    bool finished = false;
    bool joined = false;
  };

  struct Access {
    std::uint64_t thread = 0;
    std::uint64_t site = 0;
    std::uint64_t object = 0;
    std::uint64_t begin = 0;
    std::uint64_t end = 0;
    bool write = false;
    VectorClock clock;
  };

  struct MemoryLocation {
    std::uint64_t object = 0;
    std::uint64_t offset = 0;

    bool operator<(const MemoryLocation &other) const {
      return object < other.object ||
             (object == other.object && offset < other.offset);
    }
  };

  struct BlockReason {
    ConcurrencyBlockKind kind = ConcurrencyBlockKind::Harness;
    /* Mutex: the awaited mutex. Cond: the mutex released by the wait. */
    MemoryLocation mutex;
    /* Cond: the condition variable. */
    MemoryLocation condition;
    /* Join: the awaited thread. */
    std::uint64_t target = 0;
  };

  struct TransitionDeclaration {
    ConcurrencyTransitionKind kind = ConcurrencyTransitionKind::Opaque;
    std::uint64_t object = 0;
    std::uint64_t begin = 0;
    std::uint64_t end = 0;
    bool active = false;
    bool observed = false;
  };

  std::uint64_t activeThread = 0;
  std::map<std::uint64_t, ThreadState> threads;
  std::map<MemoryLocation, VectorClock> mutexReleaseClocks;
  std::map<MemoryLocation, std::uint64_t> mutexOwners;
  /* Unknown mutex locations are accepted as static initializers on first
   * use. Once a native pthread lifecycle operation touches a location, keep
   * enough state to reject use-after-destroy and to give each successful
   * destroy/init cycle a fresh synchronization generation. */
  std::set<MemoryLocation> initializedMutexes;
  std::set<MemoryLocation> destroyedMutexes;
  std::vector<Access> accesses;
  std::map<std::uint64_t, TransitionDeclaration> declarations;
  std::map<std::uint64_t, BlockReason> blockedThreads;
  bool declarationsEnabled = false;
  bool scheduleStarted = false;
  /* Exactly one scheduling interface may drive a state: the harness driver
   * intrinsics (klee_concurrency_create_thread, _set_thread, _schedule, ...)
   * or the native pthread model whose contexts the engine owns. Trace
   * read/write/mutex operations are observations shared by both modes. */
  bool harnessMode = false;
  bool nativeMode = false;
  std::uint64_t nextNativeThread = 1;
  /* Native mode yield fairness. A thread that calls sched_yield, or repeats
   * a pthread_mutex_trylock call site after one immediate EBUSY continuation,
   * asked to be descheduled: it is not offered while another thread is
   * runnable, and switching away from it is free. */
  std::uint64_t yieldedMask = 0;
  /* A completed LOCAL transition continues to guard enabledness updates until
   * the next scheduler selection. This prevents a harness from redeclaring
   * the active thread (which consumes its declaration) and then changing
   * another thread's runnable state outside the checked LOCAL window. */
  bool completedLocalGuardsEnabledness = false;
  /* Preemption accounting. The anchor is the thread whose continuation is
   * free. A selection is charged only when the anchor is still offered as
   * runnable and a different thread's non-LOCAL transition is selected.
   * Declared LOCAL transitions neither charge nor move the anchor. */
  bool anchorValid = false;
  std::uint64_t anchorThread = 0;
  std::uint64_t contextSwitches = 0;
  std::uint64_t scheduleMaxSwitches = 0;

  ThreadState *getActiveThread(std::string &error);
  static void tick(std::uint64_t thread, VectorClock &clock);
  static void merge(VectorClock &destination, const VectorClock &source);
  static bool happensBefore(const VectorClock &before,
                            const VectorClock &after);
  bool completeActiveTransition(std::string &error);
  bool validateDeclaredAccess(std::uint64_t object, std::uint64_t offset,
                              std::uint64_t size, bool write,
                              std::string &error);
  bool validateDeclaredMutex(std::uint64_t object, std::uint64_t offset,
                             std::string &error);
  bool validateDeclaredOpaqueOperation(const char *operation,
                                       std::string &error);
  bool isLocalTransition(std::uint64_t thread) const;
  bool localTransitionGuardsEnabledness() const;
  bool anchorPreemptible(std::uint64_t runnableMask) const;

public:
  ConcurrencyState();

  bool createThread(std::uint64_t thread, std::string &error);
  bool declareTransition(std::uint64_t thread, std::uint32_t kind,
                         std::uint64_t object, std::uint64_t offset,
                         std::uint64_t size,
                         std::string &error);
  bool setThread(std::uint64_t thread, std::string &error);
  bool blockThread(std::uint64_t thread, std::uint32_t kind,
                   std::uint64_t object, std::uint64_t offset,
                   std::string &error);
  bool unblockThread(std::uint64_t thread, std::string &error);
  /* Terminal boundary: complete and consume the active declaration, as the
   * next scheduling decision would, so a missing expected operation is
   * reported before any terminal oracle such as deadlock. */
  bool completePendingTransition(std::string &error);
  bool finishThread(std::string &error);
  bool joinThread(std::uint64_t thread, std::string &error);
  bool initializeMutex(std::uint64_t object, std::uint64_t offset,
                       std::string &error);
  bool destroyMutex(std::uint64_t object, std::uint64_t offset,
                    std::string &error);
  bool mutexLock(std::uint64_t object, std::uint64_t offset,
                 std::string &error);
  bool mutexUnlock(std::uint64_t object, std::uint64_t offset,
                   std::string &error);
  /* On success, verified is true when every blocked thread waits on a mutex
   * currently held by another blocked thread; false when at least one
   * reason is harness-declared and therefore not engine-verified. */
  bool validateDeadlock(std::uint64_t blockedMask, bool &verified,
                        std::string &error) const;

  /* Native pthread mode. The engine owns thread contexts and derives the
   * runnable set itself; harness scheduling-driver intrinsics are rejected
   * once a state has entered this mode, and vice versa. Trace read/write and
   * mutex operations remain valid in either mode. */
  bool enterHarnessMode(const char *operation, std::string &error);
  bool enterNativeMode(const char *operation, std::string &error);
  bool inNativeMode() const { return nativeMode; }
  bool allocateNativeThread(std::uint64_t &thread, std::string &error);
  void markYielded(std::uint64_t thread);
  void clearYielded() { yieldedMask = 0; }
  std::uint64_t yieldedThreads() const { return yieldedMask; }
  /* The current boundary is voluntary. Invalidating the anchor makes a
   * switch away free even when an all-yielded round re-enables every thread. */
  void waiveAnchorPreemption() { anchorValid = false; }
  /* Harness mode: start a new scheduling episode. After scheduling has begun,
   * exactly one logical coordinator must remain unfinished and runnable; it
   * becomes active and acquires every finished thread's clock (the harness
   * observed their completion). The preemption accounting and transition
   * declarations are cleared, while access history, mutex state, and finished
   * thread identities are kept. */
  bool resetScheduler(std::string &error);
  std::uint64_t activeThreadId() const { return activeThread; }
  bool threadExists(std::uint64_t thread) const;
  bool threadFinished(std::uint64_t thread) const;
  bool threadBlocked(std::uint64_t thread) const;
  bool threadJoined(std::uint64_t thread) const;
  /* Bits of unfinished threads that are not blocked / of all unfinished
   * threads. Thread identifiers are below 64 in native mode. */
  std::uint64_t runnableMask() const;
  std::uint64_t unfinishedMask() const;
  bool mutexOwner(std::uint64_t object, std::uint64_t offset,
                  std::uint64_t &owner) const;
  bool mutexHasWaiters(std::uint64_t object, std::uint64_t offset) const;
  bool blockOnJoin(std::uint64_t thread, std::uint64_t target,
                   std::string &error);
  bool blockOnCondition(std::uint64_t thread, std::uint64_t condObject,
                        std::uint64_t condOffset, std::uint64_t mutexObject,
                        std::uint64_t mutexOffset, std::string &error);
  /* Threads blocked for the given reason: Mutex waiters on a mutex, Cond
   * waiters on a condition variable, or Join waiters on a target thread
   * (object = target, offset ignored). */
  void collectBlocked(ConcurrencyBlockKind kind, std::uint64_t object,
                      std::uint64_t offset,
                      std::vector<std::uint64_t> &threads) const;
  /* Wake one condition waiter and remove it from the blocked set. Native
   * pthread conditions may merge the signaller's clock into the waiter;
   * std::condition_variable trace notifications do not create that memory
   * edge, and instead rely on release/acquire of the associated mutex. The
   * mutex the waiter has to reacquire is returned. */
  bool wakeConditionWaiter(std::uint64_t waiter, std::uint64_t &mutexObject,
                           std::uint64_t &mutexOffset,
                           bool mergeNotifierClock, std::string &error);
  bool scheduleCandidates(std::uint64_t runnableMask,
                          std::uint64_t maxSwitches,
                          std::vector<std::uint64_t> &candidates,
                          std::string &error);
  bool scheduleThread(std::uint64_t thread, std::uint64_t runnableMask,
                      std::uint64_t maxSwitches, std::string &error);
  ConcurrencyAccessResult recordAccess(std::uint64_t object,
                                       std::uint64_t offset,
                                       std::uint64_t address,
                                       std::uint64_t size, bool write,
                                       std::uint64_t site,
                                       ConcurrencyRace &race,
                                       std::string &error);
};

} // namespace klee

#endif // KLEE_CONCURRENCY_H
