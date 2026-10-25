//===-- Concurrency.cpp ---------------------------------------------------===//

#include "Concurrency.h"

#include <algorithm>
#include <limits>
#include <utility>

using namespace klee;

ConcurrencyState::ConcurrencyState() {
  ThreadState mainThread;
  mainThread.clock[0] = 1;
  threads.emplace(0, std::move(mainThread));
}

ConcurrencyState::ThreadState *
ConcurrencyState::getActiveThread(std::string &error) {
  auto it = threads.find(activeThread);
  if (it == threads.end()) {
    error = "active logical thread does not exist";
    return nullptr;
  }
  if (it->second.finished) {
    error = "active logical thread has already finished";
    return nullptr;
  }
  if (blockedThreads.count(activeThread)) {
    error = "active logical thread is blocked";
    return nullptr;
  }
  return &it->second;
}

void ConcurrencyState::tick(std::uint64_t thread, VectorClock &clock) {
  ++clock[thread];
}

void ConcurrencyState::merge(VectorClock &destination,
                             const VectorClock &source) {
  for (const auto &entry : source)
    destination[entry.first] =
        std::max(destination[entry.first], entry.second);
}

bool ConcurrencyState::happensBefore(const VectorClock &before,
                                     const VectorClock &after) {
  for (const auto &entry : before) {
    auto it = after.find(entry.first);
    const std::uint64_t value = it == after.end() ? 0 : it->second;
    if (entry.second > value)
      return false;
  }
  return true;
}

bool ConcurrencyState::completeActiveTransition(std::string &error) {
  /* A declaration describes exactly one transition. Once that transition has
   * completed it is consumed, so scheduling the thread again requires a
   * fresh declaration; a stale LOCAL kind must not make a later step free. */
  for (auto it = declarations.begin(); it != declarations.end();) {
    TransitionDeclaration &declaration = it->second;
    if (!declaration.active) {
      ++it;
      continue;
    }
    if ((declaration.kind == ConcurrencyTransitionKind::Read ||
         declaration.kind == ConcurrencyTransitionKind::Write ||
         declaration.kind == ConcurrencyTransitionKind::Mutex) &&
        !declaration.observed) {
      error = "declared logical transition did not execute its expected operation";
      return false;
    }
    if (declaration.kind == ConcurrencyTransitionKind::Local)
      completedLocalGuardsEnabledness = true;
    it = declarations.erase(it);
  }
  return true;
}

bool ConcurrencyState::validateDeclaredAccess(std::uint64_t object,
                                              std::uint64_t offset,
                                              std::uint64_t size, bool write,
                                              std::string &error) {
  if (!declarationsEnabled || !scheduleStarted)
    return true;
  auto it = declarations.find(activeThread);
  if (it == declarations.end() || !it->second.active) {
    error = "logical memory access has no active transition declaration";
    return false;
  }

  TransitionDeclaration &declaration = it->second;
  if (declaration.kind == ConcurrencyTransitionKind::Opaque)
    return true;
  if (declaration.kind == ConcurrencyTransitionKind::Local) {
    error = "LOCAL transition executed a shared memory access";
    return false;
  }
  if (declaration.kind == ConcurrencyTransitionKind::Mutex) {
    error = "MUTEX transition executed a shared memory access";
    return false;
  }
  if (declaration.kind == ConcurrencyTransitionKind::Read && write) {
    error = "READ transition executed a write";
    return false;
  }
  const std::uint64_t end = offset + size;
  if (object != declaration.object || offset < declaration.begin ||
      end > declaration.end) {
    error = "logical memory access exceeds its declared transition range";
    return false;
  }
  declaration.observed = true;
  return true;
}

bool ConcurrencyState::validateDeclaredMutex(std::uint64_t object,
                                             std::uint64_t offset,
                                             std::string &error) {
  if (!declarationsEnabled || !scheduleStarted)
    return true;
  auto it = declarations.find(activeThread);
  if (it == declarations.end() || !it->second.active) {
    error = "logical mutex operation has no active transition declaration";
    return false;
  }

  TransitionDeclaration &declaration = it->second;
  if (declaration.kind == ConcurrencyTransitionKind::Opaque)
    return true;
  if (declaration.kind != ConcurrencyTransitionKind::Mutex) {
    error = declaration.kind == ConcurrencyTransitionKind::Local
                ? "LOCAL transition executed a mutex operation"
                : "memory transition executed a mutex operation";
    return false;
  }
  if (declaration.object != object || declaration.begin != offset) {
    error = "logical mutex operation does not match its declaration";
    return false;
  }
  if (declaration.observed) {
    error = "MUTEX transition executed more than one mutex operation";
    return false;
  }
  declaration.observed = true;
  return true;
}

bool ConcurrencyState::validateDeclaredOpaqueOperation(
    const char *operation, std::string &error) {
  if (!declarationsEnabled || !scheduleStarted)
    return true;
  auto it = declarations.find(activeThread);
  if (it == declarations.end() || !it->second.active) {
    error = std::string(operation) +
            " has no active transition declaration";
    return false;
  }
  if (it->second.kind != ConcurrencyTransitionKind::Opaque) {
    error = std::string(operation) + " requires an OPAQUE transition";
    return false;
  }
  return true;
}

bool ConcurrencyState::declareTransition(std::uint64_t thread,
                                         std::uint32_t kindValue,
                                         std::uint64_t object,
                                         std::uint64_t offset,
                                         std::uint64_t size,
                                         std::string &error) {
  auto threadIt = threads.find(thread);
  if (threadIt == threads.end() || threadIt->second.finished) {
    error = "transition declaration names an unknown or finished logical thread";
    return false;
  }
  if (kindValue >
      static_cast<std::uint32_t>(ConcurrencyTransitionKind::Mutex)) {
    error = "transition declaration has an invalid kind";
    return false;
  }
  const auto kind = static_cast<ConcurrencyTransitionKind>(kindValue);
  const bool memory = kind == ConcurrencyTransitionKind::Read ||
                      kind == ConcurrencyTransitionKind::Write;
  if (memory &&
      (size == 0 ||
       offset > std::numeric_limits<std::uint64_t>::max() - size)) {
    error = "memory transition declaration has an invalid range";
    return false;
  }
  if (!memory && size != 0) {
    error = "non-memory transition declaration has a nonzero size";
    return false;
  }
  if ((kind == ConcurrencyTransitionKind::Local ||
       kind == ConcurrencyTransitionKind::Opaque) &&
      offset != 0) {
    error = "LOCAL or OPAQUE transition declaration has an address";
    return false;
  }

  auto existing = declarations.find(thread);
  if (existing != declarations.end() && existing->second.active &&
      !completeActiveTransition(error))
    return false;

  TransitionDeclaration declaration;
  declaration.kind = kind;
  declaration.object = object;
  declaration.begin = offset;
  declaration.end = memory ? offset + size : offset;
  declarations[thread] = declaration;
  declarationsEnabled = true;
  return true;
}

bool ConcurrencyState::createThread(std::uint64_t thread,
                                    std::string &error) {
  if (!validateDeclaredOpaqueOperation("logical thread creation", error))
    return false;
  ThreadState *parent = getActiveThread(error);
  if (!parent)
    return false;
  if (threads.count(thread)) {
    error = "logical thread identifier already exists";
    return false;
  }

  tick(activeThread, parent->clock);
  ThreadState child;
  child.clock = parent->clock;
  child.clock[thread] = 1;
  threads.emplace(thread, std::move(child));
  return true;
}

bool ConcurrencyState::resetScheduler(std::string &error) {
  if (!completeActiveTransition(error))
    return false;
  std::uint64_t unfinished = 0;
  std::uint64_t remaining = 0;
  for (const auto &entry : threads) {
    if (entry.second.finished)
      continue;
    ++unfinished;
    remaining = entry.first;
  }
  if (unfinished == 0) {
    error = "logical thread scheduler reset with no unfinished logical "
            "thread to coordinate the next episode";
    return false;
  }
  /* Before the first decision there is no accounting to discard, and a
   * harness may already have created the threads it is about to schedule. */
  if (!scheduleStarted) {
    declarations.clear();
    declarationsEnabled = false;
    return true;
  }
  if (unfinished > 1) {
    error = "logical thread scheduler reset while more than one logical "
            "thread is unfinished";
    return false;
  }
  if (blockedThreads.count(remaining)) {
    error = "logical thread scheduler reset while the remaining logical "
            "thread is blocked";
    return false;
  }
  /* The harness continues only after every other thread finished, so the
   * next episode is ordered after them, as if the remaining thread had
   * joined each one. */
  ThreadState &survivor = threads[remaining];
  for (const auto &entry : threads) {
    if (entry.second.finished)
      merge(survivor.clock, entry.second.clock);
  }
  tick(remaining, survivor.clock);
  activeThread = remaining;
  declarations.clear();
  declarationsEnabled = false;
  completedLocalGuardsEnabledness = false;
  scheduleStarted = false;
  scheduleMaxSwitches = 0;
  anchorValid = false;
  anchorThread = 0;
  contextSwitches = 0;
  return true;
}

bool ConcurrencyState::setThread(std::uint64_t thread, std::string &error) {
  auto it = threads.find(thread);
  if (it == threads.end()) {
    error = "selected logical thread does not exist";
    return false;
  }
  if (it->second.finished) {
    error = "selected logical thread has already finished";
    return false;
  }
  if (blockedThreads.count(thread)) {
    error = "selected logical thread is blocked";
    return false;
  }
  /* Once the scheduler has made a decision, only it may change the running
   * thread; a direct selection would bypass the bound, the choice bytes, and
   * the declaration checks. Re-selecting the active thread is a no-op. */
  if (scheduleStarted && thread != activeThread) {
    error = "direct logical thread selection after scheduling began";
    return false;
  }
  activeThread = thread;
  return true;
}

bool ConcurrencyState::localTransitionGuardsEnabledness() const {
  if (completedLocalGuardsEnabledness)
    return true;
  if (!declarationsEnabled || !scheduleStarted)
    return false;
  auto it = declarations.find(activeThread);
  return it != declarations.end() && it->second.active &&
         it->second.kind == ConcurrencyTransitionKind::Local;
}

bool ConcurrencyState::completePendingTransition(std::string &error) {
  return completeActiveTransition(error);
}

bool ConcurrencyState::blockThread(std::uint64_t thread, std::uint32_t kind,
                                   std::uint64_t object, std::uint64_t offset,
                                   std::string &error) {
  auto it = threads.find(thread);
  if (it == threads.end() || it->second.finished) {
    error = "blocked logical thread is unknown or finished";
    return false;
  }
  /* A LOCAL transition commutes with every other transition only if it
   * cannot change another thread's enabledness. Blocking itself only disables
   * its own next step and remains permitted. */
  if (thread != activeThread && localTransitionGuardsEnabledness()) {
    error = "LOCAL transition blocked another logical thread";
    return false;
  }
  if (blockedThreads.count(thread)) {
    error = "logical thread is already blocked";
    return false;
  }
  if (kind > static_cast<std::uint32_t>(ConcurrencyBlockKind::Mutex)) {
    error = "block reason has an invalid kind";
    return false;
  }
  BlockReason reason;
  reason.kind = static_cast<ConcurrencyBlockKind>(kind);
  if (reason.kind == ConcurrencyBlockKind::Mutex) {
    reason.mutex = MemoryLocation{object, offset};
    auto owner = mutexOwners.find(reason.mutex);
    if (owner == mutexOwners.end()) {
      error = "logical thread blocked on an unowned mutex";
      return false;
    }
    if (owner->second == thread) {
      error = "logical thread blocked on a mutex it owns";
      return false;
    }
  }
  blockedThreads[thread] = reason;
  return true;
}

bool ConcurrencyState::unblockThread(std::uint64_t thread,
                                     std::string &error) {
  auto it = blockedThreads.find(thread);
  if (it == blockedThreads.end()) {
    error = "unblocked logical thread was not blocked";
    return false;
  }
  if (localTransitionGuardsEnabledness()) {
    error = "LOCAL transition unblocked a logical thread";
    return false;
  }
  if (it->second.kind == ConcurrencyBlockKind::Mutex) {
    auto owner = mutexOwners.find(it->second.mutex);
    if (owner != mutexOwners.end() && owner->second != thread) {
      error = "logical thread unblocked while its mutex is still owned by "
              "another thread";
      return false;
    }
  }
  if (it->second.kind == ConcurrencyBlockKind::Join) {
    auto target = threads.find(it->second.target);
    if (target == threads.end() || !target->second.finished) {
      error = "logical thread unblocked while its join target is unfinished";
      return false;
    }
  }
  if (it->second.kind == ConcurrencyBlockKind::Cond) {
    error = "condition waiter unblocked without a signal";
    return false;
  }
  blockedThreads.erase(it);
  return true;
}

bool ConcurrencyState::enterHarnessMode(const char *operation,
                                        std::string &error) {
  if (nativeMode) {
    error = std::string(operation) +
            " is a harness-driver intrinsic and cannot be used once the "
            "state runs native threads";
    return false;
  }
  harnessMode = true;
  return true;
}

bool ConcurrencyState::enterNativeMode(const char *operation,
                                       std::string &error) {
  if (harnessMode) {
    error = std::string(operation) +
            " is a native thread operation and cannot be used once the "
            "state is driven by harness scheduling intrinsics";
    return false;
  }
  if (!nativeMode) {
    /* The main thread is already running when the model is entered, so a
     * first decision that switches away from it while it stays runnable is
     * a preemption and must be charged. */
    nativeMode = true;
    anchorValid = true;
    anchorThread = activeThread;
  }
  return true;
}

bool ConcurrencyState::allocateNativeThread(std::uint64_t &thread,
                                            std::string &error) {
  if (nextNativeThread >= 64) {
    error = "native thread limit reached: at most 63 pthread_create calls "
            "per path (logical thread ids are not recycled)";
    return false;
  }
  thread = nextNativeThread++;
  return true;
}

void ConcurrencyState::markYielded(std::uint64_t thread) {
  if (thread < 64)
    yieldedMask |= std::uint64_t{1} << thread;
}

bool ConcurrencyState::threadExists(std::uint64_t thread) const {
  return threads.count(thread) != 0;
}

bool ConcurrencyState::threadFinished(std::uint64_t thread) const {
  auto it = threads.find(thread);
  return it != threads.end() && it->second.finished;
}

bool ConcurrencyState::threadBlocked(std::uint64_t thread) const {
  return blockedThreads.count(thread) != 0;
}

bool ConcurrencyState::threadJoined(std::uint64_t thread) const {
  auto it = threads.find(thread);
  return it != threads.end() && it->second.joined;
}

std::uint64_t ConcurrencyState::unfinishedMask() const {
  std::uint64_t mask = 0;
  for (const auto &entry : threads)
    if (!entry.second.finished && entry.first < 64)
      mask |= std::uint64_t{1} << entry.first;
  return mask;
}

std::uint64_t ConcurrencyState::runnableMask() const {
  std::uint64_t mask = unfinishedMask();
  for (const auto &entry : blockedThreads)
    if (entry.first < 64)
      mask &= ~(std::uint64_t{1} << entry.first);
  return mask;
}

bool ConcurrencyState::mutexOwner(std::uint64_t object, std::uint64_t offset,
                                  std::uint64_t &owner) const {
  auto it = mutexOwners.find(MemoryLocation{object, offset});
  if (it == mutexOwners.end())
    return false;
  owner = it->second;
  return true;
}

bool ConcurrencyState::mutexHasWaiters(std::uint64_t object,
                                       std::uint64_t offset) const {
  const MemoryLocation mutex{object, offset};
  for (const auto &entry : blockedThreads) {
    const BlockReason &reason = entry.second;
    if ((reason.kind == ConcurrencyBlockKind::Mutex ||
         reason.kind == ConcurrencyBlockKind::Cond) &&
        reason.mutex.object == mutex.object &&
        reason.mutex.offset == mutex.offset)
      return true;
  }
  return false;
}

bool ConcurrencyState::blockOnJoin(std::uint64_t thread, std::uint64_t target,
                                   std::string &error) {
  auto it = threads.find(thread);
  if (it == threads.end() || it->second.finished) {
    error = "blocked logical thread is unknown or finished";
    return false;
  }
  if (blockedThreads.count(thread)) {
    error = "logical thread is already blocked";
    return false;
  }
  auto targetIt = threads.find(target);
  if (targetIt == threads.end() || targetIt->second.finished) {
    error = "join target is unknown or already finished";
    return false;
  }
  BlockReason reason;
  reason.kind = ConcurrencyBlockKind::Join;
  reason.target = target;
  blockedThreads[thread] = reason;
  return true;
}

bool ConcurrencyState::blockOnCondition(std::uint64_t thread,
                                        std::uint64_t condObject,
                                        std::uint64_t condOffset,
                                        std::uint64_t mutexObject,
                                        std::uint64_t mutexOffset,
                                        std::string &error) {
  auto it = threads.find(thread);
  if (it == threads.end() || it->second.finished) {
    error = "blocked logical thread is unknown or finished";
    return false;
  }
  if (blockedThreads.count(thread)) {
    error = "logical thread is already blocked";
    return false;
  }
  BlockReason reason;
  reason.kind = ConcurrencyBlockKind::Cond;
  reason.condition = MemoryLocation{condObject, condOffset};
  reason.mutex = MemoryLocation{mutexObject, mutexOffset};
  blockedThreads[thread] = reason;
  return true;
}

void ConcurrencyState::collectBlocked(
    ConcurrencyBlockKind kind, std::uint64_t object, std::uint64_t offset,
    std::vector<std::uint64_t> &result) const {
  result.clear();
  for (const auto &entry : blockedThreads) {
    const BlockReason &reason = entry.second;
    if (reason.kind != kind)
      continue;
    bool match = false;
    switch (kind) {
    case ConcurrencyBlockKind::Mutex:
      match = reason.mutex.object == object && reason.mutex.offset == offset;
      break;
    case ConcurrencyBlockKind::Cond:
      match = reason.condition.object == object &&
              reason.condition.offset == offset;
      break;
    case ConcurrencyBlockKind::Join:
      match = reason.target == object;
      break;
    case ConcurrencyBlockKind::Harness:
      match = true;
      break;
    }
    if (match)
      result.push_back(entry.first);
  }
}

bool ConcurrencyState::wakeConditionWaiter(std::uint64_t waiter,
                                           std::uint64_t &mutexObject,
                                           std::uint64_t &mutexOffset,
                                           bool mergeNotifierClock,
                                           std::string &error) {
  auto it = blockedThreads.find(waiter);
  if (it == blockedThreads.end() ||
      it->second.kind != ConcurrencyBlockKind::Cond) {
    error = "woken logical thread is not a condition waiter";
    return false;
  }
  ThreadState *signaller = getActiveThread(error);
  if (!signaller)
    return false;
  auto waiterIt = threads.find(waiter);
  if (waiterIt == threads.end() || waiterIt->second.finished) {
    error = "condition waiter is unknown or finished";
    return false;
  }
  tick(activeThread, signaller->clock);
  if (mergeNotifierClock)
    merge(waiterIt->second.clock, signaller->clock);
  mutexObject = it->second.mutex.object;
  mutexOffset = it->second.mutex.offset;
  blockedThreads.erase(it);
  return true;
}

bool ConcurrencyState::finishThread(std::string &error) {
  if (blockedThreads.count(activeThread)) {
    error = "blocked logical thread cannot finish";
    return false;
  }
  if (!completeActiveTransition(error))
    return false;
  ThreadState *current = getActiveThread(error);
  if (!current)
    return false;
  for (const auto &owner : mutexOwners) {
    if (owner.second == activeThread) {
      error = "logical thread finished while holding a mutex";
      return false;
    }
  }
  tick(activeThread, current->clock);
  current->finished = true;
  declarations.erase(activeThread);
  return true;
}

bool ConcurrencyState::joinThread(std::uint64_t thread, std::string &error) {
  if (!validateDeclaredOpaqueOperation("logical thread join", error))
    return false;
  ThreadState *current = getActiveThread(error);
  if (!current)
    return false;
  if (thread == activeThread) {
    error = "logical thread cannot join itself";
    return false;
  }
  auto it = threads.find(thread);
  if (it == threads.end()) {
    error = "joined logical thread does not exist";
    return false;
  }
  if (!it->second.finished) {
    error = "joined logical thread has not finished";
    return false;
  }
  if (it->second.joined) {
    error = "logical thread was already joined";
    return false;
  }

  merge(current->clock, it->second.clock);
  tick(activeThread, current->clock);
  it->second.joined = true;
  return true;
}

bool ConcurrencyState::initializeMutex(std::uint64_t object,
                                       std::uint64_t offset,
                                       std::string &error) {
  const MemoryLocation mutex{object, offset};
  if (mutexOwners.count(mutex)) {
    error = "pthread_mutex_init on a locked mutex";
    return false;
  }
  if (initializedMutexes.count(mutex)) {
    error = "pthread_mutex_init on an initialized mutex";
    return false;
  }

  /* A successful init starts a new synchronization generation. In
   * particular, it must not acquire the release clock of a destroyed mutex
   * that occupied the same bytes in the same live allocation. */
  mutexReleaseClocks.erase(mutex);
  destroyedMutexes.erase(mutex);
  initializedMutexes.insert(mutex);
  return true;
}

bool ConcurrencyState::destroyMutex(std::uint64_t object,
                                    std::uint64_t offset,
                                    std::string &error) {
  const MemoryLocation mutex{object, offset};
  if (mutexOwners.count(mutex)) {
    error = "pthread_mutex_destroy on a locked mutex";
    return false;
  }
  if (destroyedMutexes.count(mutex)) {
    error = "pthread_mutex_destroy on a destroyed mutex";
    return false;
  }

  /* An unknown location may be a PTHREAD_MUTEX_INITIALIZER, so its first
   * lifecycle operation is allowed to be destroy. */
  initializedMutexes.erase(mutex);
  destroyedMutexes.insert(mutex);
  mutexReleaseClocks.erase(mutex);
  return true;
}

bool ConcurrencyState::mutexLock(std::uint64_t object, std::uint64_t offset,
                                 std::string &error) {
  if (!validateDeclaredMutex(object, offset, error))
    return false;
  ThreadState *current = getActiveThread(error);
  if (!current)
    return false;
  const MemoryLocation mutex{object, offset};
  if (destroyedMutexes.count(mutex)) {
    error = "logical mutex lock after pthread_mutex_destroy";
    return false;
  }
  /* Direct concurrency intrinsics and PTHREAD_MUTEX_INITIALIZER do not have
   * an explicit init call; their first valid operation establishes the
   * initial generation lazily. */
  initializedMutexes.insert(mutex);
  auto owner = mutexOwners.find(mutex);
  if (owner != mutexOwners.end()) {
    error = owner->second == activeThread
                ? "recursive logical mutex lock is unsupported"
                : "logical mutex is owned by another runnable thread";
    return false;
  }

  auto released = mutexReleaseClocks.find(mutex);
  if (released != mutexReleaseClocks.end())
    merge(current->clock, released->second);
  tick(activeThread, current->clock);
  mutexOwners[mutex] = activeThread;
  return true;
}

bool ConcurrencyState::mutexUnlock(std::uint64_t object, std::uint64_t offset,
                                   std::string &error) {
  if (!validateDeclaredMutex(object, offset, error))
    return false;
  ThreadState *current = getActiveThread(error);
  if (!current)
    return false;
  const MemoryLocation mutex{object, offset};
  if (destroyedMutexes.count(mutex)) {
    error = "logical mutex unlock after pthread_mutex_destroy";
    return false;
  }
  initializedMutexes.insert(mutex);
  auto owner = mutexOwners.find(mutex);
  if (owner == mutexOwners.end() || owner->second != activeThread) {
    error = "logical mutex unlock by a non-owner";
    return false;
  }

  tick(activeThread, current->clock);
  mutexReleaseClocks[mutex] = current->clock;
  mutexOwners.erase(owner);
  return true;
}

bool ConcurrencyState::validateDeadlock(std::uint64_t blockedMask,
                                        bool &verified,
                                        std::string &error) const {
  verified = true;
  if (blockedMask == 0) {
    error = "deadlock mask is empty";
    return false;
  }

  for (std::uint64_t thread = 0; thread < 64; ++thread) {
    const bool reported =
        (blockedMask & (std::uint64_t{1} << thread)) != 0;
    auto it = threads.find(thread);
    if (reported && (it == threads.end() || it->second.finished)) {
      error = "deadlock mask contains an unknown or finished logical thread";
      return false;
    }
    if (it != threads.end() && !it->second.finished && !reported) {
      error = "deadlock mask omits an unfinished logical thread";
      return false;
    }
  }
  for (const auto &entry : threads) {
    if (entry.first >= 64 && !entry.second.finished) {
      error = "unfinished logical thread does not fit the deadlock mask";
      return false;
    }
  }

  /* The mask shape is right; now every reported thread needs an engine
   * recorded reason, and mutex reasons must still hold. */
  for (std::uint64_t thread = 0; thread < 64; ++thread) {
    if ((blockedMask & (std::uint64_t{1} << thread)) == 0)
      continue;
    auto reason = blockedThreads.find(thread);
    if (reason == blockedThreads.end()) {
      error = "deadlock mask contains a logical thread the engine does not "
              "record as blocked";
      return false;
    }
    if (reason->second.kind == ConcurrencyBlockKind::Harness) {
      verified = false;
      continue;
    }
    if (reason->second.kind == ConcurrencyBlockKind::Join) {
      /* Verified when the awaited thread is itself in the blocked set; the
       * mask shape already guarantees every unfinished thread is listed. */
      const std::uint64_t target = reason->second.target;
      if (target >= 64 || (blockedMask & (std::uint64_t{1} << target)) == 0) {
        error = "deadlocked logical thread joins a thread outside the "
                "blocked mask";
        return false;
      }
      continue;
    }
    if (reason->second.kind == ConcurrencyBlockKind::Cond) {
      /* Every unfinished thread is blocked, so no thread can ever signal;
       * the wait can only return through a spurious wakeup. */
      continue;
    }
    auto owner = mutexOwners.find(reason->second.mutex);
    if (owner == mutexOwners.end()) {
      error = "deadlocked logical thread waits on a mutex that is no longer "
              "owned";
      return false;
    }
    if (owner->second == thread) {
      error = "deadlocked logical thread waits on a mutex it owns";
      return false;
    }
    if (owner->second >= 64 ||
        (blockedMask & (std::uint64_t{1} << owner->second)) == 0) {
      error = "deadlocked logical thread waits on a mutex held by a thread "
              "outside the blocked mask";
      return false;
    }
  }
  return true;
}

bool ConcurrencyState::isLocalTransition(std::uint64_t thread) const {
  if (!declarationsEnabled)
    return false;
  auto it = declarations.find(thread);
  return it != declarations.end() &&
         it->second.kind == ConcurrencyTransitionKind::Local;
}

bool ConcurrencyState::anchorPreemptible(std::uint64_t runnableMask) const {
  return anchorValid && anchorThread < 64 &&
         (runnableMask & (std::uint64_t{1} << anchorThread)) != 0;
}

bool ConcurrencyState::scheduleCandidates(
    std::uint64_t runnableMask, std::uint64_t maxSwitches,
    std::vector<std::uint64_t> &candidates, std::string &error) {
  candidates.clear();
  if (!completeActiveTransition(error))
    return false;
  if (runnableMask == 0) {
    error = "runnable mask is empty";
    return false;
  }
  if (scheduleStarted && maxSwitches != scheduleMaxSwitches) {
    error = "scheduler switch bound changed during execution";
    return false;
  }
  const bool preemptible = anchorPreemptible(runnableMask);

  for (std::uint64_t thread = 0; thread < 64; ++thread) {
    if ((runnableMask & (std::uint64_t{1} << thread)) == 0)
      continue;
    auto it = threads.find(thread);
    if (it == threads.end()) {
      error = "runnable mask contains an unknown logical thread";
      return false;
    }
    if (it->second.finished) {
      error = "runnable mask contains a finished logical thread";
      return false;
    }
    if (blockedThreads.count(thread)) {
      error = "runnable mask contains a blocked logical thread";
      return false;
    }
    if (!preemptible || thread == anchorThread ||
        contextSwitches < maxSwitches || isLocalTransition(thread))
      candidates.push_back(thread);
  }
  return true;
}

bool ConcurrencyState::scheduleThread(std::uint64_t thread,
                                      std::uint64_t runnableMask,
                                      std::uint64_t maxSwitches,
                                      std::string &error) {
  auto it = threads.find(thread);
  if (it == threads.end() || it->second.finished) {
    error = "scheduler selected a non-runnable logical thread";
    return false;
  }
  if (thread >= 64 || (runnableMask & (std::uint64_t{1} << thread)) == 0) {
    error = "scheduler selected a thread outside the runnable mask";
    return false;
  }
  if (scheduleStarted && maxSwitches != scheduleMaxSwitches) {
    error = "scheduler switch bound changed during execution";
    return false;
  }
  if (declarationsEnabled) {
    auto declaration = declarations.find(thread);
    if (declaration == declarations.end()) {
      error = "scheduler selected a thread without a transition declaration";
      return false;
    }
    declaration->second.active = true;
    declaration->second.observed = false;
  }
  const bool local = isLocalTransition(thread);
  if (!local) {
    if (anchorPreemptible(runnableMask) && thread != anchorThread) {
      if (contextSwitches >= maxSwitches) {
        error = "scheduler exceeded its preemption bound";
        return false;
      }
      ++contextSwitches;
    }
    anchorValid = true;
    anchorThread = thread;
  }
  scheduleStarted = true;
  scheduleMaxSwitches = maxSwitches;
  activeThread = thread;
  completedLocalGuardsEnabledness = false;
  yieldedMask &= ~(std::uint64_t{1} << thread);
  return true;
}

ConcurrencyAccessResult ConcurrencyState::recordAccess(
    std::uint64_t object, std::uint64_t offset, std::uint64_t address,
    std::uint64_t size, bool write, std::uint64_t site, ConcurrencyRace &race,
    std::string &error) {
  ThreadState *current = getActiveThread(error);
  if (!current)
    return ConcurrencyAccessResult::Error;
  if (size == 0) {
    error = "logical memory access has zero size";
    return ConcurrencyAccessResult::Error;
  }
  if (address > std::numeric_limits<std::uint64_t>::max() - size) {
    error = "logical memory access range overflows";
    return ConcurrencyAccessResult::Error;
  }
  if (offset > std::numeric_limits<std::uint64_t>::max() - size) {
    error = "logical memory access object-relative range overflows";
    return ConcurrencyAccessResult::Error;
  }
  if (!validateDeclaredAccess(object, offset, size, write, error))
    return ConcurrencyAccessResult::Error;

  tick(activeThread, current->clock);
  const std::uint64_t end = offset + size;
  for (const Access &previous : accesses) {
    const bool overlaps = previous.begin < end && offset < previous.end;
    if (previous.thread == activeThread || previous.object != object ||
        !overlaps ||
        (!previous.write && !write))
      continue;
    if (happensBefore(previous.clock, current->clock))
      continue;

    race.currentThread = activeThread;
    race.currentSite = site;
    race.currentWrite = write;
    race.previousThread = previous.thread;
    race.previousSite = previous.site;
    race.previousWrite = previous.write;
    const std::uint64_t overlap = std::max(offset, previous.begin);
    race.address = address + (overlap - offset);
    race.size = std::min(end, previous.end) - overlap;
    return ConcurrencyAccessResult::Race;
  }

  accesses.push_back(
      Access{activeThread, site, object, offset, end, write, current->clock});
  return ConcurrencyAccessResult::Ok;
}
