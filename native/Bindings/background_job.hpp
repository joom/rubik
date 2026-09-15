#pragma once

// One cancellable background computation, polled rather than waited for.
//
// A job owns a cell shared with a detached worker thread. Polling reads the
// finished value at most once and never blocks; cancelling marks the cell
// unwanted, so a computation that is still running writes nowhere anyone
// looks. Nothing here knows what is being computed.
//
// Under emscripten there is no thread to detach onto: worker threads need
// SharedArrayBuffer, which needs cross-origin isolation headers that static
// hosting does not send. The work runs on the calling thread instead, so a
// browser tab stops painting until it finishes. Everything else, including
// the poll-once and cancel semantics, is unchanged.

#include <exception>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

#ifndef __EMSCRIPTEN__
#include <mutex>
#include <thread>
#endif

namespace crane {

// The rendezvous between a job handle and the thread computing its value.
#ifdef __EMSCRIPTEN__
// A lock is pointless where there is only ever one thread.
struct no_mutex {};
struct no_lock {
  explicit no_lock(no_mutex &) {}
};
#endif

template <class B> struct job_cell {
#ifdef __EMSCRIPTEN__
  no_mutex mutex;
#else
  std::mutex mutex;
#endif
  std::optional<B> value;
  std::exception_ptr error;
  bool wanted = true;
};

#ifdef __EMSCRIPTEN__
#define CRANE_JOB_LOCK(m) no_lock lock(m)
#else
#define CRANE_JOB_LOCK(m) std::lock_guard lock(m)
#endif

template <class B> class job {
public:
  job() = default;
  explicit job(std::shared_ptr<job_cell<B>> cell) : cell_(std::move(cell)) {}

  // The finished value, once, or nothing while the work is still running.
  std::optional<B> poll() const {
    if (!cell_) return std::nullopt;
    CRANE_JOB_LOCK(cell_->mutex);
    if (!cell_->wanted) return std::nullopt;
    if (cell_->error) {
      std::rethrow_exception(std::exchange(cell_->error, nullptr));
    }
    return std::exchange(cell_->value, std::nullopt);
  }

  // Abandon the work. It may still be running, but nothing will read it, and
  // the cell outlives this handle for as long as the worker holds it.
  void cancel() const {
    if (!cell_) return;
    CRANE_JOB_LOCK(cell_->mutex);
    cell_->wanted = false;
    cell_->value.reset();
    cell_->error = nullptr;
  }

private:
  std::shared_ptr<job_cell<B>> cell_;
};

// Run f on arg off the calling thread and return a handle immediately.
template <class F, class A> auto job_start(F f, A arg) {
  using B = std::invoke_result_t<F &, A>;
  auto cell = std::make_shared<job_cell<B>>();
  auto work = [cell, f = std::move(f), arg = std::move(arg)]() mutable {
    try {
      auto value = f(std::move(arg));
      CRANE_JOB_LOCK(cell->mutex);
      if (cell->wanted) cell->value.emplace(std::move(value));
    } catch (...) {
      CRANE_JOB_LOCK(cell->mutex);
      if (cell->wanted) cell->error = std::current_exception();
    }
  };
#ifdef __EMSCRIPTEN__
  work();
#else
  std::thread(std::move(work)).detach();
#endif
  return job<B>(std::move(cell));
}

} // namespace crane
