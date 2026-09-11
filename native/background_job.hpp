#pragma once

// One cancellable background computation, polled rather than waited for.
//
// A job owns a cell shared with a detached worker thread. Polling reads the
// finished value at most once and never blocks; cancelling marks the cell
// unwanted, so a computation that is still running writes nowhere anyone
// looks. Nothing here knows what is being computed.

#include <condition_variable>
#include <exception>
#include <memory>
#include <mutex>
#include <optional>
#include <thread>
#include <type_traits>
#include <utility>

namespace crane {

// The rendezvous between a job handle and the thread computing its value.
template <class B> struct job_cell {
  std::mutex mutex;
  std::optional<B> value;
  std::exception_ptr error;
  bool wanted = true;
};

template <class B> class job {
public:
  job() = default;
  explicit job(std::shared_ptr<job_cell<B>> cell) : cell_(std::move(cell)) {}

  // The finished value, once, or nothing while the work is still running.
  std::optional<B> poll() const {
    if (!cell_) return std::nullopt;
    std::lock_guard lock(cell_->mutex);
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
    std::lock_guard lock(cell_->mutex);
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
  std::thread([cell, f = std::move(f), arg = std::move(arg)]() mutable {
    try {
      auto value = f(std::move(arg));
      std::lock_guard lock(cell->mutex);
      if (cell->wanted) cell->value.emplace(std::move(value));
    } catch (...) {
      std::lock_guard lock(cell->mutex);
      if (cell->wanted) cell->error = std::current_exception();
    }
  }).detach();
  return job<B>(std::move(cell));
}

} // namespace crane
