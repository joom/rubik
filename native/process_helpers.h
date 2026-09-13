#pragma once

// Thin wrappers over the two host services the extracted entry point needs
// and raylib does not provide, one per effect declared in ProcDefs.v.
// Nothing here knows about any particular application.

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <optional>
#include <string>

// The value of an environment variable, or nothing when it is unset.
inline std::optional<std::string> rl_getenv(const std::string &name) {
  const char *value = std::getenv(name.c_str());
  if (value == nullptr) return std::nullopt;
  return std::string(value);
}

// Stop at once, without unwinding. A search deep enough to outlive the window
// is abandoned rather than waited for, so the process must leave without
// running destructors that might still be racing it.
[[noreturn]] inline void rl_exit_now(std::uint64_t code) {
  std::fflush(nullptr);
  std::_Exit(static_cast<int>(code));
}
